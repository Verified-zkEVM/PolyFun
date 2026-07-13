/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

-- `Notation` defines the generic single-index `FreeM` overrides; importing
-- it transitively here forces our deterministic-`FreeM` override to be
-- registered *after*, so the keyed-attribute lookup tries it first. Without
-- this, downstream `import` order would silently determine which override
-- fires for `FreeM`-shaped `do`-blocks. See `Notation/Mixed.lean` for the
-- regression test.
public import PolyFun.IPFunctor.Notation
public import Lean.Elab.Do
meta import Lean.Parser.Do

/-!
# `do`-notation for `IPFunctor.FreeM` with deterministic transitions

The single-index `do`-notation in
[`PolyFun/IPFunctor/Notation.lean`](../Notation.lean) restricts the
remainder of a `do`-block after a `let ← …` to be polymorphic in the
fresh post-state `s'`, because `IPFunctor.FreeM.bind` quantifies the
continuation universally. That kills most realistic chains.

This file lifts that restriction in the common case where every
`P.src s a b` is independent of the response `b` — i.e. `P` has *deterministic
transitions*. When that holds, an `IPFunctor.FreeM.lift s a`-style step
lands at a single concrete post-state `next s a`, and the continuation can
be specialized to that state instead of left polymorphic. Chains like

```
do
  let _ ← IPFunctor.FreeM.lift false ()   -- post-state: next false () = true
  let n ← IPFunctor.FreeM.lift true  ()   -- post-state: next true ()  = true
  pure n                                    -- at state true
```

then elaborate via a specialized bind `IPFunctor.FreeM.bindLiftA` rather
than the generic state-polymorphic one.

## Activation

Users must
* set `set_option backward.do.legacy false` (or, project-wide, via
  `[leanOptions]` in `lakefile.toml` — see
  [`../Notation.lean`](../Notation.lean) for the roadmap on this
  transitional flag), and
* provide an `IPFunctor.DeterministicTransitions P` instance, and
* express each monadic step using `IPFunctor.FreeM.lift` directly (or a
  `@[reducible]` alias). Steps that don't reduce to
  `IPFunctor.FreeM.lift s a` fall through to the generic single-index
  `IPFunctor.FreeM` elaborator, where they hit the usual
  polymorphic-continuation constraint.

## Limitations

We only specialize *single-action* steps (those reducing to
`IPFunctor.FreeM.lift s a`). A step that is itself a multi-step
`do`-block is *not* specialized — its internal leaves might genuinely
diverge, and detecting "all leaves land at one state" by structural
analysis would require an inductive proof we don't construct. Users who
hit this should nest a `do`-block of `IPFunctor.FreeM₂` instead, via the
conversion `IPFunctor.FreeM₂.toFreeM`.

See [`Indexed.lean`](Indexed.lean) for `IPFunctor.FreeM₂` `do`-notation,
which sidesteps the universal-quantification issue entirely by tracking
pre/post-state in the type.
-/

@[expose] public section

namespace IPFunctor.FreeMDetNotation

open Lean Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Lean.Parser.Term
open IPFunctor.FreeMNotation (isFreeMMonad?)

/-! ## Bind builder using `IPFunctor.FreeM.bindLiftA`

The monad-info detector is shared with the generic single-index notation:
this file reuses [`IPFunctor.FreeMNotation.isFreeMMonad?`](../Notation.lean),
brought into scope by the `open` above, so the `@[doElem_elab]` guard
matches exactly the same shapes the generic elaborator recognizes. -/

/--
Build `@IPFunctor.FreeM.bindLiftA` for a step that reduced to
`FreeM.lift s a`, followed by the continuation in `dec`. The
continuation is elaborated at `FreeM P (next s a) β`, where `next s a`
comes from the `DeterministicTransitions P` instance — no universal
quantification, so subsequent steps can be state-specific.
-/
meta def mkBindLiftA
    (dec : DoElemCont) (lvls : List Level)
    (I P s aShape detInst : Expr) : DoElabM Expr := do
  -- `DeterministicTransitions` is declared over `IPFunctor I J` (4 universes uI uJ uA uB).
  -- The `FreeM` universes are [uI, uA, uB, v]; for the endomorphic case `Endo I = IPFunctor I I`,
  -- we instantiate `uJ := uI` so the level list becomes [uI, uI, uA, uB].
  let detLvls : List Level := [lvls[0]!, lvls[0]!, lvls[1]!, lvls[2]!]
  -- next s a — a closed expression of type `I`. We want full default-transparency unfolding
  -- here to obtain the concrete post-state value, not just the head form.
  let nextState ← whnf <|
    mkAppN (mkConst ``IPFunctor.DeterministicTransitions.next detLvls)
      #[I, I, P, detInst, s, aShape]
  let xType := dec.resultType
  let declKind := Lean.LocalDeclKind.ofBinderName dec.resultName
  let nextM := mkAppN (mkConst ``IPFunctor.FreeM lvls) #[I, P, nextState]
  withLocalDecl dec.resultName .default xType (kind := declKind) fun xFVar => do
    let β := (← read).doBlockResultType
    let body ← withReader (fun c =>
        { c with monadInfo := { c.monadInfo with m := nextM } }) do
      let bodyRaw ← dec.k
      Term.ensureHasType (mkApp nextM β) bodyRaw
    let kLam ← mkLambdaFVars #[xFVar] body
    -- @bindLiftA.{uI,uA,uB,v} I P β det s a kLam — note `α` (the response type
    -- of `lift`) is implicit and inferred from `a`.
    return mkAppN (mkConst ``IPFunctor.FreeM.bindLiftA lvls)
      #[I, P, β, detInst, s, aShape, kLam]

/-! ## Elaborator

Only `doExpr` is overridden here. The `doLetArrow` form `let x ← rhs` is
delegated to the generic single-index elaborator in
[`../Notation.lean`](../Notation.lean) (`elabFreeMLetArrow`), which
recursively invokes `doElem` on `rhs` — and Lean's keyed-attribute
priority then picks *this* file's `doExpr` first for
`IPFunctor.FreeM.lift`-style steps. So a single `doLetArrow` override at
the bottom of the dispatch chain is enough; we just need a specialized
`doExpr` that catches the deterministic-step shape before the generic
one does. -/

/--
`doExpr` override for `FreeM P s` blocks where a `DeterministicTransitions P`
instance is in scope *and* the step's RHS reduces to `FreeM.lift s a`.
Specializes the continuation's pre-state to `det.next s a` so that the
rest of the block can use state-specific operations.

Falls through to the generic single-index `FreeM` elaborator if any
condition fails (no instance, non-`lift` shape, etc.).
-/
@[doElem_elab Lean.Parser.Term.doExpr]
meta def elabFreeMDetExpr : DoElab := fun stx dec => do
  let some (I, P, s, lvls) ← isFreeMMonad? (← read).monadInfo.m
    | throwUnsupportedSyntax
  -- Try to synthesize `DeterministicTransitions P`; fall through if not.
  -- `DeterministicTransitions` has 4 universes [uI, uJ, uA, uB]; the endomorphic
  -- specialization repeats `uI` for `uJ`.
  let detLvls : List Level := [lvls[0]!, lvls[0]!, lvls[1]!, lvls[2]!]
  let detClass := mkAppN (mkConst ``IPFunctor.DeterministicTransitions detLvls)
    #[I, I, P]
  let detInst ← try
    synthInstance detClass
  catch _ => throwUnsupportedSyntax
  -- Elaborate the term, then whnf-reduce to detect a `lift`-style action.
  -- `lift s a` is `@[reducible]`, so default-transparency `whnf` unfolds it to
  --   `FreeM.liftBind s a (fun b => FreeM.pure (P.src s a b) b)`.
  -- We detect that shape and trust the inner `pure` to mean "this is a
  -- single-action step".
  let `(doExpr| $e:term) := stx | throwUnsupportedSyntax
  let mα ← mkMonadApp dec.resultType
  let eExpr ← Term.elabTermEnsuringType e mα
  -- Reducible-transparency `whnf` so user-side `@[reducible]` aliases (`flip`, `lift`, …)
  -- unfold but the underlying plain-`def` `FreeM.liftBind` head survives for the check below.
  let eReduced ← Meta.withTransparency .reducible <| whnf eExpr
  unless eReduced.getAppFn.isConstOf ``IPFunctor.FreeM.liftBind do
    throwUnsupportedSyntax
  let args := eReduced.getAppArgs
  -- `@FreeM.liftBind {I} {P} {α} (s) (a) (r)` — 6 args after `getAppArgs`.
  unless args.size = 6 do throwUnsupportedSyntax
  let aShape := args[4]!
  let rFun := args[5]!
  -- `r` must be a single-step continuation: `fun b => FreeM.pure …`.
  -- Anything else (e.g. a nested `liftBind`) is a multi-step tree we can't
  -- safely specialize via `bindLiftA`.
  unless rFun.isLambda do throwUnsupportedSyntax
  unless rFun.bindingBody!.getAppFn.isConstOf ``IPFunctor.FreeM.pure do
    throwUnsupportedSyntax
  mkBindLiftA dec lvls I P s aShape detInst

end IPFunctor.FreeMDetNotation
