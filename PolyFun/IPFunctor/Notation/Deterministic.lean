/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Free.Basic
public import Lean.Elab.Do
meta import Lean.Parser.Do

/-!
# `do`-notation for `IPFunctor.FreeM` with deterministic transitions

The single-index `do`-notation in
[`PolyFun/IPFunctor/Notation.lean`](../Notation.lean) restricts the
remainder of a `do`-block after a `let ← …` to be polymorphic in the
fresh post-state `s'`, because `FreeM.bind` quantifies the continuation
universally. That kills most realistic chains.

This file lifts that restriction in the common case where every
`P.st s a b` is independent of the response `b` — i.e. `P` has *deterministic
transitions*. When that holds, a `liftA s a`-style step lands at a single
concrete post-state `next s a`, and the continuation can be specialized
to that state instead of left polymorphic. Chains like

```
do
  let _ ← liftA false ()   -- post-state: next false () = true
  let n ← liftA true  ()   -- post-state: next true ()  = true
  pure n                    -- at state true
```

then elaborate via a specialized bind `FreeM.bindLiftA` rather than the
generic state-polymorphic one.

## Activation

Users must
* set `set_option backward.do.legacy false`, and
* provide an `IPFunctor.DeterministicTransitions P` instance, and
* express each monadic step using `IPFunctor.FreeM.liftA` directly (or a
  `@[reducible]` alias). Steps that don't reduce to `liftA s a` fall
  through to the generic single-index `FreeM` elaborator, where they hit
  the usual polymorphic-continuation constraint.

## Limitations

We only specialize *single-action* steps (those reducing to `liftA s a`).
A step that is itself a multi-step `do`-block is *not* specialized — its
internal leaves might genuinely diverge, and detecting "all leaves land
at one state" by structural analysis would require an inductive proof we
don't construct. Users who hit this should nest a `do`-block of `FreeM₂`
instead, via the conversion `FreeM₂.toFreeM`.

See [`Indexed.lean`](Indexed.lean) for `FreeM₂` `do`-notation, which
sidesteps the universal-quantification issue entirely by tracking
pre/post-state in the type.
-/

@[expose] public section

universe uI uA uB v

/-- An `IPFunctor` has *deterministic transitions* when `P.st s a b` is
independent of the response `b`. Equivalently, `(fun b => P.st s a b)`
is a constant function for every shape `a`. -/
class IPFunctor.DeterministicTransitions {I : Type uI}
    (P : IPFunctor.{uI, uA, uB} I) where
  /-- The (unique) post-state after taking shape `a` at state `s`. -/
  next : (s : I) → P.A s → I
  /-- `P.st s a b` agrees with `next s a` for every response `b`. -/
  spec : ∀ s a b, P.st s a b = next s a

namespace IPFunctor.FreeM

variable {I : Type uI} {P : IPFunctor.{uI, uA, uB} I} {β : Type v}

/-- Specialized bind for a single `liftA`-style step under
`DeterministicTransitions`. The continuation receives the response `b`
at the *concrete* post-state `det.next s a` (no universal quantification
over leaf states). -/
@[always_inline, inline]
def bindLiftA [det : IPFunctor.DeterministicTransitions P]
    {s : I} (a : P.A s) (g : P.B s a → FreeM P (det.next s a) β) :
    FreeM P s β :=
  FreeM.roll s a (fun b => (det.spec s a b).symm ▸ g b)

@[simp]
lemma bindLiftA_eq [det : IPFunctor.DeterministicTransitions P]
    {s : I} (a : P.A s) (g : P.B s a → FreeM P (det.next s a) β) :
    bindLiftA a g = FreeM.roll s a (fun b => (det.spec s a b).symm ▸ g b) :=
  rfl

end IPFunctor.FreeM

namespace IPFunctor.FreeMDetNotation

open Lean Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Lean.Parser.Term

/-! ## Monad-info detection -/

/-- If `m = @IPFunctor.FreeM I P s`, return `(I, P, s)`. -/
meta def isFreeMMonad? (m : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let m ← whnf m
  unless m.getAppFn.isConstOf ``IPFunctor.FreeM do return none
  let args := m.getAppArgs
  unless args.size = 3 do return none
  return some (args[0]!, args[1]!, args[2]!)

/-! ## Bind builder using `FreeM.bindLiftA` -/

/--
Build `@IPFunctor.FreeM.bindLiftA` for a step that reduced to
`FreeM.liftA s a`, followed by the continuation in `dec`. The
continuation is elaborated at `FreeM P (next s a) β`, where `next s a`
comes from the `DeterministicTransitions P` instance — no universal
quantification, so subsequent steps can be state-specific.
-/
meta def mkBindLiftA
    (dec : DoElemCont) (I P s aShape detInst : Expr) : DoElabM Expr := do
  let info := (← read).monadInfo
  let lvls := info.m.getAppFn.constLevels!
  unless lvls.length = 4 do
    throwError "FreeMDet `do`-notation: unexpected universe count."
  let detLvls := lvls.take 3
  -- next s a — a closed expression of type `I`.
  let nextState := mkAppN (mkConst ``IPFunctor.DeterministicTransitions.next detLvls)
    #[I, P, detInst, s, aShape]
  let nextState ← whnf nextState
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
    -- of `liftA`) is implicit and inferred from `a`.
    return mkAppN (mkConst ``IPFunctor.FreeM.bindLiftA lvls)
      #[I, P, β, detInst, s, aShape, kLam]

/-! ## Elaborator -/

/--
`doExpr` override for `FreeM P s` blocks where a `DeterministicTransitions P`
instance is in scope *and* the step's RHS reduces to `FreeM.liftA s a`.
Specializes the continuation's pre-state to `det.next s a` so that the
rest of the block can use state-specific operations.

Falls through to the generic single-index `FreeM` elaborator if any
condition fails (no instance, non-`liftA` shape, etc.).
-/
@[doElem_elab Lean.Parser.Term.doExpr]
meta def elabFreeMDetExpr : DoElab := fun stx dec => do
  let some (I, P, s) ← isFreeMMonad? (← read).monadInfo.m
    | throwUnsupportedSyntax
  let lvls := (← read).monadInfo.m.getAppFn.constLevels!
  let detLvls := lvls.take 3
  -- Try to synthesize `DeterministicTransitions P`; fall through if not.
  let detClass := mkAppN (mkConst ``IPFunctor.DeterministicTransitions detLvls)
    #[I, P]
  let detInst ← try
    synthInstance detClass
  catch _ => throwUnsupportedSyntax
  -- Elaborate the term, then whnf-reduce to detect a `liftA`-style action.
  -- `liftA s a` is `@[reducible]`, so `whnf .all` unfolds it to
  --   `FreeM.roll s a (fun b => FreeM.pure (P.st s a b) b)`.
  -- We detect that shape and trust the inner `pure` to mean "this is a
  -- single-action step".
  let `(doExpr| $e:term) := stx | throwUnsupportedSyntax
  let mα ← mkMonadicType dec.resultType
  let eExpr ← Term.elabTermEnsuringType e mα
  let eReduced ← withTransparency .all <| whnf eExpr
  unless eReduced.getAppFn.isConstOf ``IPFunctor.FreeM.roll do
    throwUnsupportedSyntax
  let args := eReduced.getAppArgs
  -- `@FreeM.roll {I} {P} {α} (s) (a) (r)` — 6 args after `getAppArgs`.
  unless args.size = 6 do throwUnsupportedSyntax
  let aShape := args[4]!
  let rFun := args[5]!
  -- `r` must be a single-step continuation: `fun b => FreeM.pure …`.
  -- Anything else (e.g. a nested `roll`) is a multi-step tree we can't
  -- safely specialize via `bindLiftA`.
  unless rFun.isLambda do throwUnsupportedSyntax
  unless rFun.bindingBody!.getAppFn.isConstOf ``IPFunctor.FreeM.pure do
    throwUnsupportedSyntax
  mkBindLiftA dec I P s aShape detInst

end IPFunctor.FreeMDetNotation

/-! ## Tests -/

set_option backward.do.legacy false

namespace IPFunctorFreeMDetNotationTests

/-- The same demo `IPFunctor` as the other `Notation` files. Both states
transition to `true` regardless of the response, so deterministic. -/
@[expose] def demoP : IPFunctor Bool where
  A
    | false => Unit
    | true  => Unit
  B
    | false, _ => Unit
    | true,  _ => Nat
  st
    | false, _, _ => true
    | true,  _, _ => true

/-- The deterministic-transitions instance for `demoP`. Both `(false, ())`
and `(true, ())` go to `true`. -/
@[expose] instance instDemoP : IPFunctor.DeterministicTransitions demoP where
  next _ _ := true
  spec s a b := by cases s <;> rfl

/-- `flip` written as `liftA false ()` and marked `@[reducible]` so the
elaborator can see through it. -/
@[reducible, expose] def flip : IPFunctor.FreeM demoP false Unit :=
  IPFunctor.FreeM.liftA false ()

/-- `read` written as `liftA true ()` and marked `@[reducible]`. -/
@[reducible, expose] def read : IPFunctor.FreeM demoP true Nat :=
  IPFunctor.FreeM.liftA true ()

/-! ### Positive tests — long chains now compose. -/

example : IPFunctor.FreeM demoP false Unit := do
  let _ ← flip
  pure ()

example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  let n ← read
  pure n

example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  let a ← read
  let b ← read
  let c ← read
  pure (a + b + c)

example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  let k := 17
  let n ← read
  pure (k + n)

example : IPFunctor.FreeM demoP true Nat := do
  let n ← read
  return n + 1

example (b : Bool) : IPFunctor.FreeM demoP true Nat := do
  let n ← read
  if b then pure n else pure (n + 1)

/-! ### Regression — non-`FreeM` monads still elaborate via fall-through. -/

example : Id Nat := do
  let x := 1
  pure (x + 1)

example : List Nat := do
  let x ← [1, 2, 3]
  pure (x + 1)

end IPFunctorFreeMDetNotationTests
