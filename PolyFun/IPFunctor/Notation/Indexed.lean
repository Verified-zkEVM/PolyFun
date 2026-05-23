/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Free.Indexed
public import Lean.Elab.Do
meta import Lean.Parser.Do

/-!
# `do`-notation for `IPFunctor.FreeM₂`

The two-index variant `IPFunctor.FreeM₂ P s t α` tracks both pre- and
post-state statically. Its bind has signature
`IPFunctor.FreeM₂ P s t α → (α → IPFunctor.FreeM₂ P t u β) → IPFunctor.FreeM₂ P s u β`
— no universal quantification over the post-state — so arbitrarily long
chains compose naturally under ordinary `do`-notation.

Like the single-index variant in `PolyFun/IPFunctor/Notation.lean`, this
file plugs into the Lean 4.29 extensible do-elaborator. Users opt in by
setting `set_option backward.do.legacy false` (or, project-wide, via
`[leanOptions]` in `lakefile.toml` — see
[`../Notation.lean`](../Notation.lean) for the roadmap on this
transitional flag). Our overrides check the expected type and fall
through (`throwUnsupportedSyntax`) for any monad other than
`IPFunctor.FreeM₂ P s t`.

## Why three flavors of `IPFunctor` `do`-notation?

* [`PolyFun/IPFunctor/Notation.lean`](../Notation.lean) — single-index
  `IPFunctor.FreeM` with the universal-quantification constraint. Bind
  continuation is `(s' : I) → α → IPFunctor.FreeM P s' β`; the remainder
  of the `do`-block must typecheck for *every* leaf state. Useful when
  the tail of the block is state-polymorphic (typically just `pure`).
* This file — `IPFunctor.FreeM₂`. Bind continuation is
  `α → IPFunctor.FreeM₂ P t u β`. The intermediate state `t` is
  statically tracked, single-valued, and recoverable from `e`'s actual
  type via unification. Chains of any length compose naturally. Use
  when every step's tree has a single converging post-state.
* [`Deterministic.lean`](Deterministic.lean) — single-index
  `IPFunctor.FreeM` plus a `DeterministicTransitions P` class.
  Specializes `IPFunctor.FreeM.liftA`-style steps to a concrete
  post-state via the class, so chains compose without switching to
  `IPFunctor.FreeM₂`. Useful when you want to stay on `IPFunctor.FreeM`
  for downstream compatibility.

The forgetful map `IPFunctor.FreeM₂.toFreeM` lets you embed an
`IPFunctor.FreeM₂` tree back into `IPFunctor.FreeM` if you mostly work
with the indexed variant but need to hand a value to an
`IPFunctor.FreeM`-shaped API.
-/

@[expose] public section

namespace IPFunctor.FreeM₂Notation

open Lean Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term Lean.Parser.Term

/-! ## Monad-info detection -/

/--
If `m` is `@IPFunctor.FreeM₂ I P s t` for some `I, P, s, t`, return those
four arguments together with the universe levels on the `FreeM₂` constant;
otherwise `none`. Returning the levels here avoids a second `whnf` +
`getAppFn` walk in the elaborators that consume the detector's output.
-/
meta def isFreeM₂Monad? (m : Expr) :
    MetaM (Option (Expr × Expr × Expr × Expr × List Level)) := do
  let m ← whnf m
  let fn := m.getAppFn
  unless fn.isConstOf ``IPFunctor.FreeM₂ do return none
  let args := m.getAppArgs
  unless args.size = 4 do return none
  return some (args[0]!, args[1]!, args[2]!, args[3]!, fn.constLevels!)

/-! ## Bind builder -/

/--
Build `@IPFunctor.FreeM₂.bind` for `e : FreeM₂ P s tStep α` followed by
the continuation in `dec`. Unlike the single-index case, the intermediate
post-state `tStep` is a *concrete value* (a metavariable assigned by
unification with `e`'s actual type), not a universally-quantified
binder. The continuation is elaborated at `FreeM₂ P tStep uOuter β`,
where `uOuter` is the do-block's overall post-state extracted from the
monadic context.
-/
meta def mkBindFreeM₂
    (dec : DoElemCont) (lvls : List Level) (I P s tStep uOuter e : Expr) :
    DoElabM Expr := do
  let xType := dec.resultType
  let declKind := Lean.LocalDeclKind.ofBinderName dec.resultName
  let nextM := mkAppN (mkConst ``IPFunctor.FreeM₂ lvls) #[I, P, tStep, uOuter]
  withLocalDecl dec.resultName .default xType (kind := declKind) fun xFVar => do
    let β := (← read).doBlockResultType
    let body ← withReader (fun c =>
        { c with monadInfo := { c.monadInfo with m := nextM } }) do
      let bodyRaw ← dec.k
      Term.ensureHasType (mkApp nextM β) bodyRaw
    let kLam ← mkLambdaFVars #[xFVar] body
    return mkAppN (mkConst ``IPFunctor.FreeM₂.bind lvls)
      #[I, P, xType, β, s, tStep, uOuter, e, kLam]

/-! ## Elaborators -/

/--
`doExpr` override for `FreeM₂`. Elaborates the term against the *current*
monad type `FreeM₂ P s uOuter α`, where `uOuter` is the do-block's
overall post-state. After elaboration, infer `e`'s actual type to read
off the intermediate post-state `tStep`, which becomes the pre-state of
the next step.

Using the concrete `uOuter` rather than a fresh metavariable lets
`Pure (FreeM₂ P s s)` resolve eagerly for terminal `pure x` — instance
synthesis only fires when both type arguments are concrete.
-/
@[doElem_elab Lean.Parser.Term.doExpr]
meta def elabFreeM₂Expr : DoElab := fun stx dec => do
  let some (I, P, s, uOuter, lvls) ← isFreeM₂Monad? (← read).monadInfo.m
    | throwUnsupportedSyntax
  let `(doExpr| $e:term) := stx | throwUnsupportedSyntax
  -- First attempt: assume this step is state-preserving (pre = post = s).
  -- Concrete on both type arguments, so `Pure (FreeM₂ P s s)` resolves
  -- eagerly for `pure x`/`return x`. A fresh post-state metavariable
  -- would postpone instance synthesis past the end of the do-block,
  -- leaving `Pure (FreeM₂ P s ?t)` stuck.
  let mαPreserve :=
    mkAppN (mkConst ``IPFunctor.FreeM₂ lvls) #[I, P, s, s] |>.app dec.resultType
  let saved ← saveState
  let attempt? : Option (Expr × Expr) ← try
    let eExpr ← Term.withoutErrToSorry <|
      Term.withSynthesize (postpone := .no) <|
      Term.elabTermEnsuringType e mαPreserve
    pure (some (s, eExpr))
  catch _ =>
    saved.restore
    pure none
  match attempt? with
  | some (tStep, eExpr) =>
    mkBindFreeM₂ dec lvls I P s tStep uOuter eExpr
  | none =>
    -- Second attempt: use a fresh metavariable for the post-state and let
    -- unification fix it from `e`'s actual type. Required for state-changing
    -- steps where pre ≠ post.
    let tFresh ← mkFreshExprMVar I (userName := `t)
    let stepM := mkAppN (mkConst ``IPFunctor.FreeM₂ lvls) #[I, P, s, tFresh]
    let mα := mkApp stepM dec.resultType
    let eExpr ← Term.elabTermEnsuringType e mα
    let tStep ← instantiateMVars tFresh
    mkBindFreeM₂ dec lvls I P s tStep uOuter eExpr

/--
`doLetArrow` override for `FreeM₂`. Recursively elaborate the RHS at the
binding's type, then bind the result to `x` in the continuation. Pattern
bindings (`let (a, b) ← e`) and `mut` bindings fall through.
-/
@[doElem_elab Lean.Parser.Term.doLetArrow]
meta def elabFreeM₂LetArrow : DoElab := fun stx dec => do
  unless (← isFreeM₂Monad? (← read).monadInfo.m).isSome do throwUnsupportedSyntax
  let `(doLetArrow| let $[mut%$mutTk?]? $decl) := stx | throwUnsupportedSyntax
  if mutTk?.isSome then throwUnsupportedSyntax
  match decl with
  | `(doIdDecl| $x:ident $[: $xType?]? ← $rhs) =>
    let xType ← Term.elabType (xType?.getD (Lean.mkHole x))
    elabDoElem rhs <| .mk (kind := dec.kind) x.getId xType do
      Term.addLocalVarInfo x (← getFVarFromUserName x.getId)
      dec.continueWithUnit
  | `(doPatDecl| _%$pat ← $rhs) =>
    let x := mkIdentFrom pat (← mkFreshUserName `__x)
    let xType ← Term.elabType (Lean.mkHole x)
    elabDoElem rhs <| .mk (kind := dec.kind) x.getId xType do
      dec.continueWithUnit
  | _ => throwUnsupportedSyntax

end IPFunctor.FreeM₂Notation

/-! ## Tests -/

set_option backward.do.legacy false

namespace IPFunctorFreeM₂NotationTests

/-- A tiny `IPFunctor` over `Bool`. State `false` lets you `flip` (→ `true`);
state `true` lets you `read` (returns `Nat`, stays at `true`). -/
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

/-- The "flip" action as a two-index tree: pre `false`, post `true`. -/
@[expose] def flip₂ : IPFunctor.FreeM₂ demoP false true Unit :=
  IPFunctor.FreeM₂.roll () (fun _ => IPFunctor.FreeM₂.pure ())

/-- The "read" action as a two-index tree: stays at `true`. -/
@[expose] def read₂ : IPFunctor.FreeM₂ demoP true true Nat :=
  IPFunctor.FreeM₂.roll () (fun n => IPFunctor.FreeM₂.pure n)

/-! ### Positive tests — chains of any length compose. -/

example : IPFunctor.FreeM₂ demoP false true Unit := do
  let _ ← flip₂
  pure ()

example : IPFunctor.FreeM₂ demoP false true Nat := do
  let _ ← flip₂
  let n ← read₂
  pure n

example : IPFunctor.FreeM₂ demoP false true Nat := do
  let _ ← flip₂
  let a ← read₂
  let b ← read₂
  let c ← read₂
  pure (a + b + c)

example : IPFunctor.FreeM₂ demoP false true Nat := do
  let _ ← flip₂
  let k := 17
  let n ← read₂
  pure (k + n)

example : IPFunctor.FreeM₂ demoP false true Nat := do
  let n ← do
    let _ ← flip₂
    read₂
  pure (n + 1)

example : IPFunctor.FreeM₂ demoP true true Nat := do
  let n ← read₂
  return n + 1

example (b : Bool) : IPFunctor.FreeM₂ demoP true true Nat := do
  let n ← read₂
  if b then pure n else pure (n + 1)

example : IPFunctor.FreeM₂ demoP true true Nat := do
  let a ← read₂
  let b ← read₂
  pure (a * b)

/-! ### `IPFunctor.FreeM.erase` interop

When `I = PUnit` the `IPFunctor` is just a `PFunctor`, and
`IPFunctor.FreeM₂.toFreeM` followed by `IPFunctor.FreeM.erase` should
collapse `do`-block trees to the corresponding `PFunctor.FreeM` trees via
the `@[simp]` lemmas in `Free/Basic.lean` (`erase_punit_pure`,
`erase_punit_roll`, `toFreeM_pure`, `toFreeM_roll`). -/

/-- A `PUnit`-indexed `IPFunctor`: pick a `Bool` shape, get a `Nat` back. -/
@[expose] def demoQ : IPFunctor PUnit where
  A _ := Bool
  B _ _ := Nat
  st _ _ _ := PUnit.unit

/-- A single-step action lifting the shape `b : Bool`. -/
@[expose] def stepQ (b : Bool) :
    IPFunctor.FreeM₂ demoQ PUnit.unit PUnit.unit Nat :=
  IPFunctor.FreeM₂.roll b (fun n => IPFunctor.FreeM₂.pure n)

/-- A two-step `do`-tree on `FreeM₂ demoQ`. -/
@[expose] def twoStep : IPFunctor.FreeM₂ demoQ PUnit.unit PUnit.unit Nat := do
  let n ← stepQ true
  let m ← stepQ false
  pure (n + m : Nat)

/-- A single-step `do`-tree on `FreeM₂ demoQ`. -/
@[expose] def oneStep : IPFunctor.FreeM₂ demoQ PUnit.unit PUnit.unit Nat := do
  let n ← stepQ true
  pure (n + 1 : Nat)

/-- A pure-only `do`-tree on `FreeM₂ demoQ`. -/
@[expose] def purely : IPFunctor.FreeM₂ demoQ PUnit.unit PUnit.unit Nat := do
  let k := 42
  pure k

-- `erase ∘ toFreeM` on a two-step `do`-tree is definitionally a nested
-- `PFunctor.FreeM.roll` chain.
example :
    IPFunctor.FreeM.erase demoQ PUnit.unit twoStep.toFreeM
    = PFunctor.FreeM.roll (P := demoQ.toPFunctor) true (fun n : Nat =>
        PFunctor.FreeM.roll false (fun m : Nat =>
          PFunctor.FreeM.pure (n + m))) := by
  rfl

-- `simp` collapses the erased one-step tree using the `erase_punit_*` /
-- `toFreeM_*` simp lemmas plus the obvious unfolds.
example :
    IPFunctor.FreeM.erase demoQ PUnit.unit oneStep.toFreeM
    = PFunctor.FreeM.roll (P := demoQ.toPFunctor) true (fun n : Nat =>
        PFunctor.FreeM.pure (n + 1)) := by
  rfl

-- A pure-only do-block erases to a pure leaf.
example :
    IPFunctor.FreeM.erase demoQ PUnit.unit purely.toFreeM
    = PFunctor.FreeM.pure (P := demoQ.toPFunctor) 42 := by
  rfl

-- `simp` (rather than `rfl`) drives the same reduction via the
-- `@[simp]`-tagged `erase_punit_*` / `toFreeM_*` lemmas plus the unfolds.
example :
    IPFunctor.FreeM.erase demoQ PUnit.unit oneStep.toFreeM
    = PFunctor.FreeM.roll (P := demoQ.toPFunctor) true (fun n : Nat =>
        PFunctor.FreeM.pure (n + 1)) := by
  change IPFunctor.FreeM.erase demoQ PUnit.unit
      ((IPFunctor.FreeM₂.bind (stepQ true)
        (fun n => IPFunctor.FreeM₂.pure (n + 1))).toFreeM) = _
  simp [stepQ, IPFunctor.FreeM₂.bind]
  rfl

/-! ### Regression — non-`IPFunctor.FreeM₂` monads still work via fall-through. -/

example : Id Nat := do
  let x := 1
  pure (x + 1)

example : Option Nat := do
  let x ← some 5
  pure (x + 1)

end IPFunctorFreeM₂NotationTests
