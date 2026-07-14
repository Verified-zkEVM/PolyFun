/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Notation

/-!
# Smoke tests for the single-index `IPFunctor.FreeM` `do`-notation

Regression tests for the `do`-elaborator defined in
[`PolyFun.IPFunctor.Notation`](../../PolyFun/IPFunctor/Notation.lean): the
supported positive subset (a state-changing bind followed by a
state-polymorphic continuation), the custom state-mismatch diagnostics, and
the `IPFunctor.FreeM.erase` interop on a `[Unique I]` index.

These live outside the `IPFunctor.FreeM` namespace so that `pure` resolves to
`Pure.pure` (via the typeclass instance) rather than to the
`IPFunctor.FreeM.pure` constructor (which has an explicit state argument and
would shadow).
-/

@[expose] public section

set_option backward.do.legacy false

namespace IPFunctorNotationTests

/-- A tiny `IPFunctor.Endo` over `Bool`. At state `false` only a trivial "flip"
shape is available, which transitions to state `true`; at state `true`
only a "read" shape is available, returning a `Nat` and staying at `true`. -/
def demoP : IPFunctor.Endo Bool where
  A
    | false => Unit
    | true  => Unit
  B
    | false, _ => Unit
    | true,  _ => Nat
  src
    | false, _, _ => true
    | true,  _, _ => true

/-- Lift the `flip` shape into a `FreeM` action at state `false`. -/
def flip : IPFunctor.FreeM demoP false Unit :=
  IPFunctor.FreeM.lift false ()

/-- Lift the `read` shape into a `FreeM` action at state `true`. -/
def read : IPFunctor.FreeM demoP true Nat :=
  IPFunctor.FreeM.lift true ()

/-! ### Positive tests

These exercise the supported subset: a single state-changing bind followed by
a polymorphic continuation (purely `pure` / `return` / control-flow over pure
arms). The constraint comes from `IPFunctor.FreeM.bind`'s state-polymorphic
continuation `(s' : I) → α → IPFunctor.FreeM P s' β`: every later step must
typecheck *for every post-state `s'`*, which in practice means it must use
only `Pure.pure` or helpers that are polymorphic in the state index. -/

-- Basic `let _ ← e; pure ()`.
example : IPFunctor.FreeM demoP false Unit := do
  let _ ← flip
  pure ()

-- `let _ ← e; pure y` with an arbitrary terminal value.
example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  pure 42

-- A bound name available in the terminal pure.
example : IPFunctor.FreeM demoP true Nat := do
  let n ← read
  pure (n + 1)

-- `return` form (resolves through the `Pure` instance).
example : IPFunctor.FreeM demoP true Nat := do
  let n ← read
  return n + 1

-- Mixed pure `let :=` after a monadic bind.
example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  let k := 17
  pure k

-- `have` (non-monadic) binder.
example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  have k : Nat := 3
  pure k

-- Terminal `pure` derived from intermediate result.
example : IPFunctor.FreeM demoP true Bool := do
  let n ← read
  pure (n > 0)

-- `if`-then-else over `pure` arms (branches share the post-state).
example (b : Bool) : IPFunctor.FreeM demoP true Nat := do
  let n ← read
  if b then pure n else pure (n + 1)

-- `match` with `pure` arms.
example (b : Bool) : IPFunctor.FreeM demoP true Nat := do
  let n ← read
  match b with
  | true  => pure n
  | false => pure (n + 1)

-- A do-block with no monadic step at all (just pure).
example : IPFunctor.FreeM demoP false Nat := do
  let x := 1
  let y := 2
  pure (x + y)

/-! ### Negative tests

These show the elaborator's custom diagnostic for state mismatches. Chaining
two `read`s after `flip` is the canonical failure mode: the post-state of
`flip` is a fresh `s'`, but `read`'s pre-state is the literal `true`. -/

/--
error: FreeM `do`-notation: state mismatch in this `do`-block step.
  expected pre-state: any post-state of the previous `let ← …` step (bound here as `s'`; `FreeM.bind` quantifies over it universally)
  actual pre-state:   true
`FreeM.bind`'s continuation has type `(s' : I) → α → FreeM P s' β`, so every step after a `let ← …` must typecheck for an arbitrary post-state — but this step is fixed at the concrete state above. Use a state-polymorphic helper, pattern-match on the previous response, or write `FreeM.bind` explicitly.
-/
#guard_msgs in
example : IPFunctor.FreeM demoP false Nat := do
  flip
  read

/--
error: FreeM `do`-notation: state mismatch in this `do`-block step.
  expected pre-state: any post-state of the previous `let ← …` step (bound here as `s'`; `FreeM.bind` quantifies over it universally)
  actual pre-state:   true
`FreeM.bind`'s continuation has type `(s' : I) → α → FreeM P s' β`, so every step after a `let ← …` must typecheck for an arbitrary post-state — but this step is fixed at the concrete state above. Use a state-polymorphic helper, pattern-match on the previous response, or write `FreeM.bind` explicitly.
-/
#guard_msgs in
example : IPFunctor.FreeM demoP false Nat := do
  let _ ← flip
  let n ← read
  pure n

/-! ### `IPFunctor.FreeM.erase` interop

On a `[Unique I]` index, `IPFunctor.FreeM.erase` collapses `do`-block trees
built via the single-index elaborator to the corresponding `PFunctor.FreeM`
trees. The `@[simp]` lemmas `erase_punit_pure` / `erase_punit_liftBind` in
`Free/Basic.lean` do the simplification. -/

/-- A `PUnit`-indexed `IPFunctor.Endo`. Single-index `FreeM`'s universal
state-polymorphism constraint is vacuous here, since every leaf state
is forced to `PUnit.unit`. -/
def demoQ : IPFunctor.Endo PUnit where
  A _ := Bool
  B _ _ := Nat
  src _ _ _ := PUnit.unit

/-- A pure-only `do`-block erases to a pure leaf — no `lift` involved
so the universal-quantification limit doesn't bite. -/
example :
    IPFunctor.FreeM.erase demoQ PUnit.unit
        (do let k := 17; pure k : IPFunctor.FreeM demoQ PUnit.unit Nat)
    = PFunctor.FreeM.pure (P := demoQ.toPFunctor) 17 := by
  rfl

section Regression

-- Other monads still elaborate via the builtin elaborator. These confirm
-- our overrides don't claim non-`FreeM` `do`-blocks (the `isFreeMMonad?`
-- guard returns `none`, and we `throwUnsupportedSyntax`).
example : Id Nat := do
  let x := 1
  pure (x + 1)

example : List Nat := do
  let x ← [1, 2, 3]
  pure (x + 1)

example : Option Nat := do
  let x ← some 5
  pure (x + 1)

end Regression

end IPFunctorNotationTests
