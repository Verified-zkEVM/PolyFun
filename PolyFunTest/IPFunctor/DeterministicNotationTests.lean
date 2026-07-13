/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Notation.Deterministic

/-!
# Smoke tests for the deterministic `IPFunctor.FreeM` `do`-notation

Regression tests for the `do`-elaborator defined in
[`PolyFun.IPFunctor.Notation.Deterministic`](../../PolyFun/IPFunctor/Notation/Deterministic.lean):
under a `DeterministicTransitions` instance, long `FreeM` chains compose, and —
on a `[Unique I]` index — `IPFunctor.FreeM.erase` collapses the trees to the
corresponding `PFunctor.FreeM` trees.
-/

@[expose] public section

set_option backward.do.legacy false

namespace IPFunctorFreeMDetNotationTests

/-- The same demo `IPFunctor.Endo` as the other `Notation` files. Both states
transition to `true` regardless of the response, so deterministic. -/
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

/-- The deterministic-transitions instance for `demoP`. Both `(false, ())`
and `(true, ())` go to `true`. -/
instance instDemoP : IPFunctor.DeterministicTransitions demoP where
  next _ _ := true
  spec s a b := by cases s <;> rfl

/-- `flip` written as `lift false ()` and marked `@[reducible]` so the
elaborator can see through it. -/
@[reducible] def flip : IPFunctor.FreeM demoP false Unit :=
  IPFunctor.FreeM.lift false ()

/-- `read` written as `lift true ()` and marked `@[reducible]`. -/
@[reducible] def read : IPFunctor.FreeM demoP true Nat :=
  IPFunctor.FreeM.lift true ()

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

/-! ### `IPFunctor.FreeM.erase` interop

On a `[Unique I]` index, `IPFunctor.FreeM.erase` collapses a `do`-block
built via the deterministic-`IPFunctor.FreeM` elaborator to a
`PFunctor.FreeM` tree, with the `@[simp]` lemmas in `Free/Basic.lean`
doing the actual simplification. -/

/-- A `PUnit`-indexed `IPFunctor.Endo`: pick a `Bool`, get a `Nat` back. -/
def demoQ : IPFunctor.Endo PUnit where
  A _ := Bool
  B _ _ := Nat
  src _ _ _ := PUnit.unit

/-- Transitions for a `PUnit`-indexed `IPFunctor` are trivially deterministic. -/
instance instDemoQ : IPFunctor.DeterministicTransitions demoQ where
  next _ _ := PUnit.unit
  spec _ _ _ := rfl

/-- A `lift`-style step at the unit state. -/
@[reducible] def stepQ (b : Bool) :
    IPFunctor.FreeM demoQ PUnit.unit Nat :=
  IPFunctor.FreeM.lift PUnit.unit b

/-- A two-step `do`-tree on `FreeM demoQ`, using the deterministic elaborator. -/
def twoStepDet : IPFunctor.FreeM demoQ PUnit.unit Nat := do
  let n ← stepQ true
  let m ← stepQ false
  pure (n + m : Nat)

example :
    IPFunctor.FreeM.erase demoQ PUnit.unit twoStepDet
    = PFunctor.FreeM.liftBind (P := demoQ.toPFunctor) true (fun n : Nat =>
        PFunctor.FreeM.liftBind false (fun m : Nat =>
          PFunctor.FreeM.pure (n + m))) := by
  rfl

/-! ### Regression — non-`FreeM` monads still elaborate via fall-through. -/

example : Id Nat := do
  let x := 1
  pure (x + 1)

example : List Nat := do
  let x ← [1, 2, 3]
  pure (x + 1)

end IPFunctorFreeMDetNotationTests
