/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Notation.Indexed

/-!
# Smoke tests for the two-index `IPFunctor.FreeM₂` `do`-notation

Regression tests for the `do`-elaborator defined in
[`PolyFun.IPFunctor.Notation.Indexed`](../../PolyFun/IPFunctor/Notation/Indexed.lean):
`FreeM₂` chains of arbitrary length compose, and — when `I = PUnit` —
`IPFunctor.FreeM₂.toFreeM` followed by `IPFunctor.FreeM.erase` collapses the
trees to the corresponding `PFunctor.FreeM` trees.
-/

@[expose] public section

set_option backward.do.legacy false

namespace IPFunctorFreeM₂NotationTests

/-- A tiny `IPFunctor.Endo` over `Bool`. State `false` lets you `flip` (→ `true`);
state `true` lets you `read` (returns `Nat`, stays at `true`). -/
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

/-- The "flip" action as a two-index tree: pre `false`, post `true`. -/
def flip₂ : IPFunctor.FreeM₂ demoP false true Unit :=
  IPFunctor.FreeM₂.roll () (fun _ => IPFunctor.FreeM₂.pure ())

/-- The "read" action as a two-index tree: stays at `true`. -/
def read₂ : IPFunctor.FreeM₂ demoP true true Nat :=
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

/-- A `PUnit`-indexed `IPFunctor.Endo`: pick a `Bool` shape, get a `Nat` back. -/
def demoQ : IPFunctor.Endo PUnit where
  A _ := Bool
  B _ _ := Nat
  src _ _ _ := PUnit.unit

/-- A single-step action lifting the shape `b : Bool`. -/
def stepQ (b : Bool) :
    IPFunctor.FreeM₂ demoQ PUnit.unit PUnit.unit Nat :=
  IPFunctor.FreeM₂.roll b (fun n => IPFunctor.FreeM₂.pure n)

/-- A two-step `do`-tree on `FreeM₂ demoQ`. -/
def twoStep : IPFunctor.FreeM₂ demoQ PUnit.unit PUnit.unit Nat := do
  let n ← stepQ true
  let m ← stepQ false
  pure (n + m : Nat)

/-- A single-step `do`-tree on `FreeM₂ demoQ`. -/
def oneStep : IPFunctor.FreeM₂ demoQ PUnit.unit PUnit.unit Nat := do
  let n ← stepQ true
  pure (n + 1 : Nat)

/-- A pure-only `do`-tree on `FreeM₂ demoQ`. -/
def purely : IPFunctor.FreeM₂ demoQ PUnit.unit PUnit.unit Nat := do
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
