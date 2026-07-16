/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.SubstMonoid.Convolution
public import PolyFunTest.PFunctor.SubstMonoid

/-!
# Regression tests for convolution substitution monoids

The concrete canary combines the noncommutative word substitution monoid with
a three-state comonoid. Convolution emits the outer word before the inner word,
while its backward map threads the state through both internal-hom lenses. The
same example therefore detects reversed multiplication and broken state
threading.
-/

@[expose] public section

universe cA cB mA mB

namespace PFunctor
namespace SubstMonoidConvolutionTest

open SubstMonoidTest
open SubstMonoid

inductive ThreeState
  | source
  | middle
  | final
deriving DecidableEq

open ThreeState

/-- The outer internal-hom position emits `false` and advances the state to
`middle`. -/
def outer : Lens (selfMonomial ThreeState) wordP :=
  (fun _ => [false]) ⇆ (fun _ _ => middle)

/-- The inner internal-hom position emits `true` and advances the state to
`final` only when it receives the outer position's `middle` state. Its other
branches are deliberately different so the test observes state handoff. -/
def inner : Lens (selfMonomial ThreeState) wordP :=
  (fun
    | middle => [true]
    | _ => []) ⇆
  (fun
    | middle, _ => final
    | _, _ => source)

/-- A distinguishable continuation used away from the correct dependent
branch. If convolution selects the inner handler using the state produced by
`outer` instead of the state at which `outer` runs, this handler makes both
the emitted word and final state observably wrong. -/
def decoy : Lens (selfMonomial ThreeState) wordP :=
  (fun _ => [true, false]) ⇆ (fun _ _ => source)

/-- A two-stage convolution position with distinct outer and inner effects. -/
def twoStage :
    ((ihom (selfMonomial ThreeState) wordP) ◃
      (ihom (selfMonomial ThreeState) wordP)).A :=
  ⟨outer, fun
    | ⟨source, _⟩ => inner
    | _ => decoy⟩

/-- Convolution multiplication preserves outer-before-inner word order. -/
example :
    (convolutionMultRaw (stateComonoid ThreeState) wordMonoid).toFunA
      (twoStage, source) = [false, true] := by
  rfl

/-- The complete backward result records the matter positions used by the
outer and inner internal-hom lenses and threads the state to `final`.
Reversing or duplicating either stage changes this result. -/
example :
    (convolutionMultRaw (stateComonoid ThreeState) wordMonoid).toFunB
      (twoStage, source) PUnit.unit =
        (⟨⟨source, PUnit.unit⟩, ⟨middle, PUnit.unit⟩⟩, final) := by
  rfl

/-- Starting at `middle` must select the decoy continuation. This rules out an
implementation that ignores the dependent continuation and always uses
`inner`. -/
example :
    (convolutionMultRaw (stateComonoid ThreeState) wordMonoid).toFunA
      (twoStage, middle) = [false, true, false] := by
  rfl

/-- The alternate branch is also observable in the complete backward result:
the decoy receives `middle` and returns `source`. -/
example :
    (convolutionMultRaw (stateComonoid ThreeState) wordMonoid).toFunB
      (twoStage, middle) PUnit.unit =
        (⟨⟨middle, PUnit.unit⟩, ⟨middle, PUnit.unit⟩⟩, source) := by
  rfl

/-- The raw convolution unit emits the empty word. -/
example :
    (convolutionUnitRaw (stateComonoid ThreeState) wordMonoid).toFunA
      (PUnit.unit, source) = [] := by
  rfl

/-- The raw convolution unit follows the identity transition selected by the
comonoid counit. -/
example :
    ((convolutionUnitRaw (stateComonoid ThreeState) wordMonoid).toFunB
      (PUnit.unit, source) PUnit.unit).2 = source := by
  rfl

/-- The comonoid and target monoid may use four independent universes. -/
example (C : Comonoid.{cA, cB}) (M : SubstMonoid.{mA, mB}) :
    SubstMonoid.{max cA cB mA mB, max cA mB} :=
  convolution C M

/-- The independently universe-polymorphic construction returns the expected
internal-hom carrier. -/
example (C : Comonoid.{cA, cB}) (M : SubstMonoid.{mA, mB}) :
    (convolution C M).carrier = ihom C.carrier M.carrier := by
  simp

/-- The exported multiplication equation exposes the exact uncurried
semantics. -/
example (C : Comonoid.{cA, cB}) (M : SubstMonoid.{mA, mB}) :
    Lens.uncurry (convolution C M).mult = convolutionMultRaw C M :=
  uncurry_convolution_mult C M

/-- The exported unit equation exposes the exact uncurried semantics. -/
example (C : Comonoid.{cA, cB}) (M : SubstMonoid.{mA, mB}) :
    Lens.uncurry (convolution C M).unit = convolutionUnitRaw C M :=
  uncurry_convolution_unit C M

end SubstMonoidConvolutionTest
end PFunctor
