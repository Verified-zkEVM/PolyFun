/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Equiv.Basic

/-!
# Product-over-sum distributivity regression tests

These examples pin both directions of product-over-sum distributivity on
branch-sensitive fixtures whose position and direction types occupy different
universes. They also exercise the public projection simplification lemmas.
-/

@[expose] public section

namespace PFunctor.EquivProdSumDistribCanary

abbrev P : PFunctor.{1, 0} := ⟨Type, fun _ => Bool⟩

abbrev Q : PFunctor.{0, 1} := ⟨Bool, fun _ => Type⟩

abbrev R : PFunctor.{2, 1} := ⟨Type 1, fun _ => ULift.{1} Bool⟩

abbrev leftPosition : (P * (Q + R)).A := (Nat, Sum.inl true)

abbrev rightPosition : (P * (Q + R)).A := (String, Sum.inr Type)

@[simps (rhsMd := .default)]
def wrapped :
    (P * (Q + R) : PFunctor.{2, 1}) ≃ₚ
    ((P * Q) + (P * R) : PFunctor.{2, 1}) :=
  PFunctor.Equiv.prodSumDistrib P Q R

#check wrapped_equivB

/-! The wrapper canary rejects losing the producer's generated response projection metadata. -/

example : wrapped.equivB leftPosition (Sum.inr Nat) = Sum.inr Nat := by
  rw [wrapped_equivB]
  rfl

/-! The forward position canaries reject a swapped or collapsed sum branch. -/

example :
    (PFunctor.Equiv.prodSumDistrib P Q R).equivA
      leftPosition = Sum.inl (Nat, true) := by
  rw [PFunctor.Equiv.prodSumDistrib_equivA]
  rfl

example :
    (PFunctor.Equiv.prodSumDistrib P Q R).equivA
      rightPosition = Sum.inr (String, Type) := by
  rw [PFunctor.Equiv.prodSumDistrib_equivA]
  rfl

/-! The backward position canaries reject a non-inverse branch or reversed product order. -/

example :
    (PFunctor.Equiv.prodSumDistrib P Q R).equivA.symm
      (Sum.inl (Nat, false)) = (Nat, Sum.inl false) := by
  rw [PFunctor.Equiv.prodSumDistrib_equivA]
  rfl

example :
    (PFunctor.Equiv.prodSumDistrib P Q R).equivA.symm
      (Sum.inr (String, Type)) = (String, Sum.inr Type) := by
  rw [PFunctor.Equiv.prodSumDistrib_equivA]
  rfl

/-! The forward direction canaries reject selecting or copying the wrong direction summand. -/

example :
    (PFunctor.Equiv.prodSumDistrib P Q R).equivB
      leftPosition (Sum.inl false) = Sum.inl false := by
  rw [PFunctor.Equiv.prodSumDistrib_equivB]
  rfl

example :
    (PFunctor.Equiv.prodSumDistrib P Q R).equivB
      leftPosition (Sum.inr Nat) = Sum.inr Nat := by
  rw [PFunctor.Equiv.prodSumDistrib_equivB]
  rfl

/-! The backward direction canaries reject a constant inverse or the wrong dependent branch. -/

example :
    ((PFunctor.Equiv.prodSumDistrib P Q R).equivB
      rightPosition).symm (Sum.inl true) = Sum.inl true := by
  rw [PFunctor.Equiv.prodSumDistrib_equivB]
  rfl

example :
    ((PFunctor.Equiv.prodSumDistrib P Q R).equivB
      rightPosition).symm (Sum.inr (ULift.up false)) =
        Sum.inr (ULift.up false) := by
  rw [PFunctor.Equiv.prodSumDistrib_equivB]
  rfl

end PFunctor.EquivProdSumDistribCanary
