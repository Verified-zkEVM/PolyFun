/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Basic

/-!
# Structural Equivalences Between Indexed Polynomial Functors

This file defines `IPFunctor.Equiv P Q`, the structural equivalence between two indexed
polynomial functors `P Q : IPFunctor I J`: a fiberwise equivalence of `A`-types, a fiberwise
equivalence of `B`-types compatible with the `A`-equivalence, and a source-index preservation
law `src_eq`.

This is the indexed analogue of [`PFunctor.Equiv`](../../PFunctor/Equiv/Basic.lean). Like the
non-indexed version, it is strictly stronger than the lens / chart equivalence: every
`IPFunctor.Equiv` yields both an `IPFunctor.Lens.Equiv` and an `IPFunctor.Chart.Equiv` (those
bridges are TODO and live alongside the operations they unblock).
-/

@[expose] public section

universe uI uJ uA₁ uA₂ uA₃ uB₁ uB₂ uB₃

namespace IPFunctor

variable {I : Type uI} {J : Type uJ}

/-- A **structural equivalence** between indexed polynomial functors `P Q : IPFunctor I J`:
fiberwise type equivalences on positions and responses, plus a source-index preservation
law. -/
@[ext]
protected structure Equiv (P : IPFunctor.{uI, uJ, uA₁, uB₁} I J)
                          (Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J) where
  /-- A fiberwise equivalence on positions. -/
  equivA : ∀ j, P.A j ≃ Q.A j
  /-- A fiberwise equivalence on responses, compatible with `equivA`. -/
  equivB : ∀ j a, P.B j a ≃ Q.B j (equivA j a)
  /-- Source-index preservation. -/
  src_eq : ∀ j a b, P.src j a b = Q.src j (equivA j a) (equivB j a b)

@[inherit_doc] scoped infixl:25 " ≃ₚ " => IPFunctor.Equiv

namespace Equiv

variable {P : IPFunctor.{uI, uJ, uA₁, uB₁} I J}
  {Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J}
  {R : IPFunctor.{uI, uJ, uA₃, uB₃} I J}

/-- The identity equivalence. -/
@[refl]
def refl (P : IPFunctor.{uI, uJ, uA₁, uB₁} I J) : P ≃ₚ P where
  equivA _ := _root_.Equiv.refl _
  equivB _ _ := _root_.Equiv.refl _
  src_eq _ _ _ := rfl

/-- The inverse of a structural equivalence. The response side is built by
pulling `d : Q.B j a'` back through the round-trip cast and then taking the
symm of `e.equivB` at the preimage `(e.equivA j).symm a'`. Mirrors
[`PFunctor.Equiv.symm`](../../PFunctor/Equiv/Basic.lean) fiberwise, with the
extra `src_eq` discharged by applying `e.src_eq` at the preimage and
collapsing the round-trip via `Equiv.apply_symm_apply` and `cast_heq`. -/
@[symm]
def symm (e : P ≃ₚ Q) : Q ≃ₚ P where
  equivA j := (e.equivA j).symm
  equivB j a :=
    (_root_.Equiv.cast
        (congrArg (Q.B j) ((_root_.Equiv.symm_apply_eq (e.equivA j)).mp rfl))).trans
      (e.equivB j ((e.equivA j).symm a)).symm
  src_eq j a d := by
    apply Eq.symm
    simp only [_root_.Equiv.trans_apply]
    rw [e.src_eq j ((e.equivA j).symm a)
      ((e.equivB j ((e.equivA j).symm a)).symm
        (_root_.Equiv.cast
          (congrArg (Q.B j) ((_root_.Equiv.symm_apply_eq (e.equivA j)).mp rfl)) d))]
    simp only [_root_.Equiv.apply_symm_apply]
    congr 1
    · exact (e.equivA j).apply_symm_apply a
    · exact cast_heq _ d

/-- Composition of structural equivalences. Both `equivA` and `equivB` compose
diagrammatically; the `src_eq` chains by transitivity. Mirrors
[`PFunctor.Equiv.trans`](../../PFunctor/Equiv/Basic.lean) fiberwise. -/
@[trans]
def trans (e₁ : P ≃ₚ Q) (e₂ : Q ≃ₚ R) : P ≃ₚ R where
  equivA j := (e₁.equivA j).trans (e₂.equivA j)
  equivB j a := (e₁.equivB j a).trans (e₂.equivB j (e₁.equivA j a))
  src_eq j a b :=
    (e₁.src_eq j a b).trans (e₂.src_eq j (e₁.equivA j a) (e₁.equivB j a b))

end Equiv

end IPFunctor
