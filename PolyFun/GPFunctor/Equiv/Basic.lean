/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.GPFunctor.Basic
public import PolyFun.IPFunctor.Equiv.Basic

/-!
# Structural Equivalences Between Graded Polynomial Functors

This file defines `GPFunctor.Equiv P Q`, the structural equivalence between two graded
polynomial functors `P Q : GPFunctor G`: an equivalence of `A`-types, a fiberwise equivalence
of `B`-types compatible with the `A`-equivalence, and a grade preservation law `grade_eq`.

This is the graded analogue of [`PFunctor.Equiv`](../../PFunctor/Basic.lean) and
[`IPFunctor.Equiv`](../../IPFunctor/Equiv/Basic.lean). Because grading is per-shape, the
preservation law mentions no responses, which makes `symm` lighter than the indexed version:
the grade side closes by `Equiv.apply_symm_apply` alone. Over `[Mul G]`, an equivalence
induces an `IPFunctor.Equiv` on the indexed images (`toIPEquiv`).
-/

@[expose] public section

universe uG uA uA₁ uA₂ uA₃ uB uB₁ uB₂ uB₃

namespace GPFunctor

variable {G : Type uG}

/-- A **structural equivalence** between graded polynomial functors `P Q : GPFunctor G`:
type equivalences on positions and responses, plus a grade preservation law. -/
@[ext]
protected structure Equiv (P : GPFunctor.{uG, uA₁, uB₁} G)
                          (Q : GPFunctor.{uG, uA₂, uB₂} G) where
  /-- An equivalence on positions. -/
  equivA : P.A ≃ Q.A
  /-- A fiberwise equivalence on responses, compatible with `equivA`. -/
  equivB : ∀ a, P.B a ≃ Q.B (equivA a)
  /-- Grade preservation. -/
  grade_eq : ∀ a, P.grade a = Q.grade (equivA a)

@[inherit_doc] scoped infixl:25 " ≃ᵍ " => GPFunctor.Equiv

namespace Equiv

variable {P : GPFunctor.{uG, uA₁, uB₁} G} {Q : GPFunctor.{uG, uA₂, uB₂} G}
  {R : GPFunctor.{uG, uA₃, uB₃} G}

/-- The identity equivalence. -/
@[refl]
def refl (P : GPFunctor.{uG, uA₁, uB₁} G) : P ≃ᵍ P where
  equivA := _root_.Equiv.refl _
  equivB _ := _root_.Equiv.refl _
  grade_eq _ := rfl

/-- The inverse of a structural equivalence. The response side pulls `d : Q.B a` back
through the round-trip cast and then takes the symm of `e.equivB` at the preimage
`e.equivA.symm a`; the grade side is `e.grade_eq` at the preimage, with the round-trip
collapsed by `Equiv.apply_symm_apply`. -/
@[symm]
def symm (e : P ≃ᵍ Q) : Q ≃ᵍ P where
  equivA := e.equivA.symm
  equivB a :=
    (_root_.Equiv.cast
        (congrArg Q.B ((_root_.Equiv.symm_apply_eq e.equivA).mp rfl))).trans
      (e.equivB (e.equivA.symm a)).symm
  grade_eq a :=
    ((e.grade_eq (e.equivA.symm a)).trans
      (congrArg Q.grade (e.equivA.apply_symm_apply a))).symm

/-- Composition of structural equivalences: both `equivA` and `equivB` compose
diagrammatically, and `grade_eq` chains by transitivity. -/
@[trans]
def trans (e₁ : P ≃ᵍ Q) (e₂ : Q ≃ᵍ R) : P ≃ᵍ R where
  equivA := e₁.equivA.trans e₂.equivA
  equivB a := (e₁.equivB a).trans (e₂.equivB (e₁.equivA a))
  grade_eq a := (e₁.grade_eq a).trans (e₂.grade_eq (e₁.equivA a))

end Equiv

/-! ## Induced indexed equivalence -/

/-- The indexed structural equivalence induced on the `toIPFunctor` images: the source-index
preservation law follows from grade preservation by left multiplication with the accumulated
grade. -/
def Equiv.toIPEquiv [Mul G] {P : GPFunctor.{uG, uA₁, uB₁} G}
    {Q : GPFunctor.{uG, uA₂, uB₂} G} (e : P ≃ᵍ Q) :
    IPFunctor.Equiv P.toIPFunctor Q.toIPFunctor where
  equivA _ := e.equivA
  equivB _ a := e.equivB a
  src_eq g a _ := congrArg (g * ·) (e.grade_eq a)

end GPFunctor
