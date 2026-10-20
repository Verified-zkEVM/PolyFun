/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Equiv.Basic

/-!
# The normal form and special classes of polynomials

Every polynomial is the sum, over its positions, of the representables at its directions:
`Equiv.sigmaPurePower P : (Σₚ a, y^(P.B a)) ≃ₚ P` (Niu–Spivak Def 2.1, p. 25). Both of its
component equivalences are definitional.

Niu–Spivak §2.2 (pp. 28–29) singles out four classes of polynomials, each defined up to
isomorphism:

* `IsPurePower P`: `P ≃ₚ y^A` for some `A`. The book calls these *representable*; the covariant
  functor `Hom(A, −)` is *corepresentable* in Mathlib's terminology (`Functor.IsCorepresentable`);
* `IsConstant P`: `P ≃ₚ C I` for some `I`;
* `IsLinear P`: `P ≃ₚ linear I` for some `I` (Def 2.14);
* `IsMonomial P`: `P ≃ₚ I y^ A` for some `I` and `A` (Def 2.15).

Each class has a characterization by positions and directions (Exs 2.13, 2.17):
representables have a unique position, constants have no directions, linear polynomials have
a unique direction at every position, and monomials have pairwise equivalent direction sets.
The first three classes are monomials (Example 2.16).
-/

@[expose] public section

universe uA uB

namespace PFunctor

/-! ## The normal form -/

namespace Equiv

/-- Every polynomial is the sum of the representables at its directions,
`P ≅ Σ_{a ∈ P(1)} y^{P[a]}` (Niu–Spivak Def 2.1). -/
def sigmaPurePower (P : PFunctor.{uA, uB}) :
    sigma (fun a : P.A => (y^(P.B a) : PFunctor.{uA, uB})) ≃ₚ P where
  equivA :=
    { toFun := sigma.fst
      invFun a := sigma.mk a PUnit.unit
      left_inv _ := rfl
      right_inv _ := rfl }
  equivB _ := _root_.Equiv.refl _

end Equiv

/-! ## Special classes -/

variable {P : PFunctor.{uA, uB}}

/-- `P` is a **pure power** if it is isomorphic to `y^A` for some `A`: a representable polynomial in
the sense of Niu–Spivak §2.2, whose action is the corepresentable functor `Hom(A, −)`. -/
def IsPurePower (P : PFunctor.{uA, uB}) : Prop :=
  ∃ A : Type uB, Nonempty (P ≃ₚ (y^A : PFunctor.{uA, uB}))
@[deprecated (since := "2026-10-19")] alias IsRepresentable := IsPurePower

/-- `P` is **constant** if it is isomorphic to the constant polynomial `C I` for some `I`
(Niu–Spivak §2.2). -/
def IsConstant (P : PFunctor.{uA, uB}) : Prop :=
  ∃ I : Type uA, Nonempty (P ≃ₚ (C I : PFunctor.{uA, uB}))

/-- `P` is **linear** if it is isomorphic to `linear I = I y` for some `I` (Niu–Spivak
Def 2.14). -/
def IsLinear (P : PFunctor.{uA, uB}) : Prop :=
  ∃ I : Type uA, Nonempty (P ≃ₚ (linear I : PFunctor.{uA, uB}))

/-- `P` is a **monomial** if it is isomorphic to `I y^ A` for some `I` and `A` (Niu–Spivak
Def 2.15). -/
def IsMonomial (P : PFunctor.{uA, uB}) : Prop :=
  ∃ (I : Type uA) (A : Type uB), Nonempty (P ≃ₚ (I y^ A : PFunctor.{uA, uB}))

theorem isPurePower_purePower (A : Type uB) :
    IsPurePower (y^A : PFunctor.{uA, uB}) :=
  ⟨A, ⟨Equiv.refl _⟩⟩
@[deprecated (since := "2026-10-19")] alias isRepresentable_purePower := isPurePower_purePower

theorem isConstant_C (I : Type uA) : IsConstant (C I : PFunctor.{uA, uB}) :=
  ⟨I, ⟨Equiv.refl _⟩⟩

theorem isLinear_linear (I : Type uA) : IsLinear (linear I : PFunctor.{uA, uB}) :=
  ⟨I, ⟨Equiv.refl _⟩⟩

theorem isMonomial_monomial (I : Type uA) (A : Type uB) :
    IsMonomial (I y^ A : PFunctor.{uA, uB}) :=
  ⟨I, A, ⟨Equiv.refl _⟩⟩

/-- A polynomial is a pure power exactly when it has a unique position (Niu–Spivak
Ex 2.13). -/
theorem isPurePower_iff : IsPurePower P ↔ Nonempty (Unique P.A) := by
  constructor
  · rintro ⟨A, ⟨e⟩⟩
    exact ⟨e.equivA.unique⟩
  · rintro ⟨h⟩
    exact ⟨P.B default, ⟨
      { equivA := _root_.Equiv.equivPUnit P.A
        equivB := fun a => _root_.Equiv.cast (congrArg P.B (Subsingleton.elim a default)) }⟩⟩
@[deprecated (since := "2026-10-19")] alias isRepresentable_iff := isPurePower_iff

/-- A polynomial is constant exactly when none of its positions has a direction (Niu–Spivak
Ex 2.13). -/
theorem isConstant_iff : IsConstant P ↔ ∀ a, IsEmpty (P.B a) := by
  constructor
  · rintro ⟨I, ⟨e⟩⟩ a
    exact (e.equivB a).isEmpty
  · intro h
    exact ⟨P.A, ⟨
      { equivA := _root_.Equiv.refl _
        equivB := fun a => @_root_.Equiv.equivPEmpty _ (h a) }⟩⟩

/-- A polynomial is linear exactly when every position has a unique direction (Niu–Spivak
Ex 2.17). -/
theorem isLinear_iff : IsLinear P ↔ ∀ a, Nonempty (Unique (P.B a)) := by
  constructor
  · rintro ⟨I, ⟨e⟩⟩ a
    exact ⟨(e.equivB a).unique⟩
  · intro h
    exact ⟨P.A, ⟨
      { equivA := _root_.Equiv.refl _
        equivB := fun a => @_root_.Equiv.equivPUnit _ (h a).some }⟩⟩

/-- A polynomial is a monomial exactly when its direction sets are all equivalent to a single
set (Niu–Spivak Ex 2.17). -/
theorem isMonomial_iff : IsMonomial P ↔ ∃ A : Type uB, ∀ a, Nonempty (P.B a ≃ A) := by
  constructor
  · rintro ⟨I, A, ⟨e⟩⟩
    exact ⟨A, fun a => ⟨e.equivB a⟩⟩
  · rintro ⟨A, h⟩
    exact ⟨P.A, A, ⟨
      { equivA := _root_.Equiv.refl _
        equivB := fun a => (h a).some }⟩⟩

/-- Constant polynomials are monomials with empty exponent (Niu–Spivak Example 2.16). -/
theorem IsConstant.isMonomial (h : IsConstant P) : IsMonomial P :=
  isMonomial_iff.mpr ⟨PEmpty, fun a =>
    ⟨@_root_.Equiv.equivPEmpty _ (isConstant_iff.mp h a)⟩⟩

/-- Linear polynomials are monomials with singleton exponent (Niu–Spivak Example 2.16). -/
theorem IsLinear.isMonomial (h : IsLinear P) : IsMonomial P :=
  isMonomial_iff.mpr ⟨PUnit, fun a =>
    ⟨@_root_.Equiv.equivPUnit _ (isLinear_iff.mp h a).some⟩⟩

/-- Pure powers are monomials with a single position (Niu–Spivak
Example 2.16). -/
theorem IsPurePower.isMonomial (h : IsPurePower P) : IsMonomial P := by
  obtain ⟨u⟩ := isPurePower_iff.mp h
  exact isMonomial_iff.mpr ⟨P.B default, fun a =>
    ⟨_root_.Equiv.cast (congrArg P.B (Subsingleton.elim a default))⟩⟩
@[deprecated (since := "2026-10-19")] alias IsRepresentable.isMonomial := IsPurePower.isMonomial

end PFunctor
