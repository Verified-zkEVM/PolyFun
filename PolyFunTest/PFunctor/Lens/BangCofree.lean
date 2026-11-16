/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Lens.BangCofree

/-!
# Examples for the cofree commutative comonoid `bang P`

Regression tests for `PFunctor/Lens/BangCofree.lean`: the monoids of the comonoid `bang P`, the
universal property, and the induced lenses of the counit and of the exponential of a lens.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.BangCofree

open CategoryTheory _root_.PFunctor _root_.PFunctor.TensorCat

universe u v

variable {P R : PFunctor.{u, v}}

/-- The monoid of the comonoid `bang P` at a position is multiset addition. -/
example (a : P.A) (m₁ m₂ : Multiset (P.B a)) : comonAdd (Q := bang P) a m₁ m₂ = m₁ + m₂ :=
  rfl

/-- The unit of the comonoid `bang P` at a position is the empty multiset. -/
example (a : P.A) : comonZero (Q := bang P) a = 0 :=
  rfl

/-- A lens out of `bang R` factors uniquely through the counit of `bang P`. -/
example (f : Lens (bang R) P) :
    ∃! g : Lens (bang R) (bang P),
      IsComonHom (M := TensorCat.of (bang R)) (N := TensorCat.of (bang P)) g ∧
        Lens.bangCounit P ∘ₗ g = f :=
  bang_cofree f

/-- The lens induced by the counit of `bang P` is the identity. -/
example : bangLift (Lens.bangCounit P) = Lens.id (bang P) :=
  (@eq_bangLift P (bang P) _ _ (Lens.bangCounit P) (Lens.id (bang P))
    (inferInstanceAs (IsComonHom (𝟙 (TensorCat.of (bang P))))) rfl).symm

/-- The induced lens of the exponential of a lens is the exponential of that lens. -/
example (l : Lens R P) : bangLift (l ∘ₗ Lens.bangCounit R) = Lens.bangMap l :=
  (eq_bangLift _ _ (h := Lens.bangCounit_natural l)).symm

end PolyFunTest.PFunctor.BangCofree
