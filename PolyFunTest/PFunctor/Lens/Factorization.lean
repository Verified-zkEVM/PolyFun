/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Factorization

/-!
# Examples for the vertical–cartesian factorization

Regression tests: every lens factors as vertical-then-cartesian recovering the
original, the two legs land in their classes, and a concrete cartesian lens
(`inl`) is verified vertical exactly when its position map is a bijection.
-/

@[expose] public section

universe u

namespace PFunctor

variable {P Q : PFunctor.{u, u}}

/-- The factorization recovers the original lens. -/
example (l : Lens P Q) : Lens.factorCart l ∘ₗ Lens.factorVert l = l :=
  Lens.factorCart_comp_factorVert l

/-- The vertical leg is vertical. -/
example (l : Lens P Q) : (Lens.factorVert l).IsVertical := Lens.isVertical_factorVert l

/-- The cartesian leg is cartesian. -/
example (l : Lens P Q) : (Lens.factorCart l).IsCartesian := Lens.isCartesian_factorCart l

/-- `IsVertical` is closed under composition and holds of the identity. -/
example (l₁ l₂ : Lens P P) (h₁ : l₁.IsVertical) (h₂ : l₂.IsVertical) :
    (l₁ ∘ₗ l₂).IsVertical := h₁.comp h₂

example : (Lens.id P).IsVertical := Lens.IsVertical.id P

/-- `inl : P ⇆ P + Q` is cartesian but not vertical (its position map `Sum.inl`
is injective but not surjective when `Q` has positions). -/
example : (Lens.inl : Lens P (P + Q)).IsCartesian := Lens.IsCartesian.inl

end PFunctor
