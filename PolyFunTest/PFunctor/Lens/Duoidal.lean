/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Duoidal

/-!
# Examples for the duoidal structure relating `⊗` and `◃`

Regression tests: the ordering lens is cartesian on concrete polynomials, the
`⊗`/`◃` catalogue isomorphisms specialize to concrete small polynomials, and
the duoidal interchange lens `duoidalLens` typechecks both generically and on
concrete polynomials.
-/

@[expose] public section

universe u pA₁ pB₁ pA₂ pB₂ qA₁ qB₁ qA₂ qB₂
  rA₁ rB₁ rA₂ rB₂ sA₁ sB₁ sA₂ sB₂

namespace PFunctor

/-- The ordering lens `p ⊗ q → p ◃ q` is cartesian on concrete polynomials. -/
example : (Lens.orderingLens (linear.{0, 0} Bool) (linear.{0, 0} (Fin 3))).IsCartesian :=
  Lens.orderingLens_isCartesian _ _

/-- The `Ay ⊗ By ≅ Ay ◃ By` catalogue isomorphism on concrete small polynomials. -/
example : (linear.{0, 0} Bool ⊗ linear.{0, 0} (Fin 3)) ≃ₗ
    (linear.{0, 0} Bool ◃ linear.{0, 0} (Fin 3)) :=
  Lens.Equiv.linearTensorLinear Bool (Fin 3)

/-- The `y^A ⊗ y^B ≅ y^A ◃ y^B` catalogue isomorphism on concrete small polynomials. -/
example : (purePower.{0, 0} Bool ⊗ purePower.{0, 0} (Fin 3)) ≃ₗ
    (purePower.{0, 0} Bool ◃ purePower.{0, 0} (Fin 3)) :=
  Lens.Equiv.purePowerTensorPurePower Bool (Fin 3)

/-- The `By ⊗ p ≅ By ◃ p` catalogue isomorphism (linear factor on the left). -/
example : (linear.{0, 0} Bool ⊗ purePower.{0, 0} (Fin 3)) ≃ₗ
    (linear.{0, 0} Bool ◃ purePower.{0, 0} (Fin 3)) :=
  Lens.Equiv.linearTensor Bool (purePower (Fin 3))

/-- The `p ⊗ y^A ≅ p ◃ y^A` catalogue isomorphism (pure-power factor on the right). -/
example : (linear.{0, 0} Bool ⊗ purePower.{0, 0} (Fin 3)) ≃ₗ
    (linear.{0, 0} Bool ◃ purePower.{0, 0} (Fin 3)) :=
  Lens.Equiv.tensorPurePower (linear Bool) (Fin 3)

/-- The duoidal interchange lens typechecks with its stated signature, generically. -/
example (p p' q q' : PFunctor.{u, u}) :
    Lens ((p ◃ p') ⊗ (q ◃ q')) ((p ⊗ q) ◃ (p' ⊗ q')) :=
  Lens.duoidalLens p p' q q'

/-- Ordering is natural in both arguments. -/
example {p p' q q' : PFunctor.{u, u}} (f : Lens p p') (g : Lens q q') :
    Lens.orderingLens p' q' ∘ₗ (f ⊗ₗ g) =
      (f ◃ₗ g) ∘ₗ Lens.orderingLens p q :=
  Lens.orderingLens_natural f g

/-- Interchange is natural in all four arguments. -/
example {p₁ p₂ q₁ q₂ r₁ r₂ s₁ s₂ : PFunctor.{u, u}}
    (f₁ : Lens p₁ r₁) (f₂ : Lens p₂ r₂)
    (g₁ : Lens q₁ s₁) (g₂ : Lens q₂ s₂) :
    Lens.duoidalLens r₁ r₂ s₁ s₂ ∘ₗ ((f₁ ◃ₗ f₂) ⊗ₗ (g₁ ◃ₗ g₂)) =
      ((f₁ ⊗ₗ g₁) ◃ₗ (f₂ ⊗ₗ g₂)) ∘ₗ Lens.duoidalLens p₁ p₂ q₁ q₂ :=
  Lens.duoidalLens_natural f₁ f₂ g₁ g₂

/-- Naturality does not identify the universe pairs of any source or target
interface. -/
example {p₁ : PFunctor.{pA₁, pB₁}} {p₂ : PFunctor.{pA₂, pB₂}}
    {q₁ : PFunctor.{qA₁, qB₁}} {q₂ : PFunctor.{qA₂, qB₂}}
    {r₁ : PFunctor.{rA₁, rB₁}} {r₂ : PFunctor.{rA₂, rB₂}}
    {s₁ : PFunctor.{sA₁, sB₁}} {s₂ : PFunctor.{sA₂, sB₂}}
    (f₁ : Lens p₁ r₁) (f₂ : Lens p₂ r₂)
    (g₁ : Lens q₁ s₁) (g₂ : Lens q₂ s₂) :
    Lens.duoidalLens r₁ r₂ s₁ s₂ ∘ₗ ((f₁ ◃ₗ f₂) ⊗ₗ (g₁ ◃ₗ g₂)) =
      ((f₁ ⊗ₗ g₁) ◃ₗ (f₂ ⊗ₗ g₂)) ∘ₗ Lens.duoidalLens p₁ p₂ q₁ q₂ :=
  Lens.duoidalLens_natural f₁ f₂ g₁ g₂

/-- Interchange is cartesian. -/
example (p p' q q' : PFunctor.{u, u}) :
    (Lens.duoidalLens p p' q q').IsCartesian :=
  Lens.duoidalLens_isCartesian p p' q q'

/-- The concrete middle-four equation is the binary lax-monoidal law. -/
example (p p' q q' : PFunctor.{u, u}) :
    Lens.duoidalLens p p' q q' ∘ₗ
        (Lens.orderingLens p p' ⊗ₗ Lens.orderingLens q q') =
      Lens.orderingLens (p ⊗ q) (p' ⊗ q') ∘ₗ
        (Lens.Equiv.tensorMiddleFour p p' q q').toLens :=
  Lens.orderingLens_duoidal p p' q q'

/-- Ordering agrees with both tensor/composition unitors. -/
example (p : PFunctor.{u, u}) :
    Lens.Equiv.compX.toLens ∘ₗ Lens.orderingLens p X = Lens.Equiv.tensorX.toLens :=
  Lens.orderingLens_unit_right p

example (p : PFunctor.{u, u}) :
    Lens.Equiv.XComp.toLens ∘ₗ Lens.orderingLens X p = Lens.Equiv.xTensor.toLens :=
  Lens.orderingLens_unit_left p

/-- The duoidal interchange lens typechecks on concrete small polynomials. -/
example :
    Lens ((linear.{0, 0} Bool ◃ linear.{0, 0} (Fin 2)) ⊗
          (linear.{0, 0} (Fin 3) ◃ linear.{0, 0} (Fin 4)))
      ((linear.{0, 0} Bool ⊗ linear.{0, 0} (Fin 3)) ◃
        (linear.{0, 0} (Fin 2) ⊗ linear.{0, 0} (Fin 4))) :=
  Lens.duoidalLens (linear Bool) (linear (Fin 2)) (linear (Fin 3)) (linear (Fin 4))

end PFunctor
