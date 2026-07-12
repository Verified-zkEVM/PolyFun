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

universe u

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

/-- The duoidal interchange lens typechecks on concrete small polynomials. -/
example :
    Lens ((linear.{0, 0} Bool ◃ linear.{0, 0} (Fin 2)) ⊗
          (linear.{0, 0} (Fin 3) ◃ linear.{0, 0} (Fin 4)))
      ((linear.{0, 0} Bool ⊗ linear.{0, 0} (Fin 3)) ◃
        (linear.{0, 0} (Fin 2) ⊗ linear.{0, 0} (Fin 4))) :=
  Lens.duoidalLens (linear Bool) (linear (Fin 2)) (linear (Fin 3)) (linear (Fin 4))

end PFunctor
