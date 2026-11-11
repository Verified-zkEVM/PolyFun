/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Handler.CountMat

/-!
# Examples for handlers certified by count matrices

Regression tests: a one-shape Diller–Nahm morphism built from a matrix has that matrix as its
count matrix, co-Kleisli composition multiplies count matrices at a concrete matrix, and the
certified handler of a composite is the composite of the certified handlers.
-/

@[expose] public section

namespace PFunctor.CountMatTest

open PFunctor

/-- The one-shape morphism on `Bool` in which each direction demands `true` twice. -/
def twiceTrue : Lens (bang (y^Bool : PFunctor.{0, 0})) (y^Bool : PFunctor.{0, 0}) :=
  Lens.ofCountMat fun _ j => if j then 2 else 0

/-- Its count matrix has `2` at `(false, true)`. -/
example : twiceTrue.countMat PUnit.unit false true = 2 := by
  simp [twiceTrue]

/-- The co-Kleisli square has `4` at `(false, true)`: the product of count matrices. -/
example : (Lens.bangComp twiceTrue twiceTrue).countMat PUnit.unit false true = 4 := by
  rw [Lens.countMat_bangComp]
  decide

/-- The demand of a composite certified handler is the product of the demand matrices. -/
example {P Q R : PFunctor.{0, 0}} {c : P.A → Bool → ℕ} {e : Q.A → Bool → ℕ}
    {f : R.A → Bool → ℕ} (D₂ : Handler.CountCertified Q R e f)
    (D₁ : Handler.CountCertified P Q c e) :
    Matrix.of ((D₂.comp D₁).lens.demand ℕ) =
      Matrix.of (D₁.lens.demand ℕ) * Matrix.of (D₂.lens.demand ℕ) :=
  Lens.demand_bangComp_eq_mul _ _

/-- The composite of certified handlers is certified with the composite exchange. -/
example {P Q R : PFunctor.{0, 0}} {c : P.A → Bool → ℕ} {e : Q.A → Bool → ℕ}
    {f : R.A → Bool → ℕ} (D₂ : Handler.CountCertified Q R e f)
    (D₁ : Handler.CountCertified P Q c e) :
    (D₂.comp D₁).toCertified = D₂.toCertified.comp D₁.toCertified :=
  Handler.CountCertified.toCertified_comp D₂ D₁

end PFunctor.CountMatTest
