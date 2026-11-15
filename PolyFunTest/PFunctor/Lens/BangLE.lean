/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Lens.BangLE

/-!
# Examples for the graded exponential and count matrices

Regression tests: the graded comonad and comonoid laws specialize to a concrete polynomial, the
graded exponential includes into the exponential, a lens of the Diller–Nahm category that demands
each direction twice has grade `2` and count matrix `2` on the diagonal, and grades and count
matrices compose.
-/

@[expose] public section

namespace PFunctor.BangLETest

open PFunctor

/-- The concrete polynomial `y^Bool`. -/
abbrev P₀ : PFunctor.{0, 0} := purePower Bool

/-- The lens out of the exponential that demands each direction twice. -/
noncomputable def twice : Lens (bang P₀) P₀ := id ⇆ fun _ b => {b, b}

/-- The counit law at a concrete polynomial. -/
example : Lens.bangLECounit (bangLE 3 P₀) ∘ₗ Lens.bangLEComult 1 3 P₀ =
    Lens.bangLESub (one_mul 3).ge P₀ :=
  Lens.bangLECounit_comult 3 P₀

/-- Coassociativity at concrete grades. -/
example : Lens.bangLEComult 2 3 (bangLE 4 P₀) ∘ₗ Lens.bangLEComult (2 * 3) 4 P₀ =
    Lens.bangLEMap 2 (Lens.bangLEComult 3 4 P₀) ∘ₗ Lens.bangLEComult 2 (3 * 4) P₀ ∘ₗ
      Lens.bangLESub (mul_assoc 2 3 4).ge P₀ :=
  Lens.bangLEComult_coassoc 2 3 4 P₀

/-- Contraction is cocommutative at concrete grades. -/
example : (Lens.Equiv.tensorComm (bangLE 1 P₀) (bangLE 2 P₀)).toLens ∘ₗ
      Lens.bangLEContr 1 2 P₀ = Lens.bangLEContr 2 1 P₀ ∘ₗ Lens.bangLESub (add_comm 2 1).le P₀ :=
  Lens.bangLEContr_comm 1 2 P₀

/-- The graded comultiplication is the comultiplication of the exponential. -/
example : Lens.bangLEComult 2 2 P₀ ∘ₗ Lens.bangLEIncl (2 * 2) P₀ =
    Lens.bangLEMap 2 (Lens.bangLEIncl 2 P₀) ∘ₗ Lens.bangLEIncl 2 (bang P₀) ∘ₗ
      Lens.bangComult P₀ :=
  Lens.bangLEComult_incl 2 2 P₀

/-- The lens that demands each direction twice has grade `2`. -/
example : twice.IsGraded fun _ => 2 := fun _ b => by
  change (((({b, b} : Multiset Bool)).card : ℕ∞) ≤ 2)
  simp

/-- Its count matrix has `2` on the diagonal. -/
example : twice.countMat PUnit.unit true true = 2 := by decide

/-- Its count matrix has `0` off the diagonal. -/
example : twice.countMat PUnit.unit true false = 0 := by decide

/-- The count matrix of its composite with itself is the square of its count matrix. -/
example : (Lens.bangComp twice twice).countMat PUnit.unit =
    twice.countMat PUnit.unit * twice.countMat PUnit.unit :=
  Lens.countMat_bangComp twice twice PUnit.unit

/-- The count matrix of the counit is the identity matrix. -/
example : (Lens.bangCounit P₀).countMat PUnit.unit = 1 :=
  Lens.countMat_bangCounit (P := P₀) PUnit.unit

end PFunctor.BangLETest
