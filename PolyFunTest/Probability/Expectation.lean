/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunProbability.PFunctor.Free.Expectation

/-!
# The expectation algebra on the real carrier

Regression tests for the expectation algebra of free programs over `ℝ≥0∞`, the carrier that the
generic program-logic tests otherwise model with `ℕ∞` on a deterministic monad.
-/

public section

open MeasureTheory PFunctor PFunctor.FreeM
open scoped ENNReal

namespace PolyFunTest.Probability.Expectation

/-- One operation whose answer is a bit. -/
@[expose, reducible] def Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A coin that always answers `true`. -/
@[expose, reducible]
noncomputable def alwaysTrue : (a : Coin.A) → Measure (Coin.B a) := fun _ => Measure.dirac true

/-- The expectation of a postcondition after one flip of a coin that always answers `true` is the
postcondition at `true`. -/
example (post : Bool → ℝ≥0∞) :
    (expectationAlgebra alwaysTrue).μ (FreeM.lift (P := Coin) () >>= fun b => pure (post b)) =
      post true := by
  rw [expectationAlgebra_μ_bind_pure alwaysTrue _ (Measurable.of_discrete),
    measureFold_lift (P := Coin)]
  exact lintegral_dirac true post

/-- Under subprobability answers, the expectation of the constant `1` is at most `1`, so the
algebra restricts to the probability carrier. -/
example (program : FreeM Coin Bool) :
    (expectationAlgebra alwaysTrue).μ (program >>= fun _ => pure 1) ≤ 1 :=
  expectationAlgebra_μ_bind_const_le_one alwaysTrue program

noncomputable example : MAlgOrdered (FreeM Coin) (Set.Iic (1 : ℝ≥0∞)) :=
  probabilityAlgebra alwaysTrue

end PolyFunTest.Probability.Expectation
