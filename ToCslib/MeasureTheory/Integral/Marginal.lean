/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.MeasureTheory.Integral.Marginal

/-!
# Guessing one coordinate of a product measure

Under a finite product of probability measures, a function that ignores coordinate `i` takes the
value of coordinate `i` with probability at most the largest mass that the law of coordinate `i`
gives a single point. The proof integrates out coordinate `i` first (`lmarginal_singleton`).
-/

public section

-- upstream candidate

namespace MeasureTheory.Measure

open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ j, MeasurableSpace (X j)]

/-- A measurable function that ignores coordinate `i` takes the value of that coordinate with
probability at most `p`, when the law of coordinate `i` gives each point mass at most `p`. -/
theorem pi_setOf_eq_apply_le (μ : ∀ j, Measure (X j)) [∀ j, IsProbabilityMeasure (μ j)] {i : ι}
    [MeasurableEq (X i)] {f : (∀ j, X j) → X i} (hf : Measurable f)
    (hfi : ∀ x y, f (Function.update x i y) = f x) {p : ℝ≥0∞} (hp : ∀ y, μ i {y} ≤ p) :
    Measure.pi μ {x | f x = x i} ≤ p := by
  have hE : MeasurableSet {x | f x = x i} := measurableSet_eq_fun hf (measurable_pi_apply i)
  rw [← lintegral_indicator_one hE]
  calc ∫⁻ x, {x | f x = x i}.indicator 1 x ∂Measure.pi μ
      ≤ ∫⁻ _, p ∂Measure.pi μ := by
        refine lintegral_le_of_lmarginal_le {i} (measurable_one.indicator hE) measurable_const ?_
        rw [lmarginal_singleton, lmarginal_singleton]
        intro x
        have hx (y : X i) : {x | f x = x i}.indicator (1 : (∀ j, X j) → ℝ≥0∞)
            (Function.update x i y) = ({f x} : Set (X i)).indicator 1 y := by
          by_cases h : f x = y
          · rw [Set.indicator_of_mem (by simp [hfi, h]),
              Set.indicator_of_mem (Set.mem_singleton_iff.2 h.symm)]
            rfl
          · rw [Set.indicator_of_notMem (by simpa [hfi] using h),
              Set.indicator_of_notMem (mt Set.mem_singleton_iff.1 (Ne.symm h))]
        simp only [hx, lintegral_indicator_one (measurableSet_singleton _), lintegral_const,
          measure_univ, mul_one]
        exact hp (f x)
    _ = p := by simp

end MeasureTheory.Measure
