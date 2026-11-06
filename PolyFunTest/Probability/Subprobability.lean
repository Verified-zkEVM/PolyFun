/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunProbability.ToMathlib.Probability.Kernel.Subprobability

/-!
# Subprobability measures and kernels

Regression tests for the staged subprobability classes: the instances that let a failing
computation's measure and kernel interpretations keep total mass at most one.
-/

open MeasureTheory ProbabilityTheory

namespace PolyFunTest.Probability

/-- A Dirac mass, and every probability measure, is a subprobability measure. -/
example : IsSubprobabilityMeasure (Measure.dirac true) := inferInstance

example (μ : Measure Bool) [IsProbabilityMeasure μ] : IsSubprobabilityMeasure μ := inferInstance

/-- Scaling a probability measure by one half leaves half its mass missing. -/
example : (((1 / 2 : ENNReal) • Measure.dirac true) : Measure Bool) Set.univ ≤ 1 := by
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  norm_num

/-- Composing subprobability kernels gives a subprobability kernel. -/
example (κ : Kernel Bool Bool) (η : Kernel Bool Bool) [IsSubprobabilityKernel κ]
    [IsSubprobabilityKernel η] : IsSubprobabilityKernel (η ∘ₖ κ) := inferInstance

/-- Every fibre of a subprobability kernel has mass at most one. -/
example (κ : Kernel Bool Bool) [IsSubprobabilityKernel κ] (b : Bool) : κ b Set.univ ≤ 1 :=
  κ.measure_univ_le b

end PolyFunTest.Probability
