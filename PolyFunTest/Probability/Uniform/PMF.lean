/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Probability.UniformOn.PMF

/-!
# Uniform measures and probability mass functions

Regression tests for the bridge between `ProbabilityTheory.uniformOn` and Mathlib's `PMF`. A fair
coin written as a mass function is the uniform measure on `Bool`. The mass function of the uniform
measure on a finite set has the expected masses, and the uniform measure is recovered from its mass
function.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolyFunTest.Probability.Uniform.PMF

/-- A fair coin as a probability mass function. -/
noncomputable def fairCoin : _root_.PMF Bool :=
  ⟨fun _ ↦ 2⁻¹, by
    convert hasSum_fintype (fun _ : Bool ↦ (2⁻¹ : ℝ≥0∞))
    simpa using (ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top).symm⟩

/-- The fair coin is the uniform measure on `Bool`. -/
example : fairCoin.toMeasure = uniformOn Set.univ :=
  (fairCoin.toMeasure_eq_uniformOn_univ_iff).mpr fun _ ↦ rfl

/-- The mass function of the uniform measure on a finite set. -/
example :
    haveI := isProbabilityMeasure_uniformOn (Finset.finite_toSet ({0, 1} : Finset (Fin 4)))
      ⟨0, by simp⟩
    (uniformOn (({0, 1} : Finset (Fin 4)) : Set (Fin 4))).toPMF 1 = 2⁻¹ := by
  rw [Measure.toPMF_uniformOn_apply]
  rfl

example (a : Fin 6) : (uniformOn Set.univ : Measure (Fin 6)).toPMF a = 6⁻¹ := by
  rw [Measure.toPMF_uniformOn_univ_apply, Fintype.card_fin]
  rfl

/-- The uniform measure is recovered from its mass function, which is uniform. -/
example : (uniformOn Set.univ : Measure (Fin 6)).toPMF.toMeasure = uniformOn Set.univ :=
  Measure.toPMF_toMeasure _

example (p : _root_.PMF (Fin 6)) (h : p.toMeasure = uniformOn Set.univ) (a : Fin 6) :
    p a = 6⁻¹ := by
  rw [(p.toMeasure_eq_uniformOn_univ_iff).mp h a, Fintype.card_fin]
  rfl

end PolyFunTest.Probability.Uniform.PMF
