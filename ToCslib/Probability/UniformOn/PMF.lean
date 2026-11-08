/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import ToCslib.Probability.UniformOn

/-!
# Uniform measures and probability mass functions

PolyFun's measure modules state uniform sampling with the measure `ProbabilityTheory.uniformOn`.
This bridge relates it to Mathlib's probability mass functions in both directions. A mass function
is the uniform measure on a finite set exactly when it gives each point of the set mass `1 / #s`
(`PMF.toMeasure_eq_uniformOn_iff`), and the mass function of the uniform measure has these masses
(`MeasureTheory.Measure.toPMF_uniformOn_apply`).

Mathlib provides no uniform mass functions to compare with: `PMF.uniformOfFinset` and
`PMF.uniformOfFintype` are deprecated aliases of the measure
`MeasureTheory.Measure.uniformOfFinset`. The bridge imports only
`Mathlib.Probability.ProbabilityMassFunction.Basic`, which defines `PMF`, `PMF.toMeasure` and
`MeasureTheory.Measure.toPMF`, and leaves out the lawful monad instance on `PMF`.
-/

@[expose] public section

-- upstream candidate: Mathlib has no `Probability/UniformOn/` directory, so this bridge
-- needs a Mathlib path of its own.

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

namespace PMF

/-- A probability mass function is the uniform measure on a finite set exactly when it gives each
point of the set mass `1 / #s` and every other point mass zero. -/
theorem toMeasure_eq_uniformOn_iff [DecidableEq α] (p : PMF α) (s : Finset α) :
    p.toMeasure = uniformOn (s : Set α) ↔
      ∀ a, p a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  refine ⟨fun h a ↦ ?_, fun h ↦ ?_⟩
  · rw [← p.toMeasure_apply_singleton a (measurableSet_singleton a), h,
      uniformOn_finset_apply_singleton]
  · classical
    ext t ht
    have hst : (s : Set α) ∩ t = ↑(s.filter (· ∈ t)) := by ext; simp
    have hp : t.indicator p = (↑(s.filter (· ∈ t)) : Set α).indicator
        fun _ ↦ (s.card : ℝ≥0∞)⁻¹ := by
      ext x
      by_cases hxt : x ∈ t <;> simp [hxt, h x, Set.indicator_apply]
    rw [p.toMeasure_apply ht, hp, ← tsum_subtype,
      Finset.tsum_subtype' _ fun _ ↦ (s.card : ℝ≥0∞)⁻¹, Finset.sum_const,
      nsmul_eq_mul, ← uniformOn_inter_self s.finite_toSet, hst, uniformOn_apply_finset,
      Finset.inter_filter, Finset.inter_self, div_eq_mul_inv]

/-- A probability mass function on a finite type is the uniform measure on the whole space exactly
when it gives every point mass `1 / |α|`. -/
theorem toMeasure_eq_uniformOn_univ_iff [Fintype α] (p : PMF α) :
    p.toMeasure = uniformOn (Set.univ : Set α) ↔ ∀ a, p a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  simpa only [Finset.coe_univ, Finset.mem_univ, ite_true, Finset.card_univ] using
    p.toMeasure_eq_uniformOn_iff Finset.univ

end PMF

namespace MeasureTheory.Measure

/-- The mass function of the uniform measure on a finite set gives each point of the set mass
`1 / #s` and every other point mass zero. -/
theorem toPMF_uniformOn_apply [Countable α] [DecidableEq α] (s : Finset α)
    [IsProbabilityMeasure (uniformOn (s : Set α))] (a : α) :
    (uniformOn (s : Set α)).toPMF a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 :=
  uniformOn_finset_apply_singleton s a

/-- The mass function of the uniform measure on a finite nonempty type gives every point mass
`1 / |α|`. -/
theorem toPMF_uniformOn_univ_apply [Fintype α] [Nonempty α] (a : α) :
    (uniformOn (Set.univ : Set α)).toPMF a = (Fintype.card α : ℝ≥0∞)⁻¹ :=
  uniformOn_univ_apply_singleton a

end MeasureTheory.Measure
