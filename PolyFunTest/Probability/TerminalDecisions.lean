/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Multiparty.Measure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic.NormNum

/-!
# A noisy terminal bit

An exact report can simulate the noisy sensor after a program has finished. Even a randomized
decoder cannot recover both possible input bits from this sensor with probability one.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor Interaction.Multiparty
open scoped ENNReal

namespace PolyFunTest.TerminalDecisions

private noncomputable def accuracy : unitInterval := ⟨3 / 4, by constructor <;> norm_num⟩

/-- Report the input bit with probability three quarters. -/
noncomputable def sensor : Kernel Bool Bool where
  toFun b := bernoulliMeasure b (!b) accuracy
  measurable' := Measurable.of_discrete

instance : IsMarkovKernel sensor := ⟨fun b => inferInstanceAs
  (IsProbabilityMeasure (bernoulliMeasure b (!b) accuracy))⟩

/-- Two successive bit queries return the second reply. -/
private def twice : FreeM (monomial Unit Bool) Bool := do
  let _ ← FreeM.lift ()
  FreeM.lift ()

/-- This client changes reports without unfolding either call. -/
example (impl : KernelHandler (monomial Unit Bool) Unit) (d : Kernel Bool Bool) :
    let exactReport := Kernel.deterministic (Prod.fst : Bool × Unit → Bool) measurable_fst
    d ∘ₖ ((sensor ∘ₖ exactReport) ∘ₖ FreeM.runKernel impl twice) =
      (d ∘ₖ sensor) ∘ₖ (exactReport ∘ₖ FreeM.runKernel impl twice) :=
  FreeM.comp_runKernel_of_factor sensor rfl d impl twice

/-- A deterministic refinement also transports a decision for the same program. -/
example {coarse fine : Observation (Bool × Unit)} [MeasurableSpace coarse.1]
    [MeasurableSpace fine.1] [DiscreteMeasurableSpace fine.1]
    (h : coarse.Refines fine) (d : Kernel coarse.1 Bool) :
    ∃ f : fine.1 → coarse.1, ∀ impl : KernelHandler (monomial Unit Bool) Unit,
      d ∘ₖ (Kernel.deterministic coarse.2 Measurable.of_discrete ∘ₖ FreeM.runKernel impl twice) =
        (d ∘ₖ Kernel.deterministic f Measurable.of_discrete) ∘ₖ
          (Kernel.deterministic fine.2 Measurable.of_discrete ∘ₖ FreeM.runKernel impl twice) := by
  obtain ⟨f, hf⟩ := h.exists_comp_runKernel Measurable.of_discrete Measurable.of_discrete
  exact ⟨f, fun impl => hf d impl twice⟩

private theorem decoded_true (decode : Kernel Bool Bool) (b : Bool) :
    (decode ∘ₖ sensor) b {true} =
      (unitInterval.toNNReal accuracy : ℝ≥0∞) * decode b {true} +
      (unitInterval.toNNReal (unitInterval.symm accuracy) : ℝ≥0∞) * decode (!b) {true} := by
  rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton true)]
  change (∫⁻ x, decode x {true} ∂bernoulliMeasure b (!b) accuracy) = _
  simp [bernoulliMeasure_def, lintegral_add_measure, lintegral_smul_measure]

/-- Both sensor laws give positive mass to both reports. No decoder inverts them. -/
theorem sensor_has_no_decoder : ¬ ∃ decode : Kernel Bool Bool, decode ∘ₖ sensor = Kernel.id := by
  rintro ⟨decode, h⟩
  have hfalse := decoded_true decode false
  have htrue := decoded_true decode true
  rw [h] at hfalse htrue
  have ha : unitInterval.toNNReal accuracy ≠ 0 := by
    apply ne_of_gt
    change (0 : ℝ) < 3 / 4
    norm_num
  have hb : unitInterval.toNNReal (unitInterval.symm accuracy) ≠ 0 := by
    apply ne_of_gt
    change (0 : ℝ) < 1 - 3 / 4
    norm_num
  simp [Kernel.id_apply, eq_comm (a := (0 : ℝ≥0∞)), ha, hb] at hfalse
  simp [Kernel.id_apply, hfalse] at htrue

end PolyFunTest.TerminalDecisions
