/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Support
public import PolyFunProbability.PFunctor.Free.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Possible outputs and positive mass

PolyFun's `MonadAttach` support of a free program is the set of results some answers can reach.
This module relates it to the measure fold. Over discrete answer types, every result of positive
mass is a possible output (`mem_support_of_measureFold_singleton_ne_zero`). Conversely, when every
answer of every operation has positive mass, every possible output has positive mass
(`measureFold_singleton_ne_zero_of_mem_support`), so the two sets agree
(`support_eq_setOf_measureFold_ne_zero`).

Without full support the inclusion is strict: an answer measure may give a reachable answer zero
mass, so reachability and positive probability stay separate notions.
-/

@[expose] public section

open MeasureTheory

universe u v uA

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)]
  [∀ a, DiscreteMeasurableSpace (P.B a)] (μ : (a : P.A) → Measure (P.B a))
  {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A result of positive mass under the measure fold is a possible output. -/
theorem mem_support_of_measureFold_singleton_ne_zero {program : FreeM P α} {v : α}
    (h : measureFold μ program {v} ≠ 0) : v ∈ MonadAttach.support program := by
  induction program using FreeM.rec with
  | pure x =>
    change Measure.dirac x {v} ≠ 0 at h
    rw [Measure.dirac_apply] at h
    by_contra hv
    exact h (Set.indicator_of_notMem (fun hx => hv (Set.mem_singleton_iff.1 hx).symm) _)
  | liftBind a cont ih =>
    rw [measureFold_liftBind μ a cont Measurable.of_discrete.aemeasurable,
      Measure.bind_apply (measurableSet_singleton v) Measurable.of_discrete.aemeasurable] at h
    obtain ⟨b, hb⟩ : ∃ b, measureFold μ (cont b) {v} ≠ 0 := by
      by_contra hne
      push Not at hne
      exact h (by simp [hne])
    exact Set.mem_iUnion.2 ⟨b, ih b hb⟩

/-- When every answer of every operation has positive mass, every possible output has positive
mass under the measure fold. -/
theorem measureFold_singleton_ne_zero_of_mem_support (hμ : ∀ a b, μ a {b} ≠ 0)
    {program : FreeM P α} {v : α} (h : v ∈ MonadAttach.support program) :
    measureFold μ program {v} ≠ 0 := by
  induction program using FreeM.rec with
  | pure x =>
    obtain rfl : v = x := h
    change Measure.dirac v {v} ≠ 0
    rw [Measure.dirac_apply_of_mem (Set.mem_singleton v)]
    exact one_ne_zero
  | liftBind a cont ih =>
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 h
    rw [measureFold_liftBind μ a cont Measurable.of_discrete.aemeasurable,
      Measure.bind_apply (measurableSet_singleton v) Measurable.of_discrete.aemeasurable]
    refine ne_of_gt (lt_of_lt_of_le ?_ (setLIntegral_le_lintegral {b} _))
    rw [lintegral_singleton]
    exact pos_iff_ne_zero.2 (mul_ne_zero (ih b hb) (hμ a b))

/-- Under answer measures of full support, the possible outputs of a program are exactly its
results of positive mass. -/
theorem support_eq_setOf_measureFold_ne_zero (hμ : ∀ a b, μ a {b} ≠ 0) (program : FreeM P α) :
    MonadAttach.support program = {v | measureFold μ program {v} ≠ 0} :=
  Set.ext fun _ => ⟨measureFold_singleton_ne_zero_of_mem_support μ hμ,
    mem_support_of_measureFold_singleton_ne_zero μ⟩

end PFunctor.FreeM
