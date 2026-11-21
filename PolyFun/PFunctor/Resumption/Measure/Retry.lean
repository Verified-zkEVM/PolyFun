/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.ExpectedCharge
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Retrying a stateful Boolean trial

A resumption repeats one request until the answer is true. A trial kernel jointly samples
its answer and the private state for the next trial. Bounding the conditional retry mass
in every invariant state bounds the probability of needing more trials and the expected
cost already incurred. The current trial pays its charge even if its kernel loses mass.

The geometric cost bound applies to subprobability trials. Almost-sure success additionally
assumes a Markov trial kernel, which returns an answer with total probability one.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace PFunctor.Resumption.Retry

/-- One Boolean trial, repeated until success. -/
abbrev Trial := monomial Unit Bool

private def step : Bool → Unit ⊕ Trial.Obj Bool
  | true => .inl ()
  | false => .inr ⟨(), id⟩

/-- Repeatedly request a trial. The first true answer ends the computation. -/
def tree : Resumption Trial Unit := corec step false

private theorem corec_true : corec step true = pure () := by
  apply eq_of_dest_eq
  simp [step]

theorem tree_eq_query : tree = query () (fun b : Bool => if b then pure () else tree) := by
  apply eq_of_dest_eq
  simp only [tree, dest_corec, dest_query, step, Sum.map_inr, Sum.inr.injEq]
  change PFunctor.Obj.mk (P := Trial) () (fun b : Bool => corec step b) =
    PFunctor.Obj.mk (P := Trial) () _
  congr 1
  funext b
  cases b <;> simp [corec_true]

variable {S : Type*} [MeasurableSpace S]

/-- Observe at most `n` trials. A success contributes `done` and a cutoff contributes
`cut`. Every trial contributes its charge before sampling its answer and successor state. -/
@[expose] noncomputable def observe (K : Kernel S (Bool × S)) (c : S → ℝ≥0∞) (done cut : ℝ≥0∞) :
    ℕ → S → ℝ≥0∞
  | 0, _ => cut
  | n + 1, s => c s + ∫⁻ z, (if z.1 then done else observe K c done cut n z.2) ∂K s

@[simp] theorem observe_zero (K : Kernel S (Bool × S)) (c : S → ℝ≥0∞)
    (done cut : ℝ≥0∞) (s : S) : observe K c done cut 0 s = cut := rfl

theorem observe_succ (K : Kernel S (Bool × S)) (c : S → ℝ≥0∞) (done cut : ℝ≥0∞)
    (n : ℕ) (s : S) : observe K c done cut (n + 1) s =
      c s + ∫⁻ z, (if z.1 then done else observe K c done cut n z.2) ∂K s := rfl

theorem measurable_observe (K : Kernel S (Bool × S)) {c : S → ℝ≥0∞} (hc : Measurable c)
    (done cut : ℝ≥0∞) (n : ℕ) : Measurable (observe K c done cut n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    refine hc.add (Measurable.lintegral_kernel ?_)
    exact Measurable.ite (measurable_fst (measurableSet_singleton true))
      measurable_const (ih.comp measurable_snd)

/-- The finite observation is the expected-charge fold of the actual truncated retry program. -/
theorem wpFold_truncate_tree (K : Kernel S (Bool × S)) (c : S → ℝ≥0∞) (done cut : ℝ≥0∞)
    (n : ℕ) (s : S) :
    FreeM.wpFold (OpSpec.statefulExpectedCharge (P := Trial) (fun _ => K) (fun _ => c))
      (truncate n tree) (fun result => result.elim (fun _ => cut) (fun _ _ => done)) s =
        observe K c done cut n s := by
  induction n generalizing s with
  | zero =>
    rw [tree_eq_query, truncate_query_zero]
    rfl
  | succ n ih =>
    rw [tree_eq_query, truncate_query_succ, FreeM.wpFold_liftBind,
      OpSpec.statefulExpectedCharge_apply, observe]
    congr 1
    apply lintegral_congr
    rintro ⟨b, t⟩
    cases b <;> simp [ih]

/-- The cost and terminal observation of unbounded retries is the limit of finite observations. -/
theorem expectedCharge_tree (K : Kernel S (Bool × S)) (c : S → ℝ≥0∞) (done : ℝ≥0∞) (s : S) :
    expectedCharge (fun _ => K) (fun _ => c) tree (fun _ _ => done) s =
      ⨆ n, observe K c done 0 n s := by
  rw [expectedCharge_eq_iSup]
  exact iSup_congr fun n => wpFold_truncate_tree K c done 0 n s

/-- A reached retry must leave the invariant true, up to null sets of the trial. -/
abbrev Preserves (K : Kernel S (Bool × S)) (I : S → Prop) : Prop :=
  ∀ s, I s → ∀ᵐ z ∂K s, z.1 = false → I z.2

private theorem lintegral_retry_le (μ : Measure (Bool × S)) (f : S → ℝ≥0∞)
    {b : ℝ≥0∞} (h : ∀ᵐ z ∂μ, z.1 = false → f z.2 ≤ b) :
    (∫⁻ z, (if z.1 then 0 else f z.2) ∂μ) ≤ b * μ {z | z.1 = false} := by
  have hm : MeasurableSet {z : Bool × S | z.1 = false} :=
    measurable_fst (measurableSet_singleton false)
  rw [← lintegral_indicator_const (μ := μ) hm b]
  refine lintegral_mono_ae (h.mono fun z hz => ?_)
  cases hb : z.1 <;> simp [Set.indicator, hb, hz]

variable {K : Kernel S (Bool × S)} {I : S → Prop} {q C : ℝ≥0∞} {c : S → ℝ≥0∞}

/-- The probability that all of the first `n` trials return retry is at most `q ^ n`. -/
theorem tail_le_pow (hI : Preserves K I)
    (hq : ∀ s, I s → K s {z | z.1 = false} ≤ q) (n : ℕ) (s : S) (hs : I s) :
    observe K 0 0 1 n s ≤ q ^ n := by
  induction n generalizing s with
  | zero => simp [observe]
  | succ n ih =>
    simp only [observe, Pi.zero_apply, zero_add, pow_succ]
    exact (lintegral_retry_le _ _ ((hI s hs).mono fun z hz hb => ih _ (hz hb))).trans
      (mul_le_mul_right (hq s hs) _)

/-- Expected cost through `n` trials, when each trial costs at most `C` in invariant states. -/
theorem observe_cost_le_geom_sum (hI : Preserves K I)
    (hq : ∀ s, I s → K s {z | z.1 = false} ≤ q) (hc : ∀ s, I s → c s ≤ C)
    (n : ℕ) (s : S) (hs : I s) :
    observe K c 0 0 n s ≤ C * ∑ i ∈ Finset.range n, q ^ i := by
  induction n generalizing s with
  | zero => simp [observe]
  | succ n ih =>
    rw [observe, geom_sum_succ, mul_add, mul_one, add_comm _ C]
    apply add_le_add (hc s hs)
    refine (lintegral_retry_le _ _ ((hI s hs).mono fun z hz hb => ih _ (hz hb))).trans ?_
    calc _ ≤ (C * ∑ i ∈ Finset.range n, q ^ i) * q := mul_le_mul_right (hq s hs) _
         _ = _ := by ac_rfl

/-- A bound on the mass of retrying suffices to bound the incurred charge, including when
the trial kernel can abort. -/
theorem expectedCharge_tree_le_div_of_retry_mass_le (hI : Preserves K I) {p : ℝ≥0∞} (hp : p ≤ 1)
    (hq : ∀ s, I s → K s {z | z.1 = false} ≤ 1 - p)
    (hc : ∀ s, I s → c s ≤ C) (s : S) (hs : I s) :
    expectedCharge (fun _ => K) (fun _ => c) tree (fun _ _ => 0) s ≤ C / p := by
  rw [expectedCharge_tree]
  refine iSup_le fun n => (observe_cost_le_geom_sum hI hq hc n s hs).trans ?_
  have h := sum_le_tsum (f := fun i : ℕ => (1 - p) ^ i) (Finset.range n)
  have hfin : 1 - p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hsub := (ENNReal.cancel_of_ne hfin).tsub_tsub_cancel_of_le hp
  simpa [ENNReal.tsum_geometric, hsub, div_eq_mul_inv]
    using mul_le_mul_right h C

/-- Each finite lossless execution has either succeeded or exhausted its trial limit. -/
theorem success_add_tail (K : Kernel S (Bool × S)) [IsMarkovKernel K] (n : ℕ) (s : S) :
    observe K 0 1 0 n s + observe K 0 0 1 n s = 1 := by
  induction n generalizing s with
  | zero => simp [observe]
  | succ n ih =>
    simp only [observe, Pi.zero_apply, zero_add]
    rw [← lintegral_add_left]
    · have hsum : ∀ z : Bool × S, (if z.1 then (1 : ℝ≥0∞) else observe K 0 1 0 n z.2) +
          (if z.1 then 0 else observe K 0 0 1 n z.2) = 1 := by
        rintro ⟨b,t⟩
        cases b <;> simp [ih]
      simp [hsum]
    · exact Measurable.ite (measurable_fst (measurableSet_singleton true)) measurable_const
        ((measurable_observe K measurable_const 1 0 n).comp measurable_snd)

/-- A positive uniform lower bound on conditional success gives eventual success of mass one. -/
theorem iSup_success_eq_one [IsMarkovKernel K] (hI : Preserves K I)
    (hq : ∀ s, I s → K s {z | z.1 = false} ≤ q) (hq' : q < 1) (s : S) (hs : I s) :
    (⨆ n, observe K 0 1 0 n s) = 1 := by
  apply le_antisymm
  · exact iSup_le fun n => (le_self_add ..).trans_eq (success_add_tail K n s)
  · have hb (n : ℕ) : 1 ≤ (⨆ j, observe K 0 1 0 j s) + q ^ n := by
      calc 1 = _ := (success_add_tail K n s).symm
           _ ≤ _ := add_le_add (le_iSup (fun j => observe K 0 1 0 j s) n) (tail_le_pow hI hq n s hs)
    have hlim := (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq').const_add
      (⨆ j, observe K 0 1 0 j s)
    simpa using ge_of_tendsto hlim (Eventually.of_forall hb)

private theorem retryMass_le_one_sub (K : Kernel S (Bool × S)) [IsSubprobabilityKernel K] (s : S) :
    K s {z | z.1 = false} ≤ 1 - K s {z | z.1 = true} := by
  have heq : {z : Bool × S | z.1 = false} = {z : Bool × S | z.1 = true}ᶜ := by
    ext ⟨b,t⟩
    cases b <;> simp
  have hm : MeasurableSet {z : Bool × S | z.1 = true} :=
    measurable_fst (measurableSet_singleton true)
  rw [heq, measure_compl hm (measure_ne_top _ _)]
  exact tsub_le_tsub_right (K.measure_univ_le s) _

/-- A lower bound on success and an upper bound on per-trial expected charge give a bound on
the unbounded resumption, from each invariant state. -/
theorem expectedCharge_tree_le_div [IsSubprobabilityKernel K] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hI : Preserves K I) (hsucc : ∀ s, I s → p ≤ K s {z | z.1 = true})
    (hc : ∀ s, I s → c s ≤ C) (s : S) (hs : I s) :
    expectedCharge (fun _ => K) (fun _ => c) tree (fun _ _ => 0) s ≤ C / p := by
  exact expectedCharge_tree_le_div_of_retry_mass_le hI hp
    (fun t ht => (retryMass_le_one_sub K t).trans (tsub_le_tsub_left (hsucc t ht) _)) hc s hs

/-- Eventual success has mass one when every reached state has a positive uniform chance of
success. Pricing each trial at zero and a return at one reads off the terminal mass. -/
theorem expectedCharge_tree_success [IsMarkovKernel K] {p : ℝ≥0∞} (hp : 0 < p)
    (hI : Preserves K I) (hsucc : ∀ s, I s → p ≤ K s {z | z.1 = true})
    (s : S) (hs : I s) :
    expectedCharge (fun _ => K) (fun _ _ => 0) tree (fun _ _ => 1) s = 1 := by
  rw [expectedCharge_tree]
  apply iSup_success_eq_one hI (q := 1 - p) _ _ s hs
  · intro t ht
    exact (retryMass_le_one_sub K t).trans (tsub_le_tsub_left (hsucc t ht) _)
  · exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp.ne'

end PFunctor.Resumption.Retry
