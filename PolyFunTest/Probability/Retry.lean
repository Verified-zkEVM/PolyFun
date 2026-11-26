/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.Retry
public import ToCslib.MeasureTheory.MeasurableSpace.Option
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Retrying with fresh coins and cached coins

The retry client in these examples is the same resumption `Retry.tree`. A fresh trial
increments the attempt counter and samples a fair Boolean. A caching implementation
stores the first answer and replays it on later requests. The fresh client returns
with probability one and makes two attempts in expectation. With a cached coin its
success probability stays at one half and its expected number of attempts is infinite.

A kernel that aborts on the first trial incurs that trial’s charge and has zero return mass.

The boundary cases test each bound at its extremes. The fresh coin attains the success-form
bound at `p = 1/2`. A trial that retries with mass one half and otherwise aborts costs exactly
two at unit price, the retry-mass bound with `p = 1/2`, and never succeeds. A trial that
succeeds at once with price seven attains the success-form bound at `p = 1`. At `p = 2` it
meets the retry-mass hypothesis but costs more than `7 / 2`, so that form needs `p ≤ 1`. A
trial that succeeds with mass one half satisfies every hypothesis of eventual success except
losslessness, and succeeds with mass one half. A last kernel leaves its invariant on success
and is trapped outside it, so the invariant is needed only on retries from invariant states.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor.Resumption PFunctor.Resumption.Retry
open scoped ENNReal

namespace PolyFunTest.Probability.Retry

private noncomputable def coin {α : Type*} [MeasurableSpace α] (x y : α) : Measure α :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac x + (2⁻¹ : ℝ≥0∞) • Measure.dirac y

private theorem integral_coin {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → ℝ≥0∞) (x y : α) :
    ∫⁻ z, f z ∂coin x y = 2⁻¹ * f x + 2⁻¹ * f y := by
  simp [coin, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]

/-- A new coin is sampled each time. The state counts the trials attempted so far. -/
noncomputable def fresh : Kernel ℕ (Bool × ℕ) :=
  Kernel.ofFunOfCountable fun i => coin (true, i + 1) (false, i + 1)

private theorem fresh_apply (i : ℕ) : fresh i = coin (true, i + 1) (false, i + 1) := rfl

private instance : IsMarkovKernel fresh where
  isProbabilityMeasure i := ⟨by
    simp [fresh_apply, coin, ENNReal.inv_two_add_inv_two]⟩

private theorem fresh_succ (c : ℕ → ℝ≥0∞) (done cut : ℝ≥0∞) (n i : ℕ) :
    observe fresh c done cut (n + 1) i = c i + (2⁻¹ * done +
      2⁻¹ * observe fresh c done cut n (i + 1)) := by
  rw [observe_succ, fresh_apply, integral_coin]
  rfl

/-- The same positive success bound holds in every reached state. -/
theorem fresh_success (i : ℕ) :
    expectedCharge (fun _ => fresh) (fun _ _ => 0) tree (fun _ _ => 1) i = 1 := by
  apply expectedCharge_tree_success (p := 2⁻¹) (K := fresh) (I := fun _ => True) (by norm_num)
    (fun _ _ => Filter.Eventually.of_forall (by simp)) _ i trivial
  intro t _
  simp [fresh_apply, coin, Measure.dirac_apply_of_mem]

private theorem fresh_unit_observe (n i : ℕ) :
    observe fresh 1 0 0 n i = ∑ j ∈ Finset.range n, (2⁻¹ : ℝ≥0∞) ^ j := by
  induction n generalizing i with
  | zero => simp [observe_zero]
  | succ n ih => rw [fresh_succ, ih, geom_sum_succ]; simp [add_comm]

/-- The expected number of attempts with fresh fair coins is exactly two. -/
theorem fresh_unit_cost :
    expectedCharge (fun _ => fresh) (fun _ _ => 1) tree (fun _ _ => 0) 0 = 2 := by
  rw [expectedCharge_tree]
  simp_rw [show (fun _ : ℕ => (1 : ℝ≥0∞)) = 1 from rfl, fresh_unit_observe]
  rw [← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric_two]

/-- Store the first coin when the cache is empty. Replay a stored value on every later trial. -/
noncomputable def cached : Kernel (Option Bool) (Bool × Option Bool) :=
  Kernel.ofFunOfCountable fun s => match s with
    | none => coin (true, some true) (false, some false)
    | some b => Measure.dirac (b, some b)

private theorem cached_none : cached none = coin (true, some true) (false, some false) := rfl

private theorem cached_some (b : Bool) : cached (some b) = Measure.dirac (b, some b) := rfl

/-- A cached false answer has success mass zero, so no positive lower bound on conditional
success holds in every state the cache reaches. -/
theorem cached_false_success_mass :
    cached (some false) {z | z.1 = true} = 0 := by
  simp [cached_some]

private theorem cached_false_succ (c : Option Bool → ℝ≥0∞) (done cut : ℝ≥0∞) (n : ℕ) :
    observe cached c done cut (n + 1) (some false) =
      c (some false) + observe cached c done cut n (some false) := by
  rw [observe_succ, cached_some, lintegral_dirac]
  rfl

private theorem cached_none_succ (c : Option Bool → ℝ≥0∞) (done cut : ℝ≥0∞) (n : ℕ) :
    observe cached c done cut (n + 1) none =
      c none + (2⁻¹ * done + 2⁻¹ * observe cached c done cut n (some false)) := by
  rw [observe_succ, cached_none, integral_coin]
  rfl

private theorem cached_false_success (n : ℕ) : observe cached 0 1 0 n (some false) = 0 := by
  induction n with
  | zero => simp [observe_zero]
  | succ n ih => simp [cached_false_succ, ih]

/-- Starting from an empty cache, exactly half the clients ever receive true. -/
theorem cached_success :
    expectedCharge (fun _ => cached) (fun _ _ => 0) tree (fun _ _ => 1) none = 2⁻¹ := by
  rw [expectedCharge_tree]
  change (⨆ n, observe cached 0 1 0 n none) = _
  apply le_antisymm
  · refine iSup_le fun n => ?_
    cases n with
    | zero => simp [observe_zero]
    | succ n => simp [cached_none_succ, cached_false_success]
  · simpa [cached_none_succ, cached_false_success]
      using le_iSup (fun n => observe cached 0 1 0 n none) 1

private theorem cached_false_cost (n : ℕ) : observe cached 1 0 0 n (some false) = n := by
  induction n with
  | zero => simp [observe_zero]
  | succ n ih => simp [cached_false_succ, ih, Nat.cast_succ, add_comm]

/-- Every retry on cached false costs another unit. Their positive mass gives infinite
unconditional expected cost, even though the cache sampled only once. -/
theorem cached_unit_cost :
    expectedCharge (fun _ => cached) (fun _ _ => 1) tree (fun _ _ => 0) none = ∞ := by
  rw [expectedCharge_tree, eq_top_iff]
  change ∞ ≤ ⨆ n, observe cached 1 0 0 n none
  have h (n : ℕ) : (2⁻¹ : ℝ≥0∞) * n ≤ ⨆ i, observe cached 1 0 0 i none := by
    apply le_trans _ (le_iSup (fun i => observe cached 1 0 0 i none) (n + 1))
    simp [cached_none_succ, cached_false_cost]
  have := iSup_le h
  simpa [← ENNReal.mul_iSup, ENNReal.iSup_natCast] using this

/-- A trial that aborts incurs its price and loses all terminal credit. Pricing the trial at
zero and the return at one gives zero success mass. -/
example (price reward : ℝ≥0∞) :
    expectedCharge (fun _ => (0 : Kernel Unit (Bool × Unit))) (fun _ _ => price)
      tree (fun _ _ => reward) () = price := by
  rw [tree_eq_query, expectedCharge_query (P := Trial) _ _ (fun _ => measurable_const) _ _ _
    (fun _ => measurable_const)]
  simp

/-! ## Boundary cases of the bounds -/

/-- The success-form bound at `p = 1/2` gives two, which `fresh_unit_cost` attains. -/
example : expectedCharge (fun _ => fresh) (fun _ _ => 1) tree (fun _ _ => 0) 0 ≤ 1 / 2⁻¹ :=
  expectedCharge_tree_le_div (I := fun _ => True)
    (fun _ _ => Filter.Eventually.of_forall (by simp))
    (fun _ _ => by simp [fresh_apply, coin, Measure.dirac_apply_of_mem]) (fun _ _ => le_rfl) 0
    trivial

/-- Retry with mass one half and abort otherwise. -/
noncomputable def halfAbort : Kernel Unit (Bool × Unit) :=
  Kernel.const Unit ((2⁻¹ : ℝ≥0∞) • Measure.dirac (false, ()))

private theorem halfAbort_succ (c : Unit → ℝ≥0∞) (done cut : ℝ≥0∞) (n : ℕ) :
    observe halfAbort c done cut (n + 1) () =
      c () + 2⁻¹ * observe halfAbort c done cut n () := by
  rw [observe_succ, halfAbort, Kernel.const_apply, lintegral_smul_measure, lintegral_dirac]
  rfl

private theorem halfAbort_unit_observe (n : ℕ) :
    observe halfAbort 1 0 0 n () = ∑ j ∈ Finset.range n, (2⁻¹ : ℝ≥0∞) ^ j := by
  induction n with
  | zero => simp [observe_zero]
  | succ n ih =>
    rw [halfAbort_succ, ih, Finset.sum_range_succ', Finset.mul_sum]
    simp [pow_succ, add_comm, mul_comm]

/-- Retrying with mass one half and aborting otherwise costs exactly two at unit price. -/
theorem halfAbort_unit_cost :
    expectedCharge (fun _ => halfAbort) (fun _ _ => 1) tree (fun _ _ => 0) () = 2 := by
  rw [expectedCharge_tree]
  simp_rw [show (fun _ : Unit => (1 : ℝ≥0∞)) = 1 from rfl, halfAbort_unit_observe]
  rw [← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric_two]

/-- The retry-mass bound with `p = 1/2` gives two, which `halfAbort_unit_cost` attains. -/
theorem halfAbort_cost_le :
    expectedCharge (fun _ => halfAbort) (fun _ _ => 1) tree (fun _ _ => 0) () ≤ 2 := by
  have h := expectedCharge_tree_le_div_of_retry_mass_le (K := halfAbort) (I := fun _ => True)
    (c := fun _ => 1) (C := 1) (p := 2⁻¹) (fun _ _ => ae_of_all _ fun _ _ => trivial)
    (by norm_num) (fun _ _ => ?_) (fun _ _ => le_rfl) () trivial
  · simpa using h
  · simp [halfAbort, Measure.dirac_apply_of_mem, ENNReal.one_sub_inv_two]

/-- The aborting trial never succeeds, although its expected cost is finite. -/
theorem halfAbort_success :
    expectedCharge (fun _ => halfAbort) (fun _ _ => 0) tree (fun _ _ => 1) () = 0 := by
  rw [expectedCharge_tree]
  change (⨆ n, observe halfAbort 0 1 0 n ()) = 0
  have h (n : ℕ) : observe halfAbort 0 1 0 n () = 0 := by
    induction n with
    | zero => simp [observe_zero]
    | succ n ih => simp [halfAbort_succ, ih]
  simp [h]

/-- Succeed at once. -/
noncomputable def always : Kernel Unit (Bool × Unit) :=
  Kernel.const Unit (Measure.dirac (true, ()))

private instance : IsMarkovKernel always := by
  unfold always
  infer_instance

/-- A trial that succeeds at once pays its price once. -/
theorem always_cost :
    expectedCharge (fun _ => always) (fun _ _ => 7) tree (fun _ _ => 0) () = 7 := by
  rw [tree_eq_query, expectedCharge_query (P := Trial) _ _ (fun _ => measurable_const) _ _ _
    (fun _ => measurable_const)]
  simp [always]

/-- The success-form bound at `p = 1` gives seven, which `always_cost` attains. -/
example : expectedCharge (fun _ => always) (fun _ _ => 7) tree (fun _ _ => 0) () ≤ 7 / 1 :=
  expectedCharge_tree_le_div (I := fun _ => True)
    (fun _ _ => ae_of_all _ fun _ _ => trivial)
    (fun _ _ => by simp [always, Measure.dirac_apply_of_mem]) (fun _ _ => le_rfl) () trivial

/-- Without `p ≤ 1` the retry-mass form fails at `p = 2`. The trial's retry mass is at most
`1 - 2 = 0`, but it costs seven, more than `7 / 2`. -/
example : always () {z | z.1 = false} ≤ 1 - 2 ∧
    ¬ expectedCharge (fun _ => always) (fun _ _ => 7) tree (fun _ _ => 0) () ≤ 7 / 2 := by
  refine ⟨by simp [always], ?_⟩
  rw [always_cost, not_le]
  exact ENNReal.half_lt_self (by norm_num) (by norm_num)

/-- Succeed with mass one half and abort otherwise. -/
noncomputable def halfSucceed : Kernel Unit (Bool × Unit) :=
  Kernel.const Unit ((2⁻¹ : ℝ≥0∞) • Measure.dirac (true, ()))

example : IsSubprobabilityKernel halfSucceed :=
  ⟨fun _ => by simp [halfSucceed]⟩

/-- The conditional success mass is one half in the only state. -/
theorem halfSucceed_success_mass : halfSucceed () {z | z.1 = true} = 2⁻¹ := by
  simp [halfSucceed, Measure.dirac_apply_of_mem]

/-- A lossy trial with a positive success bound still has success mass below one, so
`expectedCharge_tree_success` needs a Markov kernel. -/
theorem halfSucceed_success :
    expectedCharge (fun _ => halfSucceed) (fun _ _ => 0) tree (fun _ _ => 1) () = 2⁻¹ := by
  rw [tree_eq_query, expectedCharge_query (P := Trial) _ _ (fun _ => measurable_const) _ _ _
    (fun _ => measurable_const)]
  simp [halfSucceed, lintegral_smul_measure]

/-- From `false`, a fair trial, whose success moves the state to `true`. From `true`, every
trial retries and stays in `true`. -/
noncomputable def sticky : Kernel Bool (Bool × Bool) :=
  Kernel.ofFunOfCountable fun s => if s then Measure.dirac (false, true)
    else coin (true, true) (false, false)

private theorem sticky_false : sticky false = coin (true, true) (false, false) := rfl

private theorem sticky_true : sticky true = Measure.dirac (false, true) := rfl

private instance : IsMarkovKernel sticky where
  isProbabilityMeasure s := ⟨by
    cases s
    · simp [sticky_false, coin, ENNReal.inv_two_add_inv_two]
    · simp [sticky_true]⟩

/-- The invariant `s = false` holds after every retry from `false`. It fails after a success
from `false`, and after a retry from `true`, which is outside it. -/
theorem sticky_preserves : Preserves sticky (· = false) := by
  rintro s rfl
  rw [ae_iff]
  have : {z : Bool × Bool | ¬(z.1 = false → z.2 = false)} = {(false, true)} := by
    ext ⟨a, b⟩
    cases a <;> cases b <;> simp
  rw [this]
  simp [sticky_false, coin]

/-- The success-form bound applies from `false`, although `true` is a trap. -/
example : expectedCharge (fun _ => sticky) (fun _ _ => 1) tree (fun _ _ => 0) false ≤ 2 := by
  have h := expectedCharge_tree_le_div (K := sticky) (c := fun _ => 1) (C := 1) (p := 2⁻¹)
    sticky_preserves (fun s hs => ?_) (fun _ _ => le_rfl) false rfl
  · simpa using h
  · subst hs
    simp [sticky_false, coin, Measure.dirac_apply_of_mem]

end PolyFunTest.Probability.Retry
