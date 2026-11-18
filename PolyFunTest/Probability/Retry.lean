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

/-- A cached false answer makes a positive lower bound on conditional success impossible. -/
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

end PolyFunTest.Probability.Retry
