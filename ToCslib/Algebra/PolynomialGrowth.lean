/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Elias Judin
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Polynomial growth against `2 ^ n`

Every fixed power, every constant multiple of a shifted power, and hence every natural-number
polynomial is eventually dominated by `2 ^ n`; the polynomial bound is stated against `2 ^ (n / 4)`
so that it can be fed to a machine-counting argument whose count at size `2 ^ (n / 4)` must stay
below `2 ^ (2 ^ n)`. These are Mathlib candidates and import nothing from PolyFun.
-/

public section

open Filter Asymptotics

-- upstream candidate: `Mathlib.Analysis.SpecificLimits.Normed`
/-- Any fixed power is eventually dominated by `2 ^ n`. -/
theorem Nat.eventually_pow_le_two_pow (k : ℕ) : ∀ᶠ n in atTop, n ^ k ≤ 2 ^ n := by
  have h : (fun n : ℕ => (n : ℝ) ^ k) =o[atTop] fun n : ℕ => (2 : ℝ) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt k (by norm_num)
  refine h.eventuallyLE.mono fun n hn => ?_
  simp only [Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hn
  exact_mod_cast (by push_cast; exact hn : ((n ^ k : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))

/-- A constant multiple of any fixed power of `n + 1` is eventually dominated by `2 ^ n`. -/
theorem Nat.eventually_const_mul_pow_le_two_pow (C k : ℕ) :
    ∀ᶠ m in atTop, C * (m + 1) ^ k ≤ 2 ^ m := by
  filter_upwards [eventually_ge_atTop (C * 2 ^ k), eventually_ge_atTop 1,
    Nat.eventually_pow_le_two_pow (k + 1)] with m hm hm1 hm3
  calc C * (m + 1) ^ k ≤ C * (2 * m) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
    _ = C * 2 ^ k * m ^ k := by rw [mul_pow]; ring
    _ ≤ m * m ^ k := Nat.mul_le_mul_right _ hm
    _ = m ^ (k + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ m := hm3

/-- **Polynomials are eventually dominated by `2 ^ (n / 4)`.** The exponent `n / 4` is the
threshold fed to the machine count: fast enough to eventually exceed every polynomial
description bound (this lemma), yet slow enough that the resulting machine count stays below
`2 ^ (2 ^ n)` (`eventually_count_lt`). -/
theorem Polynomial.eventually_eval_le_two_pow_div_four (p : Polynomial ℕ) :
    ∀ᶠ n in atTop, p.eval n ≤ 2 ^ (n / 4) := by
  obtain ⟨C, k, hCk⟩ : ∃ C k : ℕ, ∀ n : ℕ, p.eval n ≤ C * (n + 1) ^ k := by
    refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, p.natDegree, fun n => ?_⟩
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) i).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have htend : Tendsto (fun n : ℕ => n / 4) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  filter_upwards [htend.eventually (Nat.eventually_const_mul_pow_le_two_pow (C * 4 ^ k) k)]
    with n hn
  calc p.eval n ≤ C * (n + 1) ^ k := hCk n
    _ ≤ C * 4 ^ k * (n / 4 + 1) ^ k := by
        rw [mul_assoc, ← mul_pow]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
    _ ≤ 2 ^ (n / 4) := hn
