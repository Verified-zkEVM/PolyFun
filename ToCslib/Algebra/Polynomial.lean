/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Monotonicity of Natural-Number Polynomial Evaluation

Evaluation of a polynomial with natural-number coefficients is monotone in its argument:
every term `c * x ^ i` is monotone in `x`. Mathlib does not state this for `Polynomial ℕ`, so
the lemma is staged here for upstreaming. Polynomial time envelopes in the complexity backends
use it to compare bounds at different input lengths.
-/

public section

/-- Evaluation of a natural-number polynomial is monotone in the argument. -/
theorem Polynomial.eval_le_eval {p : Polynomial ℕ} {m n : ℕ} (h : m ≤ n) :
    p.eval m ≤ p.eval n := by
  rw [p.eval_eq_sum_range, p.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)
