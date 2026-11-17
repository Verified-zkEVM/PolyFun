/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.Polynomial.Monotone
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Monotonicity of Natural-Number Polynomial Evaluation

Evaluation of a polynomial with natural-number coefficients is monotone in its argument. CSLib
states this for every canonically ordered semiring as `Polynomial.eval_mono` and
`Polynomial.monotone_eval`. `Polynomial.eval_le_eval` is the deprecated `ℕ` case of
`Polynomial.eval_mono`.
-/

public section

/-- Evaluation of a natural-number polynomial is monotone in the argument. -/
@[deprecated Polynomial.eval_mono +typeChanged (since := "2026-11-17")]
theorem Polynomial.eval_le_eval {p : Polynomial ℕ} {m n : ℕ} (h : m ≤ n) :
    p.eval m ≤ p.eval n :=
  p.eval_mono h
