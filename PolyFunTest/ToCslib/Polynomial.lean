/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Algebra.Polynomial

/-!
# Direct canaries for polynomial evaluation monotonicity

This example pins the argument-monotonicity of `Polynomial.eval` over `ℕ`.
-/

example (p : Polynomial ℕ) (k : ℕ) : p.eval k ≤ p.eval (k + 1) :=
  Polynomial.eval_le_eval (Nat.le_succ k)
