/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Algebra.Polynomial

/-!
# Direct canaries for polynomial evaluation monotonicity

The first example pins the argument-monotonicity of `Polynomial.eval` over `ℕ` under its
deprecated name, which reports its deprecation. The second applies the replacement in the form
that a use of the deprecated name takes.
-/

/--
warning: `Polynomial.eval_le_eval` has been deprecated: Use `Polynomial.eval_mono` instead

Note: The updated constant has a different type:
  ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing R] [CanonicallyOrderedAdd R]
    (p : Polynomial R) {a b : R}, a ≤ b → Polynomial.eval a p ≤ Polynomial.eval b p
instead of
  ∀ {p : Polynomial ℕ} {m n : ℕ}, m ≤ n → Polynomial.eval m p ≤ Polynomial.eval n p
-/
#guard_msgs in
example (p : Polynomial ℕ) (k : ℕ) : p.eval k ≤ p.eval (k + 1) :=
  Polynomial.eval_le_eval (Nat.le_succ k)

example (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n :=
  p.eval_mono h
