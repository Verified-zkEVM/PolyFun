/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ToCslib.Data.Nat.PolynomialBound

/-!
# Canaries for polynomially bounded functions

The staged lemmas over cslib's `Cslib.PolynomiallyBounded`: the polynomial form of the bound, the
bound by a polynomial, domination of a function only eventually below a bounded one, and `2 ^ n`.
Also the staged bound of a natural-number polynomial by a constant multiple of a shifted power.
-/

public section

open Filter Cslib

namespace PolyFunTest.ToCslib.PolynomialBound

/-- `X ^ 2 + 1` is at most a constant multiple of a power of `n + 1`. -/
example : ∃ c k : ℕ, ∀ n : ℕ, (Polynomial.X ^ 2 + 1 : Polynomial ℕ).eval n ≤ c * (n + 1) ^ k :=
  (Polynomial.X ^ 2 + 1 : Polynomial ℕ).exists_eval_le_mul_add_one_pow

/-- A bound by `n ^ 2 + 3` is a polynomial bound. -/
example : PolynomiallyBounded fun n => n ^ 2 + 3 :=
  polynomiallyBounded_iff_exists_polynomial.2
    ⟨Polynomial.X ^ 2 + Polynomial.C 3, fun n => by simp⟩

/-- A function that is large on a finite prefix and then at most `n` is polynomially bounded. -/
example : PolynomiallyBounded fun n => if n < 10 then 2 ^ 100 else n :=
  (polynomiallyBounded_eval Polynomial.X).mono <| by
    filter_upwards [eventually_ge_atTop 10] with n hn
    simp [Nat.not_lt.2 hn]

/-- An exponential is not polynomially bounded, so neither is anything above it. -/
example (f : ℕ → ℕ) (hf : ∀ n, 2 ^ n ≤ f n) : ¬ PolynomiallyBounded f := fun h =>
  not_polynomiallyBounded_two_pow (h.mono (.of_forall hf))

end PolyFunTest.ToCslib.PolynomialBound
