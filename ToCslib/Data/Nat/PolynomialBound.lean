/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import ToCslib.Algebra.PolynomialGrowth

/-!
# Polynomially bounded functions and natural-number polynomials

`Cslib.PolynomiallyBounded f` says that a fixed power eventually bounds `f`. Equivalently, a
natural-number polynomial bounds `f` at every argument
(`Cslib.polynomiallyBounded_iff_exists_polynomial`). The class is closed under eventual domination
(`Cslib.PolynomiallyBounded.mono`), and `2 ^ n` is not in it
(`Cslib.not_polynomiallyBounded_two_pow`).
-/

public section

-- upstream candidate: `Cslib.Foundations.Data.Nat.PolynomialBound`, after
-- `Polynomial.exists_eval_le_mul_add_one_pow` (staged in `ToCslib.Algebra.PolynomialGrowth`)

open Filter

namespace Cslib

/-- A polynomially bounded function is at most a natural-number polynomial at every argument. -/
theorem polynomiallyBounded_iff_exists_polynomial {f : ℕ → ℕ} :
    PolynomiallyBounded f ↔ ∃ q : Polynomial ℕ, ∀ n, f n ≤ q.eval n := by
  rw [polynomiallyBounded_iff_le]
  constructor
  · rintro ⟨c, k, h⟩
    exact ⟨Polynomial.C c * (Polynomial.X + 1) ^ k, fun n => by simpa using h n⟩
  · rintro ⟨q, hq⟩
    obtain ⟨c, k, h⟩ := q.exists_eval_le_mul_add_one_pow
    exact ⟨c, k, fun n => (hq n).trans (h n)⟩

/-- Every natural-number polynomial is polynomially bounded. -/
theorem polynomiallyBounded_eval (q : Polynomial ℕ) : PolynomiallyBounded q.eval :=
  polynomiallyBounded_iff_exists_polynomial.2 ⟨q, fun _ => le_rfl⟩

/-- A function eventually at most a polynomially bounded function is polynomially bounded. -/
theorem PolynomiallyBounded.mono {f g : ℕ → ℕ} (hg : PolynomiallyBounded g) (h : f ≤ᶠ[atTop] g) :
    PolynomiallyBounded f :=
  let ⟨d, hd⟩ := hg
  ⟨d, h.trans hd⟩

/-- `2 ^ n` is not polynomially bounded. -/
theorem not_polynomiallyBounded_two_pow : ¬ PolynomiallyBounded (2 ^ ·) := fun h => by
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.1 h
  obtain ⟨n, hn⟩ := (Nat.eventually_const_mul_pow_le_two_pow (c + 1) d).exists
  have hle := hn.trans (hcd n)
  rw [add_one_mul] at hle
  exact (Nat.lt_add_of_pos_right (by positivity)).not_ge hle

end Cslib
