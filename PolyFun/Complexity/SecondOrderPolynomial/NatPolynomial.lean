/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Complexity.SecondOrderPolynomial
public import ToCslib.Algebra.Polynomial

/-!
# Ordinary polynomial bounds for second-order polynomials

Substituting polynomial upper bounds for response moduli gives an ordinary polynomial bound.
The moduli themselves need not be monotone: monotonicity of natural-coefficient polynomials
suffices to control nested oracle applications.
-/

public section

universe x

namespace Complexity.SecondOrderPolynomial

variable {ι : Type x}

/-- Replace every oracle-length symbol by a polynomial bound. -/
noncomputable def toNatPolynomial (bounds : ι → Polynomial ℕ) :
    SecondOrderPolynomial ι → Polynomial ℕ
  | .const value => .C value
  | .input => .X
  | .add left right => toNatPolynomial bounds left + toNatPolynomial bounds right
  | .mul left right => toNatPolynomial bounds left * toNatPolynomial bounds right
  | .oracle interface argument => (bounds interface).comp (toNatPolynomial bounds argument)

@[simp] theorem toNatPolynomial_const (bounds : ι → Polynomial ℕ) (value : ℕ) :
    toNatPolynomial bounds (.const value) = .C value := by simp [toNatPolynomial]

@[simp] theorem toNatPolynomial_input (bounds : ι → Polynomial ℕ) :
    toNatPolynomial bounds .input = .X := by simp [toNatPolynomial]

@[simp] theorem toNatPolynomial_add (bounds : ι → Polynomial ℕ)
    (left right : SecondOrderPolynomial ι) :
    toNatPolynomial bounds (.add left right) =
      toNatPolynomial bounds left + toNatPolynomial bounds right := by simp [toNatPolynomial]

@[simp] theorem toNatPolynomial_mul (bounds : ι → Polynomial ℕ)
    (left right : SecondOrderPolynomial ι) :
    toNatPolynomial bounds (.mul left right) =
      toNatPolynomial bounds left * toNatPolynomial bounds right := by simp [toNatPolynomial]

@[simp] theorem toNatPolynomial_oracle (bounds : ι → Polynomial ℕ)
    (interface : ι) (argument : SecondOrderPolynomial ι) :
    toNatPolynomial bounds (.oracle interface argument) =
      (bounds interface).comp (toNatPolynomial bounds argument) := by simp [toNatPolynomial]

/-- Substitution agrees exactly with evaluation at polynomial response moduli. -/
theorem eval_toNatPolynomial (bounds : ι → Polynomial ℕ)
    (q : SecondOrderPolynomial ι) (k : ℕ) :
    (toNatPolynomial bounds q).eval k = q.eval (fun i ↦ (bounds i).eval) k := by
  induction q with
  | const value => simp
  | input => simp
  | add left right ihl ihr => simp [ihl, ihr]
  | mul left right ihl ihr => simp [ihl, ihr]
  | oracle interface argument ih => simp [Polynomial.eval_comp, ih]

/-- Under polynomially bounded moduli, evaluation is bounded by the substituted polynomial. -/
theorem eval_le_toNatPolynomial (bounds : ι → Polynomial ℕ) (length : ι → ℕ → ℕ)
    (hlength : ∀ i m, length i m ≤ (bounds i).eval m) (q : SecondOrderPolynomial ι) (k : ℕ) :
    q.eval length k ≤ (toNatPolynomial bounds q).eval k := by
  induction q with
  | const value => simp [toNatPolynomial]
  | input => simp [toNatPolynomial]
  | add left right ihl ihr =>
      simp only [eval_add, toNatPolynomial, Polynomial.eval_add]
      omega
  | mul left right ihl ihr =>
      simp only [eval_mul, toNatPolynomial, Polynomial.eval_mul]
      exact Nat.mul_le_mul ihl ihr
  | oracle interface argument ih =>
      simp only [eval_oracle, toNatPolynomial, Polynomial.eval_comp]
      exact (hlength interface _).trans (Polynomial.eval_le_eval ih)

end Complexity.SecondOrderPolynomial

