/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Order.Monotone.Basic

/-!
# Second-order polynomials for open computations

An ordinary polynomial in the initial input length cannot bound a general adaptive oracle
computation: the size of a later query can depend on the size of an earlier answer. Following
Kapron--Cook, a second-order polynomial may apply an oracle length function to a recursively
computed size bound.

`SecondOrderPolynomial ι` has one length-function symbol for every interface label in `ι`.
Its evaluation is constructive and exact. `comp` substitutes the input variable, while `subst`
replaces every length-function symbol by another second-order polynomial. The latter is the
algebraic operation needed when an open interface is implemented by a resource contract.

This syntax deliberately says nothing about which functions are feasible. A quantitative backend
must separately certify the concrete bounds substituted for the oracle symbols.
-/

@[expose] public section

universe u v

namespace Complexity

/-- A second-order polynomial with length-function variables indexed by `ι`. -/
inductive SecondOrderPolynomial (ι : Type u) where
  /-- A natural-number constant. -/
  | const (value : Nat)
  /-- The initial encoded input length. -/
  | input
  /-- Addition of resource bounds. -/
  | add (left right : SecondOrderPolynomial ι)
  /-- Multiplication of resource bounds. -/
  | mul (left right : SecondOrderPolynomial ι)
  /-- Apply an interface's length function to a recursively computed argument. -/
  | oracle (interface : ι) (argument : SecondOrderPolynomial ι)
deriving DecidableEq, Repr

namespace SecondOrderPolynomial

variable {ι : Type u} {κ : Type v}

/-- Evaluate a second-order polynomial at an input length and a family of length functions. -/
def eval (length : ι → Nat → Nat) (inputSize : Nat) : SecondOrderPolynomial ι → Nat
  | .const value => value
  | .input => inputSize
  | .add left right => left.eval length inputSize + right.eval length inputSize
  | .mul left right => left.eval length inputSize * right.eval length inputSize
  | .oracle interface argument => length interface (argument.eval length inputSize)

@[simp] theorem eval_const (length : ι → Nat → Nat) (inputSize value : Nat) :
    (const value : SecondOrderPolynomial ι).eval length inputSize = value :=
  rfl

@[simp] theorem eval_input (length : ι → Nat → Nat) (inputSize : Nat) :
    (input : SecondOrderPolynomial ι).eval length inputSize = inputSize :=
  rfl

@[simp] theorem eval_add (length : ι → Nat → Nat) (inputSize : Nat)
    (left right : SecondOrderPolynomial ι) :
    (add left right).eval length inputSize =
      left.eval length inputSize + right.eval length inputSize :=
  rfl

@[simp] theorem eval_mul (length : ι → Nat → Nat) (inputSize : Nat)
    (left right : SecondOrderPolynomial ι) :
    (mul left right).eval length inputSize =
      left.eval length inputSize * right.eval length inputSize :=
  rfl

@[simp] theorem eval_oracle (length : ι → Nat → Nat) (inputSize : Nat) (interface : ι)
    (argument : SecondOrderPolynomial ι) :
    (oracle interface argument).eval length inputSize =
      length interface (argument.eval length inputSize) :=
  rfl

/-- Replace the input variable of `outer` by `inner`. -/
def comp (outer inner : SecondOrderPolynomial ι) : SecondOrderPolynomial ι :=
  match outer with
  | .const value => .const value
  | .input => inner
  | .add left right => .add (left.comp inner) (right.comp inner)
  | .mul left right => .mul (left.comp inner) (right.comp inner)
  | .oracle interface argument => .oracle interface (argument.comp inner)

@[simp]
theorem eval_comp (outer inner : SecondOrderPolynomial ι) (length : ι → Nat → Nat)
    (inputSize : Nat) :
    (outer.comp inner).eval length inputSize =
      outer.eval length (inner.eval length inputSize) := by
  induction outer with
  | const value => rfl
  | input => rfl
  | add left right left_ih right_ih => simp only [comp, eval_add, left_ih, right_ih]
  | mul left right left_ih right_ih => simp only [comp, eval_mul, left_ih, right_ih]
  | oracle interface argument ih => simp only [comp, eval_oracle, ih]

/-- Relabel the interface symbols of a second-order polynomial. -/
def reindex (map : ι → κ) : SecondOrderPolynomial ι → SecondOrderPolynomial κ
  | .const value => .const value
  | .input => .input
  | .add left right => .add (left.reindex map) (right.reindex map)
  | .mul left right => .mul (left.reindex map) (right.reindex map)
  | .oracle interface argument => .oracle (map interface) (argument.reindex map)

@[simp]
theorem eval_reindex (polynomial : SecondOrderPolynomial ι) (map : ι → κ)
    (length : κ → Nat → Nat) (inputSize : Nat) :
    (polynomial.reindex map).eval length inputSize =
      polynomial.eval (fun interface ↦ length (map interface)) inputSize := by
  induction polynomial with
  | const value => rfl
  | input => rfl
  | add left right left_ih right_ih => simp only [reindex, eval_add, left_ih, right_ih]
  | mul left right left_ih right_ih => simp only [reindex, eval_mul, left_ih, right_ih]
  | oracle interface argument ih => simp only [reindex, eval_oracle, ih]

/-- Substitute a resource transformer for every source-interface length symbol. -/
def subst (replacement : ι → SecondOrderPolynomial κ) :
    SecondOrderPolynomial ι → SecondOrderPolynomial κ
  | .const value => .const value
  | .input => .input
  | .add left right => .add (left.subst replacement) (right.subst replacement)
  | .mul left right => .mul (left.subst replacement) (right.subst replacement)
  | .oracle interface argument =>
      (replacement interface).comp (argument.subst replacement)

@[simp]
theorem eval_subst (polynomial : SecondOrderPolynomial ι)
    (replacement : ι → SecondOrderPolynomial κ) (length : κ → Nat → Nat)
    (inputSize : Nat) :
    (polynomial.subst replacement).eval length inputSize =
      polynomial.eval (fun interface size ↦ (replacement interface).eval length size)
        inputSize := by
  induction polynomial with
  | const value => rfl
  | input => rfl
  | add left right left_ih right_ih => simp only [subst, eval_add, left_ih, right_ih]
  | mul left right left_ih right_ih => simp only [subst, eval_mul, left_ih, right_ih]
  | oracle interface argument ih => simp only [subst, eval_comp, eval_oracle, ih]

/-- Every length function supplied to an open-resource bound is monotone in message size. -/
def MonotoneLengths (length : ι → Nat → Nat) : Prop :=
  ∀ interface, Monotone (length interface)

/-- Evaluation is monotone in the initial input length when all length functions are monotone. -/
theorem eval_monotone (polynomial : SecondOrderPolynomial ι) {length : ι → Nat → Nat}
    (hLength : MonotoneLengths length) : Monotone (polynomial.eval length) := by
  intro left right hle
  induction polynomial with
  | const value => exact le_rfl
  | input => exact hle
  | add first second first_ih second_ih =>
      exact Nat.add_le_add first_ih second_ih
  | mul first second first_ih second_ih =>
      exact Nat.mul_le_mul first_ih second_ih
  | oracle interface argument ih =>
      exact hLength interface ih

/-- Evaluation is monotone under pointwise enlargement of monotone length functions. -/
theorem eval_mono_lengths (polynomial : SecondOrderPolynomial ι)
    {smaller larger : ι → Nat → Nat} (hLarger : MonotoneLengths larger)
    (hle : ∀ interface size, smaller interface size ≤ larger interface size)
    (inputSize : Nat) :
    polynomial.eval smaller inputSize ≤ polynomial.eval larger inputSize := by
  induction polynomial with
  | const value => exact le_rfl
  | input => exact le_rfl
  | add left right left_ih right_ih => exact Nat.add_le_add left_ih right_ih
  | mul left right left_ih right_ih => exact Nat.mul_le_mul left_ih right_ih
  | oracle interface argument ih =>
      exact (hle interface _).trans (hLarger interface ih)

end SecondOrderPolynomial

end Complexity
