/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Polynomial
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Logic.Function.Iterate

/-!
# Polynomial bounds for bounded backend iteration

A loop certificate supplies one backend code taking an encoded iteration count and state.
Its local cost comparison charges the actual step code at every intermediate state and keeps
loop administration explicit. Polynomial bounds follow from a polynomial iteration count,
an initial-state size bound, and a uniform additive bound on one step's size growth.

A polynomial bound for one step alone is insufficient: repeated size doubling can be
exponential. The size-growth premise controls every intermediate invocation. An iteration count
also needs its own bound in the encoded loop input; binary encoding alone does not supply it.

This module constructs polynomial certificates for supplied executable loop code. A backend must
implement that code and prove its cost comparison; semantic function iteration supplies neither.
-/

public section

universe u v w

namespace PFunctor.QuantitativeStepClass

open _root_.Complexity

variable {C : StepClass.{u, v}} {Q : QuantitativeStepClass.{u, v, w} C}
  {S : Type u} {state : C.Str S} {next : S → S}

/-- Backend work of each concrete step along the first `count` iterations. -/
@[expose] def iterationWork (step : Q.Realizer state state next) (count : ℕ) (initial : S) : ℕ :=
  ∑ i ∈ Finset.range count, Q.cost step (next^[i] initial)

/-- One uniform executable iterator and its local cost decomposition.

The input representation is explicit: it must encode both the count and initial state.
No code is selected separately for individual counts or states. -/
structure IterationCode (input : C.Str (ℕ × S)) (step : Q.Realizer state state next) where
  /-- Executable iteration, with semantic correctness supplied by the realizer's index. -/
  code : Q.Realizer input state fun value => next^[value.1] value.2
  /-- Backend work for loop control and its input representation. -/
  overhead : ℕ → S → ℕ
  /-- Loop code is charged against each executed step and its explicit administration. -/
  cost_le : ∀ count initial, Q.cost code (count, initial) ≤
    iterationWork step count initial + overhead count initial

namespace IterationCode

variable {input : C.Str (ℕ × S)} {step : Q.Realizer state state next}

/-- Additive one-step size growth bounds every state reached during iteration. -/
theorem size_iterate_le (growth : ℕ)
    (hstep : ∀ value, Q.size state (next value) ≤ Q.size state value + growth)
    (count : ℕ) (initial : S) :
    Q.size state (next^[count] initial) ≤ Q.size state initial + count * growth := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      apply (hstep _).trans
      simpa [Nat.succ_mul, Nat.add_assoc] using Nat.add_le_add_right ih growth

/-- Sum the step's polynomial work at a single envelope for every intermediate state. -/
theorem iterationWork_le (step : Q.PolyRealizer state state next) (count : ℕ)
    (initial : S) (envelope : ℕ)
    (hsize : ∀ i < count, Q.size state (next^[i] initial) ≤ envelope) :
    iterationWork step.code count initial ≤ count * step.work.eval envelope := by
  calc
    _ ≤ ∑ _i ∈ Finset.range count, step.work.eval envelope := by
      apply Finset.sum_le_sum
      intro i hi
      exact (step.work_le _).trans (step.work.eval_monotone
        (hsize i (Finset.mem_range.mp hi)))
    _ = _ := by simp

/-- Polynomial data needed for all inputs to one loop code.

Count and initial size are bounded in the whole encoded input. Additive size growth is a
property of the actual step function, and the overhead bound applies to the backend's loop
administration from `IterationCode`. -/
structure PolynomialBounds (loop : IterationCode input step) where
  /-- Upper bound for the iteration count in the encoded loop input. -/
  count : FirstOrderPolynomial
  /-- Upper bound for the encoded initial state in the encoded loop input. -/
  initialSize : FirstOrderPolynomial
  /-- Upper bound for all loop administration. -/
  overhead : FirstOrderPolynomial
  /-- Maximum additional encoded state size produced by one step. -/
  growth : ℕ
  /-- The count is polynomially bounded for every encoded input. -/
  count_le : ∀ n value, n ≤ count.eval (Q.size input (n, value))
  /-- The initial-state projection cannot hide arbitrarily large state. -/
  initialSize_le : ∀ n value, Q.size state value ≤ initialSize.eval (Q.size input (n, value))
  /-- Every transition has the asserted additive growth bound. -/
  growth_le : ∀ value, Q.size state (next value) ≤ Q.size state value + growth
  /-- The selected administration polynomial bounds the actual loop allowance. -/
  overhead_le : ∀ n value, loop.overhead n value ≤ overhead.eval (Q.size input (n, value))

namespace PolynomialBounds

variable {loop : IterationCode input step}

/-- One envelope for all intermediate states and the final output. -/
@[expose] def stateSize (bounds : PolynomialBounds loop) : FirstOrderPolynomial :=
  .add bounds.initialSize (.mul bounds.count (.const bounds.growth))

/-- The size envelope covers every finite prefix, including the final state. -/
theorem size_le (bounds : PolynomialBounds loop) (count : ℕ) (initial : S)
    (i : ℕ) (hi : i ≤ count) :
    Q.size state (next^[i] initial) ≤ bounds.stateSize.eval (Q.size input (count, initial)) :=
  (size_iterate_le bounds.growth bounds.growth_le i initial).trans <|
    Nat.add_le_add (bounds.initialSize_le count initial)
      (Nat.mul_le_mul_right bounds.growth (hi.trans (bounds.count_le count initial)))

end PolynomialBounds

/-- Construct a polynomial realizer from uniform loop code and local step certificates.
The resulting work is count times per-step work at the size envelope, plus administration. -/
def polyRealizer (step : Q.PolyRealizer state state next)
    (loop : IterationCode input step.code) (bounds : PolynomialBounds loop) :
    Q.PolyRealizer input state (fun value => next^[value.1] value.2) where
  code := loop.code
  work := .add (.mul bounds.count (.comp step.work bounds.stateSize)) bounds.overhead
  outputSize := bounds.stateSize
  work_le value := by
    rcases value with ⟨count, initial⟩
    rw [FirstOrderPolynomial.eval_add, FirstOrderPolynomial.eval_mul,
      FirstOrderPolynomial.eval_comp]
    apply (loop.cost_le count initial).trans
    apply Nat.add_le_add _ (bounds.overhead_le count initial)
    exact (iterationWork_le step count initial _ fun i hi =>
      bounds.size_le count initial i (Nat.le_of_lt hi)).trans
        (by
          simpa using Nat.mul_le_mul_right
            (step.work.eval (bounds.stateSize.eval (Q.size input (count, initial))))
            (bounds.count_le count initial))
  outputSize_le value := bounds.size_le value.1 value.2 value.1 le_rfl

end IterationCode

end PFunctor.QuantitativeStepClass
