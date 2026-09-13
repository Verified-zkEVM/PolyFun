/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Iteration

/-!
# Bounded-iteration arithmetic regressions

The test backend deliberately supplies only a cost function. It isolates the resource algebra;
it carries no computability claim. Incrementing state makes successive invocations more expensive,
and loop control is charged even when the iteration count is zero. Negative checks reject size
doubling under a constant additive-growth premise and a representation that erases the count.
-/

public section

namespace PFunctor.IterationTest

open QuantitativeStepClass _root_.Complexity

/-- Test representations explicitly select their natural-number size function. -/
@[expose] def sizes : StepClass where
  Str A := A → ℕ
  Hom _ _ _ := True
  id_mem _ := trivial
  comp_mem _ _ := trivial

/-- Arithmetic-only fixture whose code records a cost on each input. -/
@[expose] def metered : QuantitativeStepClass sizes where
  Realizer {A} {_B} _ _ _ := A → ℕ
  size rep value := rep value
  cost code value := code value
  admissible _ := trivial

/-- Increment one state, paying its successor size. -/
@[expose] def increment : metered.PolyRealizer id id Nat.succ where
  code := Nat.succ
  work := .add .input (.const 1)
  outputSize := .add .input (.const 1)
  work_le _ := le_rfl
  outputSize_le _ := le_rfl

/-- The encoded loop input accounts for both its count and initial state. -/
@[expose] def inputSize (input : ℕ × ℕ) : ℕ := input.1 + input.2 + 1

/-- Charge the entire arithmetic step trace and one loop-control unit per iteration plus setup. -/
@[expose] def loop : IterationCode (Q := metered) inputSize increment.code where
  code value := iterationWork increment.code value.1 value.2 + (value.1 + 1)
  overhead n _ := n + 1
  cost_le _ _ := le_rfl

/-- Linear count and state envelopes with additive one-unit size growth. -/
@[expose] def bounds : loop.PolynomialBounds where
  count := .input
  initialSize := .input
  overhead := .add .input (.const 1)
  growth := 1
  count_le n value := by change n ≤ n + value + 1; omega
  initialSize_le n value := by change value ≤ n + value + 1; omega
  growth_le _ := le_rfl
  overhead_le n value := by change n + 1 ≤ n + value + 1 + 1; omega

/-- Three iterations from state two charge different step costs: `3 + 4 + 5 + 4`. -/
example : metered.cost loop.code (3, 2) = 16 := by decide

/-- Zero iterations still incur the loop setup cost. -/
example : metered.cost loop.code (0, 2) = 1 := by decide

/-- The generic constructor certifies the same uniform iterator. -/
example : metered.PolyRealizer inputSize id (fun value => Nat.succ^[value.1] value.2) :=
  IterationCode.polyRealizer increment loop bounds

/-- Every prefix has a bounded state size, including the final one. -/
example (count initial i : ℕ) (hi : i ≤ count) :
    Nat.succ^[i] initial ≤ 2 * (count + initial + 1) := by
  have h := bounds.size_le count initial i hi
  simpa [IterationCode.PolynomialBounds.stateSize, bounds, metered, inputSize,
    two_mul] using h

/-- Size doubling cannot satisfy any fixed additive one-step growth allowance. -/
example (growth : ℕ) : ¬∀ size : ℕ, 2 * size ≤ size + growth := by
  intro h
  have := h (growth + 1)
  omega

/-- Erasing the count from the input size defeats every proposed uniform count polynomial. -/
example (p : FirstOrderPolynomial) : ¬∀ count initial : ℕ, count ≤ p.eval (initial + 1) := by
  intro h
  have hbad := h (p.eval 1 + 1) 0
  simp at hbad

end PFunctor.IterationTest
