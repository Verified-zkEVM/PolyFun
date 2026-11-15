/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Batteries.Control.AlternativeMonad
public import PolyFun.Control.Monad.Measure.Event

/-!
# Successful-output measure of failure

`LawfulFailureEvalDistSemantics` certifies that failure has zero successful-output measure.
This law is independent of attachment, pure and bind.

Failure contributes no successful outputs to a measurable composition. The intermediate
measurable-space choice is internal to the composition laws, so final observations need no source
space. `failure` fails with probability one, and `guard p` fails exactly when `p` does not hold.
-/

public section

open MeasureTheory
open scoped EvalDistSemantics

universe u v

/-- A measure interpretation assigns zero successful-output mass to failure. -/
class LawfulFailureEvalDistSemantics (m : Type u → Type v) [Alternative m]
    [EvalDistSemantics m] : Prop where
  /-- Failure denotes the zero measure. -/
  denote_failure {α : Type u} [MeasurableSpace α] : evalDist (failure : m α) = 0

/-- Failure has zero successful-output measure. -/
@[simp, grind =]
theorem evalDist_failure_eq_zero {m : Type u → Type v} [Alternative m]
    [EvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] : evalDist (failure : m α) = 0 :=
  LawfulFailureEvalDistSemantics.denote_failure

/-! ## Failure in compositions -/

section compositions

variable {m : Type u → Type v} [AlternativeMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
  {α β : Type u} [MeasurableSpace β]

/-- Binding any continuation after failure has zero successful-output measure. -/
@[simp, grind =]
theorem evalDist_failure_bind (f : α → m β) : evalDist ((failure : m α) >>= f) = 0 := by
  let : MeasurableSpace α := ⊤
  rw [evalDist_bind_of_discrete, evalDist_failure_eq_zero, Measure.bind_zero_left]

/-- A continuation that always fails has zero successful-output measure. -/
@[simp↓ high, grind norm↓]
theorem evalDist_bind_failure (mx : m α) :
    evalDist (mx >>= fun _ ↦ (failure : m β)) = 0 := by
  let : MeasurableSpace α := ⊤
  simp

end compositions

/-! ## Events and failure probabilities -/

/-- A failed event computation has probability zero. -/
@[simp, grind =]
theorem prEvent_failure_prop {m : Type → Type v} [AlternativeMonad m]
    [EvalDistSemantics m] [LawfulFailureEvalDistSemantics m] :
    prEvent (failure : m Prop) = 0 := by
  rw [prEvent_def, evalDist_failure_eq_zero]
  rfl

/-- No final event succeeds after failure. -/
@[simp↓ high, grind norm↓]
theorem prEvent_failure {m : Type → Type v} [AlternativeMonad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
    {α : Type} (p : α → Prop) : prEvent (p <$>ₘ (failure : m α)) = 0 := by
  rw [prEvent_def, map_eq_bind_pure_comp]
  simp

/-- `failure` always fails. -/
@[simp, grind =]
theorem prFail_failure {m : Type u → Type v} [AlternativeMonad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
    {α : Type u} : prFail (failure : m α) = 1 := by
  let : MeasurableSpace α := ⊤
  simp [prFail_eq_defect, Measure.defect]

/-- `guard p` fails exactly when `p` does not hold. -/
@[simp]
theorem prFail_guard {m : Type → Type v} [AlternativeMonad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m]
    (p : Prop) [Decidable p] : prFail (guard p : m Unit) = if p then 0 else 1 := by
  by_cases hp : p <;> simp [guard, hp]
