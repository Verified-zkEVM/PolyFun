/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Measure.EvalDist
public import PolyFun.Control.Monad.Measure.EvalDistEq
public import PolyFun.Control.Monad.Measure.WithFailure

/-!
# Measure semantics of monads

Regression tests for `EvalDistSemantics` and its laws over an abstract lawful monad, over the
deterministic carriers `Id`, `Option` and `Except`, and over partial results read through
`Option`. They cover event and failure probabilities, the lossless mixin, equality in distribution
across monads, and instances at universes above `Type`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace PolyFunTest.Probability.EvalDist

/-! ## Deterministic carriers -/

example (x : ℕ) : evalDist (pure x : Id ℕ) = Measure.dirac x := by simp

example (x : ℕ) : evalDist (pure x : Option ℕ) = Measure.dirac x := by simp

example : evalDist (failure : Option ℕ) = 0 := by simp

example : evalDist (Except.error "boom" : Except String ℕ) = 0 := by simp

/-- `Id` is lossless; `Option` is not. -/
example : LosslessEvalDistSemantics Id := inferInstance

example (mx : Id ℕ) : prFail mx = 0 := prFail_eq_zero_of_lossless mx

example (x : ℕ) : prFail (some x) = 0 := prFail_pure x

example : prFail (none : Option ℕ) = 1 := by
  let : MeasurableSpace ℕ := ⊤
  simp [prFail_eq_defect, Measure.defect]

/-- The failure probability is the defect of the output measure in any measurable structure. -/
example [MeasurableSpace ℕ] (mx : Option ℕ) : prFail mx = (evalDist mx).defect :=
  prFail_eq_defect mx

/-- The failure probability through the event `True`. -/
example (mx : Option ℕ) : prFail mx = 1 - prEvent ((fun _ ↦ True) <$> mx) := prFail_def mx

example (mx : Option ℕ) : prEvent ((fun _ ↦ True) <$> mx) + prFail mx = 1 :=
  prEvent_true_add_prFail mx

example (mx : Option ℕ) (f : ℕ → Bool) : prFail (f <$> mx) = prFail mx := prFail_map f mx

example [MeasurableSpace ℕ] : evalDistWithFailure (none : Option ℕ) {none} = 1 := by
  rw [evalDistWithFailure_none_eq_prFail]
  simp [prFail_eq_defect, Measure.defect]

/-! ## A lawful monad

Over an abstract lawful semantics, `simp` closes the structural failure and event laws. -/

section generic

variable {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β : Type}

example (x : α) : prFail (pure x : m α) = 0 := by simp

example (f : α → β) (mx : m α) : prFail (f <$> mx) = prFail mx := by simp

example (mx : m α) : prEvent ((fun _ ↦ True) <$> mx) + prFail mx = 1 := by simp

example (mx : m α) : prEvent ((fun _ ↦ False) <$> mx) = 0 := by simp

example (mx : m α) (p : α → Prop) : prEvent (p <$> mx) ≤ 1 := by simp

end generic

/-! ## Events -/

example : prEvent ((fun n ↦ n = 2) <$> (some 2 : Option ℕ)) = 1 := by simp

example : prEvent ((fun n ↦ n = 2) <$> (Except.ok 3 : Except String ℕ)) = 0 := by simp

example (mx : Option ℕ) (p q : ℕ → Prop) (h : ∀ n, p n → q n) :
    prEvent (p <$> mx) ≤ prEvent (q <$> mx) :=
  prEvent_mono mx p q h

example (mx : Option ℕ) : prEvent ((fun _ ↦ False) <$> mx) = 0 := by simp

/-! ## Equality in distribution -/

/-- Equality in distribution relates computations in different monads. -/
example : EvalDistEq (some 3 : Option ℕ) (pure 3 : Id ℕ) := by
  let : MeasurableSpace ℕ := ⊤
  exact EvalDistEq.of_evalDist_eq (by simp)

example (mx : Option ℕ) {f g : ℕ → Option Bool} (h : ∀ n, EvalDistEq (f n) (g n)) :
    EvalDistEq (mx >>= f) (mx >>= g) :=
  EvalDistEq.bind_right mx h

example {mx my : Option ℕ} (h : EvalDistEq mx my) [MeasurableSpace ℕ] :
    evalDist mx = evalDist my :=
  h.evalDist_eq

/-! ## Partial results -/

example : evalDist (DomainResult.value 3 : DomainResult String ℕ).toOption = Measure.dirac 3 := by
  simp

example : evalDist (⊥ : DomainResult String ℕ).toOption = 0 := by simp

example [MeasurableSpace ℕ] :
    prFail (DomainResult.error "boom" : DomainResult String ℕ).toOption = 1 := by
  rw [DomainResult.prFail_toOption, DomainResult.failureMass_dirac_error]

/-! ## Universes

The deterministic instances name the universe of their results, so they apply above `Type`. -/

noncomputable example : EvalDistSemantics Id.{2} := inferInstance

example : LawfulEvalDistSemantics Option.{1} := inferInstance

example : LawfulEvalDistSemantics (Except.{0, 1} String) := inferInstance

example : LawfulEvalDistSemantics (Except.{1, 0} (ULift.{1} String)) := inferInstance

example {α : Type 1} [MeasurableSpace α] (x : α) : evalDist (some x) = Measure.dirac x :=
  Option.evalDist_some x

example {α : Type 1} (x : α) : prFail (pure x : Id α) = 0 := prFail_eq_zero_of_lossless _

end PolyFunTest.Probability.EvalDist
