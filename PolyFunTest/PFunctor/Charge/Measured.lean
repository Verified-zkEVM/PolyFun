/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Measured

/-!
# Measured and budgeted programs

Checks for `PolyFun.PFunctor.Free.Cost.Measured`:

* a measured program composed with itself computes the composite and adds budgets;
* budgeted programs compose into a budgeted program for the composite function;
* free programs within budget form a graded monad.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargeMeasured

/-- One operation that answers with its input plus one. -/
def incr : MeasuredProgram ℕ ℕ ℕ where
  View := ℕ
  view := id
  Op := Unit
  Ans _ _ := ℕ
  program _ := FreeM.lift (P := ⟨Unit, fun _ => ℕ⟩) ()
  answer v _ := v + 1
  cost _ := 1

example (i : ℕ) : (incr.comp incr).run i = i + 2 := by
  rw [MeasuredProgram.run_comp]
  rfl

theorem incr_realizes : incr.Realizes (· + 1) := fun _ => rfl

theorem incr_cost : incr.CostAtMost 1 := by
  intro v p
  rcases p with ⟨b, ⟨⟩⟩
  exact le_rfl

example : (incr.comp incr).CostAtMost 2 :=
  MeasuredProgram.CostAtMost.comp incr_cost incr_cost

/-- Two increments, as a budgeted program with budget `2`. -/
def addTwo : BudgetedProgram ((· + 1) ∘ (· + 1) : ℕ → ℕ) ℕ :=
  BudgetedProgram.comp ⟨incr, 1, incr_realizes, incr_cost⟩ ⟨incr, 1, incr_realizes, incr_cost⟩

example : addTwo.budget = 2 := rfl

example : (BudgetedProgram.ofFun (ω := ℕ) (fun n : ℕ => n * 2)).budget = 0 := rfl

/-! ## Budgeted carriers -/

abbrev Keys : PFunctor.{0, 0} := ⟨ℕ, fun _ => Bool⟩

example (c : Keys.A → ℕ) (x : Budgeted c (Multiplicative.ofAdd 1) Bool)
    (f : Bool → Budgeted c (Multiplicative.ofAdd 2) Bool) :
    Budgeted c (Multiplicative.ofAdd 1 * Multiplicative.ofAdd 2) Bool :=
  GradedMonad.gbind x f

end PolyFunTest.ChargeMeasured
