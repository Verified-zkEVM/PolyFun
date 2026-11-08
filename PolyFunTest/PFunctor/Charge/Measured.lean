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
* budgeted programs compose into a budgeted program for the composite function, and the
  existential form of a cost statement is trivial;
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
  spec _ _ := ℕ
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

/-- The one call is charged: no smaller budget holds. -/
example : ¬ incr.CostAtMost 0 := fun h => absurd (h (0 : ℕ) ⟨(0 : ℕ), ⟨⟩⟩) (by decide)

/-- The run is the output of the path the answers pick, and precomposing a map on inputs keeps the
budget. -/
example (i : ℕ) :
    incr.run i = FreeM.output (incr.program i) (FreeM.Path.ofHandler (incr.answer i) _) :=
  incr.run_eq_output i

example : ((incr.contramap (· * 2)).Realizes fun n => n * 2 + 1) ∧
    (incr.contramap (· * 2)).CostAtMost 1 :=
  ⟨incr_realizes.contramap _, incr_cost.contramap _⟩

/-- Two increments, as a budgeted program with budget `2`. -/
def addTwo : BudgetedProgram ((· + 1) ∘ (· + 1) : ℕ → ℕ) ℕ :=
  BudgetedProgram.comp ⟨incr, 1, incr_realizes, incr_cost⟩ ⟨incr, 1, incr_realizes, incr_cost⟩

example : addTwo.budget = 2 := rfl

example : (BudgetedProgram.ofFun (ω := ℕ) (fun n : ℕ => n * 2)).budget = 0 := rfl

/-! ## Stages along a path

An acceptance test after ArkLib's `MeasuredStages.programAlong`, which composes per-stage budgeted
programs along an execution path, starting from the zero-stage `BudgetedProgram.ofFun`. -/

/-- One budgeted increment: a stage of budget `1`. -/
def incrStage : BudgetedProgram (· + 1 : ℕ → ℕ) ℕ := ⟨incr, 1, incr_realizes, incr_cost⟩

/-- `k` increment stages composed along a path of length `k`: the composite computes `+ k`. -/
def stagesAlong : (k : ℕ) → BudgetedProgram (fun n : ℕ => n + k) ℕ
  | 0 => BudgetedProgram.ofFun id
  | k + 1 => incrStage.comp (stagesAlong k)

/-- The declared budgets add along the path. -/
theorem stagesAlong_budget (k : ℕ) : (stagesAlong k).budget = k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (· + 1) ih

/-- Uniform stage budgets give the path-length bound, on every completed path of the composite. -/
example (k : ℕ) : (stagesAlong k).program.CostAtMost (k • 1) :=
  (stagesAlong k).costAtMost.mono (by rw [stagesAlong_budget, smul_eq_mul, mul_one])

/-- The composite computes the composed function. -/
example (k n : ℕ) : (stagesAlong k).program.run n = n + k :=
  ((stagesAlong k).realizes n).symm

/-- Quantifying over measured programs proves nothing: every function has one at cost `0`, because
the view, the answers and the code between calls are uncharged. Statements name the program. -/
example (f : ℕ → ℕ) : ∃ M : MeasuredProgram ℕ ℕ ℕ, M.Realizes f ∧ M.CostAtMost 0 :=
  ⟨MeasuredProgram.ofFun f, MeasuredProgram.realizes_ofFun f, MeasuredProgram.costAtMost_ofFun f⟩

/-! ## Budgeted carriers -/

abbrev Keys : PFunctor.{0, 0} := ⟨ℕ, fun _ => Bool⟩

example (c : Keys.A → ℕ) (x : Budgeted c (Multiplicative.ofAdd 1) Bool)
    (f : Bool → Budgeted c (Multiplicative.ofAdd 2) Bool) :
    Budgeted c (Multiplicative.ofAdd 1 * Multiplicative.ofAdd 2) Bool :=
  GradedMonad.gbind x f

end PolyFunTest.ChargeMeasured
