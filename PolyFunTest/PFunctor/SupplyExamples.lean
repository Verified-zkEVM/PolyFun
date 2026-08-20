/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Supply
public import PolyFunTest.PFunctor.FreeCursorOccurrenceExamples

/-! # Positional answer supply examples

`Supply.run_setAt_eq_run_takeAt_addValues` at concrete data, on the nested example program:
substituting the first `target` answer sends the run down the other branch, and doing so agrees
with rewinding to that answer and resupplying it.
-/

@[expose] public section

open PFunctor

namespace PFunctor.FreeM.Cursor

/-- Enough answers for the branch that asks `target` twice. -/
def exampleSupply : Supply ExampleQuery
  | .noise => [noiseOne]
  | .target => [true, true]

/-- The answer substituted in below, at the type the supply expects. -/
def falseAnswers : List (ExampleQuery.B ExampleOp.target) := [false]

/-- The tail that rewinding discards. -/
def trueAnswers : List (ExampleQuery.B ExampleOp.target) := [true]

/-- As supplied, the program takes the two-`target` branch. -/
example : (Supply.run nestedProgram exampleSupply).map Prod.fst = some 211 := rfl

/-- Substituting the first `target` answer sends it down the other branch, so the substitution is
visible in the output. -/
example : (Supply.run nestedProgram (exampleSupply.setAt ExampleOp.target 0 false)).map Prod.fst
    = some 101 := rfl

/-- Rewinding to that answer and resupplying it reaches the same output. -/
example : (Supply.run nestedProgram
      ((exampleSupply.takeAt ExampleOp.target 0).addValues falseAnswers)).map Prod.fst
    = some 101 := rfl

/-- **The rewind law at concrete data.** The two runs agree, and the substituted run's leftover
supply is the rewound run's plus exactly the tail `takeAt` discarded. -/
example : ∃ s' : Supply ExampleQuery,
    Supply.run nestedProgram ((exampleSupply.takeAt ExampleOp.target 0).addValues falseAnswers)
        = some (101, s') ∧
      Supply.run nestedProgram (exampleSupply.setAt ExampleOp.target 0 false)
        = some (101, s'.addValues trueAnswers) := by
  refine ⟨_, rfl, ?_⟩
  exact Supply.run_setAt_eq_run_takeAt_addValues nestedProgram exampleSupply ExampleOp.target
    false (by decide) rfl

/-- A supply too short for the branch it selects makes the run fail, so `run` really is partial. -/
example : Supply.run nestedProgram (exampleSupply.update ExampleOp.target [true]) = none := rfl

end PFunctor.FreeM.Cursor
