/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Supply.Trace
public import PolyFunTest.PFunctor.SupplyExamples

/-! # What a run against a supply reads — examples

`exampleSupply` answers `target` with `[true, true]`, so the run takes the branch that asks
`target` twice. Substituting the first of those answers sends it down the branch that asks only
once, so the substituted run reads a *shorter* trace — which is what makes the statements below
about the untouched positions worth checking rather than reading off a common prefix.
-/

@[expose] public section

open PFunctor

namespace PFunctor.FreeM.Cursor

/-- The path the supply selects. -/
example : (Supply.runPath nestedProgram exampleSupply).map Prod.fst
    = some nestedTrueTruePath := rfl

/-- `run` is `runPath` with the path forgotten. -/
example : Supply.run nestedProgram exampleSupply
    = (Supply.runPath nestedProgram exampleSupply).map fun r =>
        (output nestedProgram r.1, r.2) :=
  Supply.run_eq_map_runPath nestedProgram exampleSupply

/-- Its trace: one `noise` event and two `target` events. -/
example : Path.trace nestedProgram nestedTrueTruePath
    = [(⟨ExampleOp.noise, noiseOne⟩ : ExampleQuery.Idx),
      ⟨ExampleOp.target, true⟩, ⟨ExampleOp.target, true⟩] := rfl

example : PFunctor.TraceList.occurrences ExampleOp.target
    (Path.trace nestedProgram nestedTrueTruePath) = 2 := by decide

/-- **The bridge at concrete data.** The answer taken at the second `target` occurrence is the
supply's second `target` answer. -/
example : PFunctor.TraceList.getAt? (Path.trace nestedProgram nestedTrueTruePath)
      ExampleOp.target 1 = (exampleSupply ExampleOp.target)[1]? := by
  obtain ⟨s', hs'⟩ : ∃ s', Supply.runPath nestedProgram exampleSupply
      = some (nestedTrueTruePath, s') := ⟨_, rfl⟩
  exact Supply.getAt?_trace_runPath nestedProgram ExampleOp.target 1 exampleSupply s'
    nestedTrueTruePath hs' (by decide)

/-! ## Substituting one answer -/

/-- Substituting the first `target` answer sends the run down the shorter branch. -/
example : (Supply.runPath nestedProgram
      (exampleSupply.setAt ExampleOp.target 0 false)).map Prod.fst
    = some nestedFalsePath := rfl

/-- That branch reads only one `target` answer, so the substituted supply's second answer is never
looked at. -/
example : PFunctor.TraceList.occurrences ExampleOp.target
    (Path.trace nestedProgram nestedFalsePath) = 1 := by decide

/-- **Substituting the supply substitutes the trace.** -/
example : PFunctor.TraceList.getAt? (Path.trace nestedProgram nestedFalsePath)
      ExampleOp.target 0 = some false := by
  obtain ⟨s', hs'⟩ : ∃ s', Supply.runPath nestedProgram
      (exampleSupply.setAt ExampleOp.target 0 false) = some (nestedFalsePath, s') := ⟨_, rfl⟩
  exact Supply.getAt?_trace_runPath_setAt (by decide) hs' (by decide)

/-- **And leaves every other position alone.** The `noise` answer is still the supply's own, even
though the substituted run follows a different branch from here on. -/
example : PFunctor.TraceList.getAt? (Path.trace nestedProgram nestedFalsePath)
      ExampleOp.noise 0 = (exampleSupply ExampleOp.noise)[0]? := by
  obtain ⟨s', hs'⟩ : ∃ s', Supply.runPath nestedProgram
      (exampleSupply.setAt ExampleOp.target 0 false) = some (nestedFalsePath, s') := ⟨_, rfl⟩
  exact Supply.getAt?_trace_runPath_setAt_of_pos_ne (by decide) hs' (by decide)

/-- The completion the occurrence layer builds from that same substituted answer carries it at the
same index, so the two accounts of "the answer at occurrence `0` of `target`" agree. -/
example : PFunctor.TraceList.getAt? (Path.trace nestedProgram nestedFork.first.path)
      ExampleOp.target 0 = PFunctor.TraceList.getAt?
        (Path.trace nestedProgram nestedFalsePath) ExampleOp.target 0 := rfl

/-! ## What the run consumed -/

/-- The shorter run leaves one `target` answer behind, and the accounting lemma says so. -/
example : ∀ s' : Supply ExampleQuery, Supply.runPath nestedProgram
      (exampleSupply.setAt ExampleOp.target 0 false) = some (nestedFalsePath, s') →
    (s' ExampleOp.target).length + 1 = 2 := by
  intro s' h
  have hlen := Supply.length_add_occurrences h ExampleOp.target
  rw [show PFunctor.TraceList.occurrences ExampleOp.target
      (Path.trace nestedProgram nestedFalsePath) = 1 from by decide,
    show ((exampleSupply.setAt ExampleOp.target 0 false) ExampleOp.target).length = 2 from rfl]
    at hlen
  exact hlen

end PFunctor.FreeM.Cursor
