/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Notes.Walkthrough
meta import Notes.Walkthrough

/-! # Independent expected outputs for all six executable representations -/

public section

open Notes.Walkthrough PolyFunIO PFunctor PFunctor.DynSystem

/-- Every representation must consume one line, issue one prompt, and preserve exact text. -/
def representationTests : IO Unit := do
  for model in Model.all do
    let (result, memory) := (run model consoleMemoryHandler).run { input := ["  α  ", "unused"] }
    unless result == .ok (some "  α  ") && memory.input == ["unused"] &&
        memory.output == #["Note: "] do
      throw (IO.userError s!"{model.name}: wrong result or effects")
    let (result, memory) := (run model consoleMemoryHandler).run {}
    unless result == .ok none && memory.output == #["Note: "] do
      throw (IO.userError s!"{model.name}: wrong EOF behavior")
    for (input, expected) in [
        (["0", "0", "  replacement α  ", "save"],
          Except.ok (some (Notes.Command.edit 0 0 "  replacement α  "))),
        (["0", "0", "cancelled", "cancel"], .ok none),
        (["0", "0", "unfinished"], .error .endOfInput),
        (["0", "1", "stale"], .error (.invalid
          "Stale edit: expected version 1, but the current version is 0."))] do
      let (answer, memory) := (runEdit model consoleMemoryHandler).run { input }
      let (_, reference) := (runEdit .free consoleMemoryHandler).run { input }
      unless answer == .ok expected && memory.output == reference.output && memory.input.isEmpty do
        throw (IO.userError s!"{model.name}: edit workflow changed answers or visible effects")
  let (first, memory) := (ITree.machine.runChunk (ITree.withSilentSteps consoleMemoryHandler)
    1 tree.toResumptionWithTau).run { input := ["later"] }
  let .paused residual := first | throw (IO.userError "tau budget falsely reported completion")
  unless memory.output.isEmpty && memory.input == ["later"] do
    throw (IO.userError "tau called the console handler")
  let (second, memory) :=
    (ITree.machine.runChunk (ITree.withSilentSteps consoleMemoryHandler) 1 residual).run memory
  let .done (some "later") := second | throw (IO.userError "tau residual lost its continuation")
  unless memory.output == #["Note: "] do throw (IO.userError "resume duplicated the prompt")
  let silent : ITree Console Unit := ITree.diverge
  let (silentResult, silentMemory) := (ITree.machine.runChunk
    (ITree.withSilentSteps consoleMemoryHandler) 8 silent.toResumptionWithTau).run {}
  match silentResult with
  | .done _ => throw (IO.userError "infinite silence was mistaken for completion")
  | .paused _ => pure ()
  unless silentMemory.output.isEmpty do throw (IO.userError "infinite silence prompted")
  let (some view, memory) := (branch.liftM consoleMemoryHandler).run {
    input := ["original", "first edit", "second edit"] }
    | throw (IO.userError "missing edit occurrence")
  unless FreeM.output branchProgram view.firstPath == ("original", "first edit") &&
      FreeM.output branchProgram view.secondPath == ("original", "second edit") &&
      memory.output == #["Original: ", "Edit: ", "Edit: "] do
    throw (IO.userError "branch did not retain its shared prefix")
  let program := (Notes.Preview.form demoNotebook).run
  let (some choices, memory) := ((Notes.Preview.compare demoNotebook).liftM
    consoleMemoryHandler).run { input := ["0", "0", "proposed", "unused"] }
    | throw (IO.userError "missing preview decision")
  unless FreeM.output program choices.firstPath == .ok (some (.edit 0 0 "proposed")) &&
      FreeM.output program choices.secondPath == .ok none && memory.input == ["unused"] &&
      memory.output.size == 4 do
    throw (IO.userError "explicit fork repeated preparation or requested a decision")
  IO.println "Six representations and shared-prefix branching: ok"

/-- info: Six representations and shared-prefix branching: ok -/
#guard_msgs in
#eval representationTests

-- The protocol cannot request another operation after completion.
/-- error: Application type mismatch: The argument
  ()
has type
  Unit
but is expected to have type
  EditProtocol.A EditPhase.done
in the application
  IPFunctor.FreeM.lift EditPhase.done () -/
#guard_msgs in
example := IPFunctor.FreeM.lift (P := EditProtocol) EditPhase.done ()
