/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Parliament
meta import Parliament

/-! # Nonempty paths and handler instrumentation of the actual meeting application -/

public section

namespace ParliamentTest.Walkthrough

open Parliament Parliament.App Parliament.Walkthrough

/-- The introductory form distinguishes parsing, domain rejection, and certified updates. -/
def checkAttendanceForm : IO Unit := do
  let config := exampleConfiguration
  let .ok journal := config.start | throw (IO.userError "invalid initial configuration")
  let run (lines : List String) :=
    ((checkedAttendance config.rules journal.state).interpret
      PolyFunIO.consoleMemoryHandler).run { input := lines }
  let (.ok (.ok input), console) := run [" 0 ", "1", "yes", "unused"]
    | throw (IO.userError "valid attendance form failed")
  unless input.command == .attendance 0 1 true && input.next.isPresent 1 &&
      input.next.revision == journal.state.revision + 1 &&
      console.input == ["unused"] &&
      console.output == #["Chair ID: ", "Member ID: ", "Present (yes/no): "] do
    throw (IO.userError "attendance form lost its typed input or effects")
  let (.ok (.error .notMember), _) := run ["1", "1", "yes"]
    | throw (IO.userError "parsing incorrectly conferred chair authority")
  let (.error (.invalid _), invalid) := run ["not a number", "unused"]
    | throw (IO.userError "invalid input reached the domain checker")
  unless invalid.input == ["unused"] && invalid.output == #["Chair ID: "] do
    throw (IO.userError "invalid form consumed later fields")
  for lines in [[], ["0"], ["0", "1"]] do
    let (.error .endOfInput, _) := run lines
      | throw (IO.userError "partial form submitted a command")
  IO.println "checkAttendanceForm: ok"

/-- info: checkAttendanceForm: ok -/
#guard_msgs in
#eval checkAttendanceForm

/-- Exercise the bridges on an accepted command and a real application effect sequence. -/
def checkBridges : IO Unit := do
  let config := exampleConfiguration
  let .ok journal := config.start | throw (IO.userError "invalid initial configuration")
  let command := Command.attendance 0 1 true
  let .ok input := checkInput config.rules journal.state command
    | throw (IO.userError "attendance should be legal")
  let path := MeetingPath.cons input (MeetingPath.nil input.next)
  let orbit := toPrefix path
  unless orbit.last == input.next && orbit.events commandLabel == [command] &&
      (orbit.events receiptLabel).flatten == input.events do
    throw (IO.userError "generic prefix lost a domain observation")
  let backend : Memory := { actions := [.command command, .quit] }
  let ((result, log), final) :=
    (((application config).runChunk (loggedHandler config) 100 (.ready journal)).run).run backend
  let .done exit := result | throw (IO.userError "instrumented application did not finish")
  unless exit.code == 0 && final.persistCount == 1 && final.publishCount == 1 &&
      log == [.read, .persist, .tell, .read, .publish, .tell] do
    throw (IO.userError "instrumentation changed or lost an application interaction")
  let ((failure, failedLog), failed) :=
    (((application config).runChunk (loggedHandler config) 100 (.ready journal)).run).run
      { backend with failPersistAt := some 1 }
  let .done exit := failure | throw (IO.userError "failed instrumented application did not stop")
  unless exit.code == 1 && exit.journal.state.revision == 0 && failed.persistCount == 1 &&
      failedLog == [.read, .persist, .tell] do
    throw (IO.userError "instrumentation changed failure behavior")
  IO.println "checkBridges: ok"

/-- info: checkBridges: ok -/
#guard_msgs in
#eval checkBridges

end ParliamentTest.Walkthrough
