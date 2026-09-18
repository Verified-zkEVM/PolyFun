/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Examples.Parliament.Scenarios
meta import PolyFunTest.Examples.Parliament.Scenarios

/-! # Boundary scenarios and actual PolyFun interpreters -/

open Parliament ParliamentTest

@[expose] public section

namespace ParliamentTest.Edges

def emptyPoll : Scenario Unit := do
  start
  let id ← mainMotion
  send (.openVote 0)
  send (.announce 0)
  check ((← get).events.contains (.decided id false ⟨0, 0⟩)) "empty poll adopted a motion"

def speechClock : Scenario Unit := do
  start
  let _ ← mainMotion
  floorFor 1
  send (.speak 1)
  send (.advanceTime 0 calendar.today 599)
  check ((← get).state.floor.isSome) "speech ended early"
  send (.pointOfOrder 2 "interrupt the speaker" .none)
  send (.advanceTime 0 calendar.today 799)
  ruleOn false
  send (.continueAfterRuling 0)
  check ((← get).state.floor.isSome) "interruption charged speaker time"
  send (.advanceTime 0 calendar.today 800)
  check ((← get).state.floor.isNone) "speech exceeded ten minutes"
  floorFor 1
  send (.speak 1)
  send (.yieldFloor 1)
  floorFor 1
  rejected (.speak 1) .speechLimit
  send (.yieldFloor 1)
  send (.advanceTime 0 ⟨2026, 1, 16⟩ 0)
  floorFor 1
  send (.speak 1)
  send (.yieldFloor 1)
  adopt

def quorumAtDecision : Scenario Unit := do
  start
  let _ ← mainMotion
  send (.openVote 0)
  send (.vote 1 .yes)
  send (.attendance 0 3 false)
  send (.attendance 0 4 false)
  rejected (.announce 0) .noQuorum
  send (.attendance 0 3 true)
  send (.announce 0)
  let _ ← mainMotion
  send (.seekConsent 0)
  send (.attendance 0 3 false)
  rejected (.closeConsent 0) .noQuorum
  send (.attendance 0 3 true)
  send (.closeConsent 0)

def scopedClosure : Scenario Unit := do
  start
  let main ← mainMotion
  let amendment ← move (.primary main ⟨2, 1, ["museum"]⟩)
  let _ ← move (.previousQuestion amendment)
  adopt
  check ((← get).state.pending.all (fun q => q.id != main || !q.closed))
    "scoped closure reached the main motion"
  adopt
  floorFor 1
  send (.speak 1)
  send (.yieldFloor 1)
  adopt

def failedClosure : Scenario Unit := do
  start
  let main ← mainMotion
  let pq ← move (.previousQuestion main)
  send (.openVote 0)
  send (.vote 1 .yes)
  send (.vote 2 .no)
  send (.announce 0)
  check ((← get).events.contains (.decided pq false ⟨1, 1⟩)) "tie closed debate"
  check ((← get).state.activeQuestion.any (fun q => !q.closed)) "failed closure persisted"
  adopt

def appealContinuation : Scenario Unit := do
  start
  let main ← mainMotion
  floorFor 1
  send (.propose 1 (.primary main ⟨2, 1, ["museum"]⟩))
  ruleOn false
  let some r := (← get).state.ruling | throw "missing ruling"
  send (.propose 3 (.appeal r.request.id))
  send (.second 4)
  send (.stateQuestion 0)
  let some appeal := (← get).state.activeQuestion | throw "missing appeal"
  floorFor 1
  rejected (.propose 1 (.refer 7)) .unsupported
  rejected (.propose 1 .adjourn) .unsupported
  send (.propose 1 (.previousQuestion appeal.id))
  send (.lackSecond 0)
  check ((← get).state.ruling.isSome) "unseconded subsidiary erased appeal context"
  floorFor 1
  send (.propose 1 (.previousQuestion appeal.id))
  send (.withdraw 1)
  check ((← get).state.ruling.isSome) "withdrawal erased appeal context"
  send (.openVote 0)
  send (.vote 1 .yes)
  send (.vote 2 .no)
  send (.announce 0)
  adopt

def unfinishedBusiness : Scenario Unit := do
  start
  let main ← mainMotion
  let amendment ← move (.primary main ⟨2, 1, ["museum"]⟩)
  let _ ← move .adjourn
  adopt
  send (.nextMeeting 0 {
    today := ⟨2026, 2, 15⟩, nextRegular := ⟨2026, 3, 15⟩,
    meeting := 1, session := 1 } true)
  for member in [0, 1, 2, 3, 4] do send (.attendance 0 member true)
  send (.openMeeting 0)
  check ((← get).state.businessClass == .unfinished) "lost unfinished order"
  check ((← get).state.activeQuestion.any (fun q => q.id == amendment)) "lost amendment"
  rejected (.advanceBusiness 0) .businessPending
  adopt
  adopt
  send (.advanceBusiness 0)

def duePrecedence : Scenario Unit := do
  start
  let main ← mainMotion
  let _ ← move (.postpone ⟨2026, 1, 16⟩)
  adopt
  send (.advanceTime 0 ⟨2026, 1, 16⟩ 0)
  floorFor 1
  rejected (.propose 1 (.main ["another", "motion"])) .wrongPrecedence
  send (.yieldFloor 1)
  send (.resumeDue 0 main)
  adopt

def recessAcrossMidnight : Scenario Unit := do
  start
  let _ ← move (.recess 100)
  adopt
  rejected (.resumeRecess 0) .notDue
  send (.advanceTime 0 ⟨2026, 1, 16⟩ 0)
  send (.resumeRecess 0)

def rejectedPrefix : IO Unit := do
  let commands : List (Command wordDomain) :=
    [.attendance 0 1 true, .openMeeting 0, .unsupported "reconsider", .attendance 0 2 true]
  match replay rules initial commands with
  | .ok _ => throw (IO.userError "unsupported command accepted")
  | .error error =>
    unless error.index == 2 && error.error == .unsupported &&
        error.acceptedPrefix == commands.take 2 && error.state.present == [1] do
      throw (IO.userError "replay failed to retain the correct accepted prefix")
    match replay rules initial error.acceptedPrefix with
    | .ok (state, events) =>
      unless state == error.state && events == error.events do
        throw (IO.userError "rejected suffix altered the accepted prefix")
    | .error _ => throw (IO.userError "accepted prefix was not replayable")
  IO.println "Replay rejection preserves its accepted prefix and stops before the suffix"

def configuration : IO Unit := do
  match initializeAssembly wordDomain rules roster 0 calendar [7] with
  | .ok state => unless state == initial do throw (IO.userError "wrong initial state")
  | .error _ => throw (IO.userError "valid configuration rejected")
  for invalid in [initializeAssembly wordDomain { rules with quorum := 0 } roster 0 calendar,
      initializeAssembly wordDomain rules (roster ++ roster) 0 calendar,
      initializeAssembly wordDomain rules roster 0 { calendar with today := ⟨2026, 2, 30⟩ },
      initializeAssembly wordDomain rules roster 0 calendar [7, 7]] do
    match invalid with
    | .error .invalidConfiguration => pure ()
    | _ => throw (IO.userError "invalid configuration accepted")
  IO.println "Initialization rejects duplicate identities, invalid dates, and zero quorum"

-- This interpreter consumes raw commands through PolyFun's actual IFreeM monadic fold.
def scriptedInput (s : AssemblyState wordDomain) :
    StateT (List (Command wordDomain)) (Except String) (EnabledInput rules s) := do
  let commands ← get
  let command :: rest := commands | throw "script exhausted"
  set rest
  match checkInput rules s command with
  | .error error => throw s!"script rejected: {repr error}"
  | .ok input => pure input

def polyfunReplay : IO Unit := do
  let .ok (_, run) := amendment.run {} | throw (IO.userError "setup failed")
  let script := boundedScript rules run.commands.length initial
  match (script.interpret scriptedInput).run run.commands with
  | .error error => throw (IO.userError error)
  | .ok (result, remaining) =>
    unless result.1 == run.state && remaining.isEmpty do
      throw (IO.userError "PolyFun script diverged from replay")
  IO.println "PolyFun IFreeM interpreter agrees with amendment journal"

def openHandler : IO Unit := do
  let setup : Scenario Unit := do
    start
    floorFor 1
    send (.propose 1 (.main ["plant", "trees"]))
  let .ok (_, run) := setup.run {} | throw (IO.userError "setup failed")
  let allowed := answerInput rules run.state
    (m := Id) (fun _ => pure ⟨⟨true, "human accepts"⟩⟩)
  let denied := answerInput rules run.state
    (m := Id) (fun _ => pure ⟨⟨false, "human rejects"⟩⟩)
  match allowed, denied with
  | .ok yes, .ok no =>
    unless yes.next.ruling.any (fun r => r.answer.allowed) &&
        no.next.ruling.any (fun r => !r.answer.allowed) do
      throw (IO.userError "handler responses were not recorded independently")
  | _, _ => throw (IO.userError "valid external reply rejected")
  IO.println "Open judgment handlers accept both external answers without semantic axioms"

#eval runScenario "empty poll" emptyPoll
#eval runScenario "speech clock and interruption" speechClock
#eval runScenario "quorum at decision" quorumAtDecision
#eval runScenario "scoped closure" scopedClosure
#eval runScenario "failed closure" failedClosure
#eval runScenario "appeal continuation" appealContinuation
#eval runScenario "unfinished business" unfinishedBusiness
#eval runScenario "due business precedence" duePrecedence
#eval runScenario "recess across midnight" recessAcrossMidnight
#eval polyfunReplay
#eval openHandler
#eval rejectedPrefix
#eval configuration

end ParliamentTest.Edges
