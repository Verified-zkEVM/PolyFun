/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament
meta import Examples.Parliament

/-! # Executable, replay-checked meeting scenarios -/

open Parliament

@[expose] public section

namespace ParliamentTest

def rules : Rules := { quorum := 4 }
def calendar : Calendar :=
  { today := ⟨2026, 1, 15⟩, nextRegular := ⟨2026, 2, 15⟩ }
def roster : List Member := [⟨0, true, true⟩, ⟨1, true, true⟩,
  ⟨2, true, true⟩, ⟨3, true, true⟩, ⟨4, true, true⟩]

def initial : AssemblyState wordDomain :=
  { members := roster, chair := 0, calendar, committees := [7] }

structure Run where
  state : AssemblyState wordDomain := initial
  commands : List (Command wordDomain) := []
  events : List Event := []

abbrev Scenario := StateT Run (Except String)

def send (command : Command wordDomain) : Scenario Unit := do
  let run ← get
  match step rules run.state command with
  | .error error => throw s!"command {run.commands.length}: {repr error}"
  | .ok (state, events) =>
    set ({ state, commands := run.commands ++ [command], events := run.events ++ events } : Run)

def check (condition : Bool) (message : String) : Scenario Unit :=
  if condition then pure () else throw message

def rejected (command : Command wordDomain) (expected : RuleError) : Scenario Unit := do
  let run ← get
  match step rules run.state command with
  | .ok _ => throw s!"expected rejection {repr expected}"
  | .error error => check (error == expected) s!"expected {repr expected}, got {repr error}"

def start : Scenario Unit := do
  for member in [0, 1, 2, 3, 4] do send (.attendance 0 member true)
  send (.openMeeting 0)
  send (.advanceBusiness 0)
  send (.advanceBusiness 0)

def floorFor (member : MemberId) : Scenario Unit := do
  send (.requestFloor member)
  send (.recognize 0 member)

def ruleOn (allowed : Bool) : Scenario Unit := do
  let s := (← get).state
  let some request := s.judgment | throw "no judgment request"
  send (.answerJudgment 0 request.id request.revision ⟨allowed, "scripted ruling"⟩)

def approve : Scenario Unit := do
  ruleOn true
  send (.continueAfterRuling 0)

def move (motion : Motion wordDomain) (actor : MemberId := 1) : Scenario QuestionId := do
  floorFor actor
  send (.propose actor motion)
  let some q := (← get).state.proposal | throw "no proposal"
  send (.second (if actor == 2 then 3 else 2))
  if (← get).state.judgment.isSome then approve
  send (.stateQuestion 0)
  pure q.id

def mainMotion : Scenario QuestionId := move (.main ["fund", "the", "library"])

def adopt : Scenario Unit := do
  send (.openVote 0)
  send (.vote 1 .yes)
  send (.vote 2 .yes)
  send (.vote 3 .no)
  send (.announce 0)

def consent : Scenario Unit := do
  send (.seekConsent 0)
  send (.closeConsent 0)

def basic : Scenario Unit := do
  start
  let id ← mainMotion
  floorFor 1
  send (.speak 1)
  rejected (.speak 1) .duplicate
  send (.yieldFloor 1)
  send (.openVote 0)
  send (.vote 1 .yes)
  send (.vote 1 .no)
  send (.vote 1 .yes)
  send (.vote 2 .yes)
  send (.vote 3 .abstain)
  send (.announce 0)
  check ((← get).state.pending.isEmpty) "main motion remained pending"
  check ((← get).events.contains (.decided id true ⟨2, 0⟩)) "wrong tally"

def amendment : Scenario Unit := do
  start
  let main ← mainMotion
  let primary ← move (.primary main ⟨2, 1, ["museum"]⟩)
  let secondary ← move (.secondary primary (.wording ⟨0, 1, ["school"]⟩))
  floorFor 1
  rejected (.propose 1 (.secondary secondary (.wording ⟨0, 1, ["park"]⟩))) .invalidAmendment
  send (.yieldFloor 1)
  adopt
  adopt
  let some q := (← get).state.activeQuestion | throw "missing main motion"
  check (q.motion == .main ["fund", "the", "school"]) "amendment application was wrong"
  adopt

def missingSecond : Scenario Unit := do
  start
  floorFor 1
  send (.propose 1 (.main ["plant", "trees"]))
  approve
  rejected (.stateQuestion 0) .needsSecond
  rejected (.second 1) .alreadySeconded
  send (.lackSecond 0)
  check ((← get).state.proposal.isNone) "unseconded proposal remained"

def debateClosure : Scenario Unit := do
  start
  let main ← mainMotion
  floorFor 1
  rejected (.openVote 0) .floorOccupied
  send (.yieldFloor 1)
  send (.requestFloor 2)
  rejected (.openVote 0) .pendingSpeakers
  send (.recognize 0 2)
  send (.propose 2 (.previousQuestion main))
  send (.second 3)
  send (.stateQuestion 0)
  adopt
  let some q := (← get).state.activeQuestion | throw "missing main"
  check q.closed "Previous Question did not close debate"
  floorFor 1
  rejected (.speak 1) .debateClosed
  send (.yieldFloor 1)
  adopt

def consentObjection : Scenario Unit := do
  start
  let _ ← mainMotion
  send (.seekConsent 0)
  send (.object 3)
  rejected (.closeConsent 0) .wrongPhase
  check ((← get).state.phase == .business) "objection did not resume ordinary procedure"
  adopt

def appeal : Scenario Unit := do
  start
  let main ← mainMotion
  floorFor 1
  send (.propose 1 (.primary main ⟨2, 1, ["museum"]⟩))
  send (.second 2)
  ruleOn false
  let some r := (← get).state.ruling | throw "missing ruling"
  send (.propose 3 (.appeal r.request.id))
  send (.second 4)
  send (.stateQuestion 0)
  send (.openVote 0)
  send (.vote 1 .no)
  send (.vote 2 .no)
  send (.vote 3 .yes)
  send (.announce 0)
  let some proposal := (← get).state.proposal | throw "appeal lost original proposal"
  check proposal.approved "appeal failed to reverse ruling"
  send (.stateQuestion 0)
  adopt
  adopt
  rejected (.propose 3 (.appeal r.request.id)) .tooLate

def appealTie : Scenario Unit := do
  start
  let main ← mainMotion
  floorFor 1
  send (.propose 1 (.primary main ⟨2, 1, ["museum"]⟩))
  ruleOn false
  let some r := (← get).state.ruling | throw "missing ruling"
  send (.propose 3 (.appeal r.request.id))
  send (.second 4)
  send (.stateQuestion 0)
  send (.openVote 0)
  send (.vote 1 .yes)
  send (.vote 2 .no)
  send (.announce 0)
  check ((← get).state.proposal.isNone) "tie did not sustain rejection"

def interruption : Scenario Unit := do
  start
  let _ ← mainMotion
  floorFor 1
  send (.speak 1)
  send (.pointOfOrder 3 "speaker's relevance" .releaseFloor)
  check ((← get).state.floor.isNone) "interruption did not suspend floor"
  ruleOn false
  send (.continueAfterRuling 0)
  check ((← get).state.floor.any (fun f => f.member == 1 && f.speaking))
    "floor was not restored"
  send (.yieldFloor 1)
  adopt

def staleJudgment : Scenario Unit := do
  start
  floorFor 1
  send (.propose 1 (.main ["plant", "trees"]))
  let some request := (← get).state.judgment | throw "missing request"
  rejected (.answerJudgment 0 request.id (request.revision + 1) ⟨true, "stale"⟩) .staleJudgment
  send (.withdraw 1)
  rejected (.answerJudgment 0 request.id request.revision ⟨true, "stale"⟩) .staleJudgment

def quorumLoss : Scenario Unit := do
  start
  let _ ← mainMotion
  send (.attendance 0 3 false)
  send (.attendance 0 4 false)
  rejected (.openVote 0) .noQuorum
  let _ ← move (.recess 100) 1
  send (.openVote 0)
  send (.vote 1 .yes)
  send (.announce 0)
  check ((← get).state.phase == .recessed) "no-quorum recess failed"
  send (.advanceTime 0 calendar.today 100)
  send (.resumeRecess 0)
  send (.attendance 0 3 true)
  send (.openVote 0)
  send (.vote 1 .yes)
  send (.vote 2 .yes)
  send (.announce 0)

def tableRestore : Scenario Unit := do
  start
  let main ← mainMotion
  let primary ← move (.primary main ⟨2, 1, ["museum"]⟩)
  let _ ← move .table
  adopt
  check ((← get).state.pending.isEmpty) "table did not suspend"
  let _ ← move (.takeFromTable main)
  adopt
  check ((← get).state.activeQuestion.any (fun q => q.id == primary))
    "table lost attached amendment"
  adopt
  adopt

def committeeReport : Scenario Unit := do
  start
  let main ← mainMotion
  let primary ← move (.primary main ⟨2, 1, ["museum"]⟩)
  let _ ← move (.refer 7)
  adopt
  rejected (.report 0 8 main) .wrongTarget
  send (.report 0 7 main)
  check ((← get).state.activeQuestion.any (fun q => q.id == primary))
    "committee report lost pending amendment"
  adopt
  adopt

def postponement : Scenario Unit := do
  start
  let main ← mainMotion
  let _ ← move (.postpone ⟨2026, 1, 16⟩)
  adopt
  rejected (.resumeDue 0 main) .notDue
  send (.advanceTime 0 ⟨2026, 1, 16⟩ 0)
  send (.resumeDue 0 main)
  adopt

def withdrawal : Scenario Unit := do
  start
  let main ← mainMotion
  send (.withdraw 1)
  send (.stateQuestion 0)
  consent
  check ((← get).state.pending.isEmpty) "withdrawal failed"
  check ((← get).events.contains (.withdrawn main)) "missing withdrawal event"

def chairVote : Scenario Unit := do
  start
  let _ ← mainMotion
  send (.openVote 0)
  send (.vote 1 .yes)
  send (.vote 2 .no)
  send (.vote 0 .yes)
  send (.announce 0)
  let _ ← mainMotion
  send (.openVote 0)
  send (.vote 1 .yes)
  send (.vote 2 .yes)
  send (.vote 0 .yes)
  rejected (.announce 0) .chairVoteIrrelevant
  send (.vote 0 .abstain)
  send (.announce 0)

def sessionExpiration : Scenario Unit := do
  start
  let main ← mainMotion
  let _ ← move .table
  adopt
  let _ ← move .adjourn
  adopt
  send (.nextMeeting 0 {
    today := ⟨2026, 2, 15⟩, nextRegular := ⟨2026, 3, 15⟩,
    meeting := 1, session := 1 } true)
  start
  check ((← get).state.suspended.any (fun b => b.id == main)) "premature expiration"
  let _ ← move .adjourn
  adopt
  send (.nextMeeting 0 {
    today := ⟨2026, 3, 15⟩, nextRegular := ⟨2026, 4, 15⟩,
    meeting := 2, session := 2 } true)
  check ((← get).state.suspended.isEmpty) "expired tabled item survived"
  check ((← get).events.contains (.expired main)) "missing expiry event"

def runScenario (name : String) (scenario : Scenario Unit) : IO Unit := do
  match scenario.run {} with
  | .error error => throw (IO.userError s!"{name}: {error}")
  | .ok (_, run) =>
    match replay rules initial run.commands with
    | .error error => throw (IO.userError s!"{name}: replay rejected at {error.index}")
    | .ok (state, events) =>
      unless state == run.state && events == run.events do
        throw (IO.userError s!"{name}: replay diverged")
      unless decide state.WellFormed do throw (IO.userError s!"{name}: invalid final state")
      IO.println s!"{name}: ok"
/-- info: basic: ok -/
#guard_msgs in
#eval runScenario "basic" basic
/-- info: amendment: ok -/
#guard_msgs in
#eval runScenario "amendment" amendment
/-- info: missing second: ok -/
#guard_msgs in
#eval runScenario "missing second" missingSecond
/-- info: debate closure: ok -/
#guard_msgs in
#eval runScenario "debate closure" debateClosure
/-- info: consent objection: ok -/
#guard_msgs in
#eval runScenario "consent objection" consentObjection
/-- info: appeal: ok -/
#guard_msgs in
#eval runScenario "appeal" appeal
/-- info: appeal tie: ok -/
#guard_msgs in
#eval runScenario "appeal tie" appealTie
/-- info: interruption: ok -/
#guard_msgs in
#eval runScenario "interruption" interruption
/-- info: stale judgment: ok -/
#guard_msgs in
#eval runScenario "stale judgment" staleJudgment
/-- info: quorum loss: ok -/
#guard_msgs in
#eval runScenario "quorum loss" quorumLoss
/-- info: table and restore: ok -/
#guard_msgs in
#eval runScenario "table and restore" tableRestore
/-- info: committee report: ok -/
#guard_msgs in
#eval runScenario "committee report" committeeReport
/-- info: postponement: ok -/
#guard_msgs in
#eval runScenario "postponement" postponement
/-- info: withdrawal: ok -/
#guard_msgs in
#eval runScenario "withdrawal" withdrawal
/-- info: chair vote: ok -/
#guard_msgs in
#eval runScenario "chair vote" chairVote
/-- info: session expiration: ok -/
#guard_msgs in
#eval runScenario "session expiration" sessionExpiration

end ParliamentTest
