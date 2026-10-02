/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ParliamentTest.Scenarios
public import ParliamentTest.Application
meta import ParliamentTest.Application

/-! # Source-derived procedural boundaries, including editable minutes

Assertions name expected outcomes independently of replay. The application runner executes all
accepted and rejected attempts, checking that only accepted commands reach persistence.
-/

@[expose] public section

namespace ParliamentTest.Semantics

open Parliament

def untabling : Scenario Unit := do
  start
  let target ← mainMotion
  let _ ← move .table
  adopt
  floorFor 1
  send (.propose 1 (.takeFromTable target))
  send (.second 2)
  rejected (.stateQuestion 0) .judgmentRequired
  let some request := (← get).state.judgment | throw "missing untabling review"
  check (request.obligations.contains .untabling) "untabling omitted contextual eligibility"
  ruleOn false
  send (.continueAfterRuling 0)
  check ((← get).state.pending.isEmpty) "denied untabling restored business"
  let _ ← move (.main ["handle", "intervening", "business"])
  consent
  let _ ← move (.takeFromTable target)
  adopt
  check ((← get).state.activeQuestion.any (fun q ↦ q.id == target)) "lost tabled question"

def renewal : Scenario Unit := do
  start
  let target ← mainMotion
  let _ ← move (.previousQuestion target)
  send (.openVote 0)
  send (.vote 1 .no)
  send (.announce 0)
  floorFor 1
  send (.propose 1 (.previousQuestion target))
  send (.second 2)
  rejected (.stateQuestion 0) .judgmentRequired
  let some request := (← get).state.judgment | throw "renewal omitted review"
  check (request.obligations == [.sameQuestion]) "wrong renewal obligations"
  ruleOn false
  send (.continueAfterRuling 0)
  check ((← get).state.activeQuestion.any (fun q ↦ q.id == target && !q.closed))
    "denied renewal closed debate"
  let _ ← move .adjourn
  send (.openVote 0)
  send (.vote 1 .no)
  send (.announce 0)
  floorFor 1
  send (.propose 1 .adjourn)
  send (.second 2)
  rejected (.stateQuestion 0) .judgmentRequired
  approve
  send (.stateQuestion 0)
  consent

/-- A prior reversed ruling must not strand an appeal against a different ruling. -/
def distinctAppeals : Scenario Unit := do
  ParliamentTest.appeal
  let main ← mainMotion
  floorFor 1
  send (.propose 1 (.primary main ⟨2, 1, ["museum"]⟩))
  send (.second 2)
  ruleOn false
  let some ruling := (← get).state.ruling | throw "missing second ruling"
  send (.propose 3 (.appeal ruling.request.id))
  send (.second 4)
  check ((← get).state.judgment.isNone) "appeal acquired a renewal judgment"
  send (.stateQuestion 0)
  adopt
  check ((← get).state.proposal.isNone) "sustained ruling left a proposal"

/-- The direct withdrawal command must create the same renewal review as an explicit motion. -/
def withdrawalRenewal : Scenario Unit := do
  start
  let _ ← mainMotion
  send (.withdraw 1)
  send (.stateQuestion 0)
  send (.openVote 0)
  send (.vote 2 .no)
  send (.announce 0)
  send (.withdraw 1)
  let some request := (← get).state.judgment | throw "withdrawal renewal omitted judgment"
  check (request.obligations == [.sameQuestion]) "wrong withdrawal renewal obligations"
  rejected (.stateQuestion 0) .judgmentRequired
  approve
  send (.stateQuestion 0)
  consent
  check ((← get).state.pending.isEmpty) "renewed withdrawal failed"

def idleRecess : Scenario Unit := do
  start
  let _ ← move (.recess 100)
  floorFor 1
  send (.speak 1)
  send (.yieldFloor 1)
  adopt
  check ((← get).state.phase == .recessed) "idle main-motion recess failed"

def advanceMeeting : Scenario Unit := do
  let _ ← move .adjourn
  consent
  let cal := (← get).state.calendar
  send (.nextMeeting 0 { cal with meeting := cal.meeting + 1 } false)
  for member in [0, 1, 2, 3, 4] do send (.attendance 0 member true)
  send (.openMeeting 0)
  send (.advanceBusiness 0)
  send (.advanceBusiness 0)

def submitted : Scenario Nat := do
  start
  send (.attendance 0 3 false)
  let _ ← mainMotion
  consent
  advanceMeeting
  let some (_, source) := (← get).state.completedMeetings.head? | throw "missing completion"
  rejected (.submitMinutesDraft 2 0 source ["wrong", "secretary"]) .notMember
  send (.submitMinutesDraft 1 0 source ["intentionally", "inaccurate"])
  pure source

def minutesLifecycle : Scenario Unit := do
  let _ ← submitted
  let originalDecisions := (← get).state.history
  send (.openMinutesReview 0 ⟨0, 0⟩)
  send (.requestFloor 3)
  rejected (.closeMinutesReview 0 ⟨0, 0⟩) .businessPending
  send (.recognize 0 3)
  send (.propose 3 (.correctMinutes ⟨0, 0⟩ ["corrected", "draft"]))
  send (.second 2)
  send (.stateQuestion 0)
  let some q := (← get).state.activeQuestion | throw "missing correction"
  let _ ← move (.primary q.id ⟨0, 1, ["reviewed"]⟩)
  consent
  adopt
  rejected (.closeMinutesReview 0 ⟨0, 0⟩) .staleMinutes
  send (.closeMinutesReview 0 ⟨0, 1⟩)
  let some doc := (← get).state.minutes.head? | throw "missing minutes"
  check (doc.approval.any (fun a ↦ a.text == ["reviewed", "draft"])) "wrong approved text"
  check (doc.submission.text == ["intentionally", "inaccurate"]) "submission was rewritten"
  let decisions := (← get).state.history
  check (originalDecisions.all (fun d ↦ decisions.contains d)) "old decisions changed"
  let _ ← move (.correctMinutes ⟨0, 1⟩ ["later", "correction"])
  send (.seekConsent 0)
  send (.object 2)
  rejected (.closeConsent 0) .wrongPhase
  adopt
  let some changed := (← get).state.minutes.head? | throw "lost minutes"
  check (changed.approval == doc.approval && changed.corrections.length == 1 &&
    changed.text == ["later", "correction"]) "postapproval correction overwrote original"
  floorFor 1
  rejected (.propose 1 (.correctMinutes ⟨0, 1⟩ ["stale"])) .staleMinutes

/-- Resolving one correction cannot erase a member's opportunity to offer another. -/
def correctionQueue : Scenario Unit := do
  let _ ← submitted
  send (.openMinutesReview 0 ⟨0, 0⟩)
  let _ ← move (.correctMinutes ⟨0, 0⟩ ["first", "correction"])
  send (.requestFloor 3)
  consent
  check ((← get).state.requests == [3]) "correction erased waiting recognition"
  rejected (.closeMinutesReview 0 ⟨0, 1⟩) .businessPending
  send (.recognize 0 3)
  rejected (.closeMinutesReview 0 ⟨0, 1⟩) .businessPending
  send (.yieldFloor 3)
  send (.closeMinutesReview 0 ⟨0, 1⟩)

/-- Approval is procedural: deliberately inaccurate submitted text can still be approved. -/
def approvalIsNotTruth : Scenario Unit := do
  let _ ← submitted
  let before := (← get).state.history
  send (.openMinutesReview 0 ⟨0, 0⟩)
  send (.closeMinutesReview 0 ⟨0, 0⟩)
  check ((← get).state.history == before) "approval rewrote the decision register"
  let some doc := (← get).state.minutes.head? | throw "missing minutes"
  check (doc.approval.any (fun a ↦ a.text == ["intentionally", "inaccurate"]))
    "approval silently repaired text"

/-- Independent arithmetic/scope checks; ordinary main-motion overrides cannot alter these rules. -/
def thresholds : IO Unit := do
  let doc : MinutesDocument wordDomain := {
    submission := ⟨0, 10, 1, ["original"]⟩, draft := ["original"],
    approval := some ⟨1, 20, 0, ["original"]⟩ }
  let state : AssemblyState wordDomain := { initial with
    members := (List.range 7).map (fun id ↦ ⟨id, true, true⟩),
    calendar := { calendar with meeting := 2 }, minutes := [doc] }
  let q : Question wordDomain := {
    id := 0, maker := 1,
    motion := .correctMinutes ⟨0, 0⟩ ["changed"] }
  let poll (yes no : Nat) : Poll := ⟨0,
    (List.range yes).map (fun id ↦ ⟨id, .yes⟩) ++
    (List.range no).map (fun id ↦ ⟨id + yes, .no⟩)⟩
  let outcome := Procedure.outcome { rules with ordinaryBasis := .membership }
  unless outcome state q (poll 2 1) && outcome state q (poll 4 3) &&
      !outcome state q (poll 3 2) do throw (IO.userError "wrong no-notice threshold alternatives")
  let noticed := { state with minutesNotices := [⟨⟨0, 0⟩, ["changed"], 1, calendar.today, 1⟩] }
  unless outcome noticed q (poll 3 2) &&
      !outcome noticed { q with motion := .correctMinutes ⟨0, 0⟩ ["amended"] } (poll 3 2) &&
      !outcome { noticed with calendar := { calendar with meeting := 3 } } q (poll 3 2) do
    throw (IO.userError "notice scope or previous-meeting restriction ignored")
  let main : Question wordDomain := { id := 0, maker := 1, motion := .main ["rejected"] }
  let rejectedMain := { state with history := [⟨main, false, calendar.today, calendar.session⟩] }
  unless (Procedure.issueRequest rejectedMain main).obligations ==
      [.admissibility, .sameQuestion] do
    throw (IO.userError "renewal erased the intrinsic admissibility obligation")

def tests : IO Unit := do
  for (name, program) in [("untabling", untabling), ("renewal", renewal),
      ("distinct appeals", distinctAppeals), ("withdrawal renewal", withdrawalRenewal),
      ("idle recess", idleRecess), ("minutes lifecycle", minutesLifecycle),
      ("correction queue", correctionQueue),
      ("approval not truth", approvalIsNotTruth)] do
    Application.scenario name program
  thresholds
  IO.println "Procedural and minutes boundaries: ok"

/-- info: Procedural and minutes boundaries: ok -/
#guard_msgs in
#eval tests

end ParliamentTest.Semantics
