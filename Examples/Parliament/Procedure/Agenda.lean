/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Procedure.Actions

/-! # Attendance, time, reports, postponed business, and meeting continuity -/

@[expose] public section

namespace Parliament
namespace Procedure

open RuleProgram

variable {D : MotionDomain}

/-- Open a configured meeting, retaining any unfinished pending series. -/
def openMeeting (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  chair s actor
  ensure (s.phase == .dormant) .wrongPhase
  pure ({ s with
    phase := .business,
    businessClass := if s.pending.isEmpty then .reports else .unfinished },
    [.opened s.calendar.meeting s.calendar.session])

/-- Move through the modeled business classes without skipping pending or due questions. -/
def advanceBusiness (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  chair s actor
  business s
  settled s
  ensure (s.pending.isEmpty && s.proposal.isNone && s.floor.isNone) .businessPending
  let next ← match s.businessClass with
    | .reports => pure BusinessClass.unfinished
    | .unfinished => do
      ensure (!hasDueBusiness s) .businessPending
      pure BusinessClass.newBusiness
    | .newBusiness => .reject .wrongPhase
  pure ({ s with businessClass := next }, [.businessAdvanced next])

/-- Update presence and release floor or queue entries for a departing member. -/
def attendance (s : AssemblyState D) (actor memberId : MemberId) (present : Bool) :
    RuleProgram (Result D) := do
  chair s actor
  ensure (s.isMember memberId) .notMember
  let remaining := s.present.filter (· != memberId)
  let next := if present then memberId :: remaining else remaining
  pure ({ s with
    present := next,
    floor := s.floor.filter (fun f => present || f.member != memberId),
    requests := s.requests.filter (fun m => present || m != memberId) },
    [.attendance memberId present])

/-- Receive a committee's referred series for resumed consideration. -/
def report (rules : Rules) (s : AssemblyState D) (actor : MemberId)
    (committee : CommitteeId) (target : QuestionId) : RuleProgram (Result D) := do
  chair s actor
  business s
  settled s
  quorum rules s
  ensure (s.pending.isEmpty && s.proposal.isNone && s.floor.isNone) .businessPending
  let b ← need (s.suspended.find? (fun b => b.id == target)) .noBusiness
  ensure (b.disposition == .referred committee) .wrongTarget
  pure (restoreBundle s b, [.resumed target])

/-- Restore postponed business whose specified date has arrived. -/
def resumeDue (rules : Rules) (s : AssemblyState D) (actor : MemberId)
    (target : QuestionId) : RuleProgram (Result D) := do
  chair s actor
  business s
  settled s
  quorum rules s
  ensure (s.pending.isEmpty && s.proposal.isNone && s.floor.isNone) .businessPending
  let b ← need (s.suspended.find? (fun b => b.id == target)) .noBusiness
  match b.disposition with
  | .postponed dueDate =>
    ensure (dueDate.ordinal ≤ s.calendar.today.ordinal) .notDue
    ensure (b.expiresAfterSession.all (fun n => s.calendar.session ≤ n)) .expired
    pure (restoreBundle s b, [.resumed target])
  | _ => .reject .wrongTarget

/-- Advance the host clock and expire any speech whose time has elapsed. -/
def advanceTime (rules : Rules) (s : AssemblyState D) (actor : MemberId)
    (date : Date) (second : Nat) : RuleProgram (Result D) := do
  chair s actor
  ensure (decide date.Valid && s.calendar.today.ordinal ≤ date.ordinal &&
    date.ordinal ≤ s.calendar.nextRegular.ordinal) .invalidDate
  ensure (date != s.calendar.today || s.nowSecond ≤ second) .invalidDate
  let floor := s.floor.filter (fun f => !f.speaking ||
    (date == s.calendar.today && second < f.sinceSecond + rules.speechSeconds))
  let review := s.review.map fun r =>
    { r with
      floor := r.floor.bind fun f =>
        if date != s.calendar.today then none
        else some { f with sinceSecond := f.sinceSecond + (second - s.nowSecond) } }
  pure ({ s with
    calendar := { s.calendar with today := date }, nowSecond := second, floor, review,
    recessUntil := if date == s.calendar.today then s.recessUntil else 0 },
    [.timeAdvanced date second])

/-- Resume business once the recess deadline has arrived. -/
def resumeRecess (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  chair s actor
  ensure (s.phase == .recessed) .wrongPhase
  ensure (s.recessUntil ≤ s.nowSecond) .notDue
  pure ({ s with phase := .business }, [])

/-- Carry unfinished pending business separately from tabled and postponed bundles. -/
def carryPending (s : AssemblyState D) (calendar : Calendar) (newSession : Bool) :
    List (Question D) :=
  if !newSession then s.pending
  else if s.calendar.termsContinue && s.calendar.today.withinQuarter calendar.today then
    s.pending.filterMap fun q =>
      match q.motion with
      | .previousQuestion _ => none
      | .postpone dueDate =>
        if dueDate.ordinal ≤ calendar.today.ordinal then none else some { q with closed := false }
      | _ => some { q with closed := false }
  else []

/-- Advance from adjournment, carrying or expiring business under session rules. -/
def nextMeeting (s : AssemblyState D) (actor : MemberId) (calendar : Calendar)
    (newSession : Bool) : RuleProgram (Result D) := do
  chair s actor
  ensure (s.phase == .adjourned) .wrongPhase
  ensure (decide calendar.Valid && s.calendar.today.ordinal ≤ calendar.today.ordinal) .invalidDate
  ensure (calendar.meeting == s.calendar.meeting + 1 &&
    calendar.session == s.calendar.session + if newSession then 1 else 0) .invalidDate
  if newSession then
    ensure (calendar.today == s.calendar.nextRegular) .invalidDate
  let live := s.suspended.filter fun b =>
    b.expiresAfterSession.all (fun n => calendar.session ≤ n) &&
      (match b.disposition with
       | .referred _ => true
       | _ => !newSession ||
           (s.calendar.termsContinue && b.date.withinQuarter calendar.today))
  let expired := s.suspended.filter (fun b => !live.any (fun x => x.id == b.id))
  pure ({ s with
    calendar, phase := .dormant, present := [], floor := none, requests := [],
    pending := carryPending s calendar newSession, suspended := live, proposal := none,
    judgment := none, ruling := none, review := none, heldProposal := none, poll := none,
    nowSecond := 0, consentObjector := none }, expired.map (fun b => .expired b.id))

/-- The rule program associated to each public command. -/
def procedure (rules : Rules) (s : AssemblyState D) : Command D → RuleProgram (Result D)
  | .openMeeting a => openMeeting s a
  | .advanceBusiness a => advanceBusiness s a
  | .attendance a m p => attendance s a m p
  | .requestFloor a => requestFloor s a
  | .recognize a m => recognize s a m
  | .speak a => speak rules s a
  | .yieldFloor a => yieldFloor s a
  | .propose a m => propose rules s a m
  | .second a => second s a
  | .stateQuestion a => stateQuestion rules s a
  | .lackSecond a => lackSecond s a
  | .withdraw a => withdraw rules s a
  | .pointOfOrder a reason remedy => pointOfOrder s a reason remedy
  | .answerJudgment a request revision answer => answerJudgment s a request revision answer
  | .continueAfterRuling a => continueAfterRuling s a
  | .openVote a => openVote rules s a
  | .vote a v => vote s a v
  | .announce a => announce rules s a
  | .seekConsent a => seekConsent rules s a
  | .object a => object s a
  | .closeConsent a => closeConsent rules s a
  | .report a c q => report rules s a c q
  | .resumeDue a q => resumeDue rules s a q
  | .advanceTime a date second => advanceTime rules s a date second
  | .resumeRecess a => resumeRecess s a
  | .nextMeeting a calendar newSession => nextMeeting s a calendar newSession
  | .unsupported _ => .reject .unsupported

end Procedure
end Parliament
