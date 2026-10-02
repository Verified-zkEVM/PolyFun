/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Parliament.Procedure.Actions

/-! # Minutes submission, correction opportunity, and initial approval

The chair closes a correction opportunity, not a majority vote on the whole document. Contested
corrections use the ordinary second/debate/vote or consent machinery. The submitted text may be
inaccurate: this procedure certifies authority and transitions, never historical truth.
-/

@[expose] public section

namespace Parliament.Procedure

open RuleProgram

variable {D : MotionDomain}

/-- No correction or request for recognition may be silently bypassed at approval. -/
def minutesIdle (s : AssemblyState D) : Bool :=
  s.phase == .business && s.pending.isEmpty && s.proposal.isNone && s.floor.isNone &&
    s.requests.isEmpty && s.judgment.isNone && s.ruling.isNone && s.poll.isNone

/-- Submit attributed text for a recorded, completed, earlier meeting. -/
def submitMinutesDraft (s : AssemblyState D) (actor sourceMeeting sourceRevision : Nat)
    (text : D.Content) : RuleProgram (Result D) := do
  member s actor
  ensure (actor == s.secretary) .notSecretary
  ensure (sourceMeeting < s.calendar.meeting &&
    s.completedMeetings.contains (sourceMeeting, sourceRevision)) .wrongTarget
  ensure (!s.minutes.any (fun doc ↦ doc.submission.meeting == sourceMeeting)) .duplicate
  let doc : MinutesDocument D := {
    submission := ⟨sourceMeeting, sourceRevision, actor, text⟩,
    draft := text }
  pure ({ s with minutes := s.minutes ++ [doc] }, [.minutesSubmitted sourceMeeting])

/-- Open an explicit correction opportunity for an exact draft version. -/
def openMinutesReview (rules : Rules) (s : AssemblyState D) (actor : MemberId)
    (target : MinutesRef) : RuleProgram (Result D) := do
  chair s actor
  quorum rules s
  ensure (minutesIdle s && s.minutesReview.isNone) .businessPending
  let doc ← need (s.minutes.find? (fun doc ↦ doc.ref == target)) .staleMinutes
  ensure doc.approval.isNone .tooLate
  pure ({ s with minutesReview := some target }, [.minutesReviewOpened target])

/-- Freeze the exact reviewed text. This operation cannot overwrite a previous approval. -/
def approveMinutes (s : AssemblyState D) (target : MinutesRef) : AssemblyState D :=
  { s with
    minutesReview := none,
    minutes := s.minutes.map fun doc ↦
      if doc.ref == target && doc.approval.isNone then
        doc.approve s.calendar.meeting (s.revision + 1)
      else doc }

/-- Approval changes document state, not the raw substantive decision history. -/
theorem approveMinutes_history (s : AssemblyState D) (target : MinutesRef) :
    (approveMinutes s target).history = s.history := rfl

/-- Declare approval after the opportunity to correct, without a whole-document majority vote. -/
def closeMinutesReview (rules : Rules) (s : AssemblyState D) (actor : MemberId)
    (target : MinutesRef) : RuleProgram (Result D) := do
  chair s actor
  quorum rules s
  ensure (s.minutesReview == some target) .staleMinutes
  ensure (minutesIdle s) .businessPending
  let doc ← need (s.minutes.find? (fun doc ↦ doc.ref == target)) .staleMinutes
  ensure doc.approval.isNone .tooLate
  pure (approveMinutes s target, [.minutesApproved target])

/-- Record exact intended wording; later amendments automatically lose this narrow notice route. -/
def giveMinutesCorrectionNotice (s : AssemblyState D) (actor : MemberId)
    (target : MinutesRef) (text : D.Content) : RuleProgram (Result D) := do
  member s actor
  business s
  let doc ← need (s.minutes.find? (fun doc ↦ doc.ref == target)) .staleMinutes
  ensure doc.approval.isSome .wrongPhase
  pure ({ s with minutesNotices := s.minutesNotices ++
    [⟨target, text, s.calendar.meeting, s.calendar.today, actor⟩] }, [.minutesNoticeGiven target])

end Parliament.Procedure
