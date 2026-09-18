/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Rulebook

/-! # Shared parliamentary premises and judgment continuations -/

@[expose] public section

namespace Parliament
namespace Procedure

open RuleProgram

variable {D : MotionDomain}

/-- Candidate state and emitted events before transaction-boundary certification. -/
abbrev Result (D : MotionDomain) := AssemblyState D × List Event

/-- Require the configured chair's identity. -/
def chair (s : AssemblyState D) (actor : MemberId) : RuleProgram Unit :=
  ensure (actor == s.chair) .notChair

/-- Require a roster member whose presence is recorded. -/
def member (s : AssemblyState D) (actor : MemberId) : RuleProgram Unit :=
  ensure (s.isPresent actor) .notMember

/-- Require enough eligible members to be present. -/
def quorum (rules : Rules) (s : AssemblyState D) : RuleProgram Unit :=
  ensure (s.hasQuorum rules) .noQuorum

/-- Require the ordinary business phase. -/
def business (s : AssemblyState D) : RuleProgram Unit :=
  ensure (s.phase == .business) .wrongPhase

/-- Require any outstanding ruling to be resolved or under an active appeal. -/
def settled (s : AssemblyState D) : RuleProgram Unit := do
  ensure s.judgment.isNone .judgmentRequired
  ensure (s.ruling.isNone || s.pending.any (fun q => q.motion.kind == .appeal)) .tooLate

/-- Require the actor to hold the floor. -/
def ownsFloor (s : AssemblyState D) (actor : MemberId) : RuleProgram Unit :=
  ensure (s.floor.any (fun f => f.member == actor)) .lacksFloor

/-- Require and retrieve the immediately pending question. -/
def question (s : AssemblyState D) : RuleProgram (Question D) :=
  need s.activeQuestion .noQuestion

/-- Identify the supported recess and adjournment exceptions to quorum. -/
def allowsNoQuorum (motion : Motion D) : Bool :=
  match motion with
  | .adjourn | .recess _ => true
  | _ => false

/-- Require quorum unless this motion is a supported exception. -/
def substantiveQuorum (rules : Rules) (s : AssemblyState D) (motion : Motion D) :
    RuleProgram Unit :=
  ensure (allowsNoQuorum motion || s.hasQuorum rules) .noQuorum

/-- Count a member's speeches on this question during the current civil day. -/
def speechCount (s : AssemblyState D) (question : QuestionId) (member : MemberId) : Nat :=
  (s.speeches.filter (fun x => x.question == question && x.member == member &&
    x.date == s.calendar.today)).length

/-- Determine debate eligibility, including the current appeal's context. -/
def isDebatable (s : AssemblyState D) (q : Question D) : Bool :=
  match q.motion with
  | .appeal _ => s.ruling.any (fun r => r.request.debatable)
  | _ => q.motion.kind.debatable

/-- Apply ordinary limits or the special one-speech appeal limit for members. -/
def speechLimit (rules : Rules) (s : AssemblyState D) (q : Question D) (actor : MemberId) : Nat :=
  if q.motion.kind == .appeal then if actor == s.chair then 2 else 1
  else rules.speechesPerQuestion

/-- Determine whether a queued member remains entitled to speak on this question. -/
def canDebate (rules : Rules) (s : AssemblyState D) (q : Question D) (actor : MemberId) : Bool :=
  s.isPresent actor && isDebatable s q && !q.closed &&
    (actor != s.chair || q.motion.kind == .appeal) &&
    speechCount s q.id actor < speechLimit rules s q actor

/-- Choose the configured main-motion basis or prescribed procedural cast-vote basis. -/
def denominator (rules : Rules) (s : AssemblyState D) (q : Question D) (poll : Poll) : Nat :=
  -- Subsidiary and incidental motions keep their prescribed cast-vote thresholds.
  let basis := if q.motion.kind == .main then rules.ordinaryBasis else .cast
  poll.tally.denominator basis s.presentVoters s.votingCount

/-- Compute the prescribed result from a question and its poll. -/
def outcome (rules : Rules) (s : AssemblyState D) (q : Question D) (poll : Poll) : Bool :=
  poll.tally.passes q.motion.kind.threshold (denominator rules s q poll)

/-- Require any nonabstaining chair vote to change the computed outcome. -/
def chairVoteRelevant (rules : Rules) (s : AssemblyState D) (q : Question D) (poll : Poll) : Bool :=
  if poll.ballots.any (fun b => b.member == s.chair && b.vote != .abstain) then
    outcome rules s q poll != outcome rules s q (poll.without s.chair)
  else true

/-- Identify proposals requiring interpretation in the modeled subset. -/
def needsJudgment : Motion D → Bool
  | .main _ | .primary .. | .secondary .. | .table | .refer _ => true
  | _ => false

/-- Select the primary interpretive issue exposed for a proposed motion. -/
def issueFor : Motion D → IssueKind
  | .primary .. | .secondary .. => .germaneness
  | .table => .urgency
  | .refer _ => .dilatory
  | _ => .admissibility

/-- A general order which is due must precede fresh ordinary business. -/
def hasDueBusiness (s : AssemblyState D) : Bool :=
  s.suspended.any fun b =>
    match b.disposition with
    | .postponed date => date.ordinal ≤ s.calendar.today.ordinal
    | _ => false

/-- Allocate a fresh question with its initial approval requirement. -/
def newQuestion (s : AssemblyState D) (actor : MemberId) (motion : Motion D) : Question D :=
  { id := s.nextId, maker := actor, motion, approved := !needsJudgment motion }

/-- Capture the proposed wording and surrounding business for an external judgment. -/
def issueRequest (s : AssemblyState D) (q : Question D) : JudgmentRequest D :=
  { id := s.nextId + 1, revision := s.revision + 1, issue := issueFor q.motion,
    proposal := some q, context := s.pending, raisedBy := q.maker,
    suspended := s.suspended.flatMap (·.questions), history := s.history,
    reason := "Determine admissibility in the recorded context",
    debatable := q.motion.kind.debatable }

/-- Restore interrupted proceedings or the proposal held during an appeal. -/
def restoreReview (s : AssemblyState D) : AssemblyState D :=
  match s.review with
  | none => { s with proposal := s.heldProposal.or s.proposal, heldProposal := none }
  | some review =>
    { s with
      phase := review.phase,
      floor := review.floor.filter (fun f => s.isPresent f.member), proposal := review.proposal,
      poll := review.poll, heldProposal := none, review := none }

/-- Remove a proposal and only its own interpretive records, preserving an active appeal. -/
def discardProposal (s : AssemblyState D) (id : QuestionId) : AssemblyState D :=
  { s with
    proposal := none,
    judgment := s.judgment.filter (fun r => !r.proposal.any (fun q => q.id == id)),
    ruling := s.ruling.filter (fun r => !r.request.proposal.any (fun q => q.id == id)) }

/-- Commit the interpretive response after its appeal opportunity is resolved. -/
def finishRuling (s : AssemblyState D) (r : JudgmentRecord D) (allowed : Bool) : AssemblyState D :=
  let restored := restoreReview s
  let base := { restored with ruling := none, judgment := none }
  match r.request.proposal with
  | some proposed =>
    { base with
      proposal := base.proposal.bind fun q =>
        if q.id == proposed.id && q.version == proposed.version then
          if allowed then some { q with approved := true } else none
        else some q }
  | none =>
    if !allowed then base
    else match r.request.remedy with
    | .none => base
    | .releaseFloor => { base with floor := none }
    | .discardProposal => { base with proposal := none }
    | .cancelPoll => { base with poll := none, phase := .business }
    | .reopenDebate =>
      { base with
        poll := none, phase := .business,
        pending := base.pending.map (fun q => { q with closed := false }) }

/-- Mechanical applicability; semantic admissibility is a separate interaction. -/
def applicable (rules : Rules) (s : AssemblyState D) (motion : Motion D) : RuleProgram Unit := do
  substantiveQuorum rules s motion
  match motion with
  | .main _ =>
    ensure s.pending.isEmpty .businessPending
    ensure (s.businessClass == .newBusiness && !hasDueBusiness s) .wrongPrecedence
  | .primary target edit =>
    let q ← question s
    ensure (q.id == target) .wrongTarget
    ensure (!q.closed) .debateClosed
    match q.motion with
    | .main text => ensure (D.apply text edit).isSome .invalidAmendment
    | _ => .reject .unsupported
  | .secondary target edit =>
    let q ← question s
    ensure (q.id == target) .wrongTarget
    ensure (!q.closed) .debateClosed
    match q.motion with
    | .primary parent primary =>
      let main ← need (s.pending.find? (fun x => x.id == parent)) .wrongTarget
      match main.motion with
      | .main text => ensure (D.applySecondary text primary edit).isSome .invalidAmendment
      | _ => .reject .invalidAmendment
    | _ => .reject .invalidAmendment
  | .refer committee =>
    ensure (s.committees.contains committee) .unknownCommittee
    let q ← question s
    ensure (q.motion.kind.rank < MotionKind.refer.rank && !q.closed) .wrongPrecedence
    ensure (s.pending.any (fun q => q.motion.kind == .main)) .wrongTarget
  | .postpone dueDate =>
    ensure s.ruling.isNone .unsupported
    let q ← question s
    ensure (q.motion.kind.rank < MotionKind.postpone.rank && !q.closed) .wrongPrecedence
    ensure (s.pending.any (fun q => q.motion.kind == .main)) .wrongTarget
    ensure (decide dueDate.Valid && s.calendar.today.ordinal < dueDate.ordinal &&
      dueDate.ordinal ≤ s.calendar.nextRegular.ordinal &&
      s.calendar.today.withinQuarter dueDate && s.calendar.termsContinue) .invalidDate
  | .previousQuestion through =>
    let q ← question s
    ensure (isDebatable s q && !q.closed) .debateClosed
    ensure (s.pending.any (fun q => q.id == through)) .wrongTarget
    ensure (s.pending.takeWhile (fun q => q.id != through) |>.all
      (fun q => q.motion.kind != .appeal)) .wrongTarget
  | .table =>
    let q ← question s
    ensure (q.motion.kind.rank < MotionKind.table.rank) .wrongPrecedence
    ensure (s.pending.any (fun q => q.motion.kind == .main)) .wrongTarget
  | .takeFromTable target =>
    ensure s.pending.isEmpty .businessPending
    let bundle ← need (s.suspended.find? (fun b => b.id == target)) .noBusiness
    ensure (bundle.disposition == .tabled) .wrongTarget
    ensure (s.businessClass != .reports || bundle.businessClass == .reports) .wrongPrecedence
    ensure (bundle.expiresAfterSession.all (fun n => s.calendar.session ≤ n)) .expired
  | .recess endSecond =>
    ensure (s.nowSecond < endSecond) .invalidDate
    ensure (s.activeQuestion.all (fun q => q.motion.kind.rank < MotionKind.recess.rank))
      .wrongPrecedence
  | .adjourn =>
    ensure s.ruling.isNone .unsupported
    ensure (s.activeQuestion.all (fun q => q.motion.kind != .adjourn)) .wrongPrecedence
  | .withdrawal target =>
    let q ← need (s.pending.find? (fun q => q.id == target)) .wrongTarget
    ensure (q.motion.kind == .main || q.motion.kind == .primary ||
      q.motion.kind == .secondary) .unsupported
  | .appeal _ => pure ()

end Procedure
end Parliament
