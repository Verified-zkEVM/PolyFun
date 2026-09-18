/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Procedure.Disposition

/-! # Motion, debate, voting, and ruling procedures -/

@[expose] public section

namespace Parliament
namespace Procedure

open RuleProgram

variable {D : MotionDomain}

/-- Make a motion, checking precedence and opening any required judgment interaction. -/
def propose (rules : Rules) (s : AssemblyState D) (actor : MemberId) (motion : Motion D) :
    RuleProgram (Result D) := do
  business s
  member s actor
  ensure (actor != s.chair) .lacksFloor
  match motion with
  | .appeal rulingId =>
    let r ← need s.ruling .tooLate
    ensure (r.request.id == rulingId && r.request.appealable) .notAppealable
    ensure (s.pending.all (fun q => q.motion.kind != .appeal) &&
      s.proposal.all (fun q => q.motion.kind != .appeal)) .notAppealable
    quorum rules s
    let q := newQuestion s actor motion
    pure ({ s with
      proposal := some q, heldProposal := s.proposal, floor := none,
      nextId := s.nextId + 1 }, [.proposed q.id .appeal actor])
  | _ =>
    settled s
    ensure (s.ruling.isNone || !needsJudgment motion) .unsupported
    ensure s.proposal.isNone .businessPending
    ownsFloor s actor
    applicable rules s motion
    if let .withdrawal target := motion then
      let original ← need (s.pending.find? (fun q => q.id == target)) .wrongTarget
      ensure (original.maker == actor) .wrongTarget
    let q := newQuestion s actor motion
    let request := if needsJudgment motion then some (issueRequest s q) else none
    pure ({ s with
      proposal := some q, floor := none, judgment := request,
      nextId := s.nextId + 2 },
      [.proposed q.id motion.kind actor] ++
        request.toList.map (fun r => .judgmentRequested r.id r.issue))

/-- Record a distinct member's second before the chair states a proposal. -/
def second (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  member s actor
  business s
  ensure (actor != s.chair) .lacksFloor
  let q ← need s.proposal .noQuestion
  ensure (actor != q.maker) .alreadySeconded
  ensure q.seconder.isNone .alreadySeconded
  pure ({ s with proposal := some { q with seconder := some actor } }, [.seconded q.id actor])

/-- Transfer an approved, sufficiently seconded proposal into pending business. -/
def stateQuestion (rules : Rules) (s : AssemblyState D) (actor : MemberId) :
    RuleProgram (Result D) := do
  chair s actor
  business s
  let q ← need s.proposal .noQuestion
  if q.motion.kind != .appeal then settled s
  ensure q.approved .judgmentRequired
  ensure (q.seconder.isSome || q.motion.kind == .withdrawal) .needsSecond
  applicable rules s q.motion
  pure ({ s with pending := q :: s.pending, proposal := none, floor := none }, [.stated q.id])

/-- Dispose of a proposal for which no second has been supplied. -/
def lackSecond (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  chair s actor
  business s
  let q ← need s.proposal .noQuestion
  ensure q.seconder.isNone .alreadySeconded
  if q.motion.kind == .appeal then
    let r ← need s.ruling .staleJudgment
    pure (finishRuling { s with proposal := none } r r.answer.allowed, [])
  else
    pure (discardProposal s q.id,
      [.decided q.id false {}])

/-- Withdraw before statement, or request assembly permission afterward. -/
def withdraw (rules : Rules) (s : AssemblyState D) (actor : MemberId) :
    RuleProgram (Result D) := do
  member s actor
  business s
  match s.proposal with
  | some q =>
    ensure (q.maker == actor) .wrongTarget
    ensure (q.motion.kind != .appeal) .unsupported
    pure (discardProposal s q.id, [.withdrawn q.id])
  | none =>
    settled s
    let q ← question s
    ensure (q.maker == actor) .wrongTarget
    ensure (s.floor.all (fun f => f.member == actor)) .floorOccupied
    quorum rules s
    let request := newQuestion s actor (.withdrawal q.id)
    pure ({ s with proposal := some request, floor := none, nextId := s.nextId + 1 },
      [.proposed request.id .withdrawal actor])

/-- Queue a present member for recognition. -/
def requestFloor (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  member s actor
  business s
  ensure (!s.requests.contains actor) .duplicate
  pure ({ s with requests := s.requests ++ [actor] }, [])

/-- Grant an unoccupied floor to a member who has requested it. -/
def recognize (s : AssemblyState D) (actor memberId : MemberId) : RuleProgram (Result D) := do
  chair s actor
  business s
  settled s
  member s memberId
  ensure s.floor.isNone .floorOccupied
  ensure (s.requests.contains memberId) .lacksFloor
  ensure s.proposal.isNone .businessPending
  pure ({ s with
    floor := some ⟨memberId, s.nowSecond, false⟩,
    requests := s.requests.filter (· != memberId) }, [.recognized memberId])

/-- Begin a speech subject to debate eligibility and the daily speech count. -/
def speak (rules : Rules) (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  member s actor
  business s
  settled s
  ownsFloor s actor
  let q ← question s
  ensure (isDebatable s q && !q.closed) .debateClosed
  ensure (actor != s.chair || q.motion.kind == .appeal) .lacksFloor
  let floor ← need s.floor .lacksFloor
  ensure (!floor.speaking) .duplicate
  ensure (speechCount s q.id actor < speechLimit rules s q actor) .speechLimit
  pure ({ s with
    floor := some { floor with speaking := true, sinceSecond := s.nowSecond },
    speeches := ⟨q.id, actor, s.calendar.today⟩ :: s.speeches }, [.spoke q.id actor])

/-- Release the actor's own floor. -/
def yieldFloor (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  member s actor
  ownsFloor s actor
  pure ({ s with floor := none }, [])

/-- Suspend proceedings and expose a prospective procedural remedy for judgment. -/
def pointOfOrder (s : AssemblyState D) (actor : MemberId) (reason : String) (remedy : Remedy) :
    RuleProgram (Result D) := do
  member s actor
  ensure (s.phase == .business || s.phase == .voting || s.phase == .consent) .wrongPhase
  ensure s.judgment.isNone .judgmentRequired
  ensure s.ruling.isNone .unsupported
  let req : JudgmentRequest D :=
    { id := s.nextId, revision := s.revision + 1, issue := .pointOfOrder,
      proposal := none, context := s.pending, raisedBy := actor, reason, remedy,
      suspended := s.suspended.flatMap (·.questions), history := s.history,
      debatable := s.activeQuestion.any (fun q => isDebatable s q) }
  pure ({ s with
    judgment := some req, nextId := s.nextId + 1,
    review := some ⟨s.phase, s.floor, s.proposal, s.poll⟩,
    phase := .business, floor := none, proposal := none, poll := none },
    [.judgmentRequested req.id req.issue])

/-- Record a reply to the exact outstanding request and question versions. -/
def answerJudgment (s : AssemblyState D) (actor request revision : Nat) (answer : Ruling) :
    RuleProgram (Result D) := do
  chair s actor
  let req ← need s.judgment .staleJudgment
  ensure (req.id == request && req.revision == revision) .staleJudgment
  ensure (req.context.map (fun q => (q.id, q.version)) ==
    s.pending.map (fun q => (q.id, q.version))) .staleJudgment
  ensure (req.proposal.all (fun q => s.proposal.any
    (fun current => current.id == q.id && current.version == q.version))) .staleJudgment
  pure ({ s with
    judgment := none,
    ruling := some ⟨req, answer, s.revision + 1⟩ }, [.ruled request answer])

/-- Close the explicit appeal opportunity and apply the ruling. -/
def continueAfterRuling (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  chair s actor
  let r ← need s.ruling .staleJudgment
  ensure (s.pending.all (fun q => q.motion.kind != .appeal) &&
    s.proposal.all (fun q => q.motion.kind != .appeal)) .businessPending
  pure (finishRuling s r r.answer.allowed, [])

/-- Open a poll after debate is closed or no eligible speaker is waiting. -/
def openVote (rules : Rules) (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  chair s actor
  business s
  ensure s.judgment.isNone .judgmentRequired
  ensure s.proposal.isNone .businessPending
  let q ← question s
  ensure (s.ruling.isNone || s.pending.any (fun q => q.motion.kind == .appeal)) .tooLate
  substantiveQuorum rules s q.motion
  ensure s.floor.isNone .floorOccupied
  ensure (q.closed || !isDebatable s q ||
    !s.requests.any (fun m => canDebate rules s q m)) .pendingSpeakers
  pure ({ s with phase := .voting, poll := some ⟨q.id, []⟩ }, [.voteOpened q.id])

/-- Record or replace a present eligible member's choice before announcement. -/
def vote (s : AssemblyState D) (actor : MemberId) (choice : Vote) : RuleProgram (Result D) := do
  ensure (s.phase == .voting) .wrongPhase
  ensure (s.canVote actor) .ineligibleVoter
  let poll ← need s.poll .wrongPhase
  pure ({ s with poll := some (poll.record actor choice) }, [.voteCast poll.question actor choice])

/-- Recheck quorum, count the poll, and apply the immediately pending question. -/
def announce (rules : Rules) (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  chair s actor
  ensure (s.phase == .voting) .wrongPhase
  let poll ← need s.poll .wrongPhase
  let q ← question s
  ensure (poll.question == q.id) .wrongTarget
  substantiveQuorum rules s q.motion
  ensure (chairVoteRelevant rules s q poll) .chairVoteIrrelevant
  let adopted := outcome rules s q poll
  let (next, events) ← dispose s adopted
  pure (next, .decided q.id adopted poll.tally :: events)

/-- Open an explicit opportunity to object to adoption without a counted vote. -/
def seekConsent (rules : Rules) (s : AssemblyState D) (actor : MemberId) :
    RuleProgram (Result D) := do
  chair s actor
  business s
  ensure s.judgment.isNone .judgmentRequired
  ensure s.proposal.isNone .businessPending
  let q ← question s
  ensure (s.ruling.isNone || s.pending.any (fun q => q.motion.kind == .appeal)) .tooLate
  substantiveQuorum rules s q.motion
  ensure s.floor.isNone .floorOccupied
  pure ({ s with phase := .consent, consentObjector := none }, [.consentOpened q.id])

/-- End the consent attempt and return the question to ordinary consideration. -/
def object (s : AssemblyState D) (actor : MemberId) : RuleProgram (Result D) := do
  member s actor
  ensure (s.phase == .consent) .wrongPhase
  let q ← question s
  pure ({ s with phase := .business, consentObjector := some actor }, [.objection q.id actor])

/-- Adopt after an unopposed consent opportunity, rechecking quorum. -/
def closeConsent (rules : Rules) (s : AssemblyState D) (actor : MemberId) :
    RuleProgram (Result D) := do
  chair s actor
  ensure (s.phase == .consent) .wrongPhase
  ensure s.consentObjector.isNone .consentObjected
  let q ← question s
  substantiveQuorum rules s q.motion
  let (next, events) ← dispose s true
  pure (next, .consentGranted q.id :: events)

end Procedure
end Parliament
