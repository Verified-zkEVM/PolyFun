/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Content

/-!
# Public meeting data and commands

Pending questions are stored innermost first. A bundle retains an entire interrupted
question series. Judgment requests are versioned and remain explicit in meeting state.
-/

@[expose] public section

namespace Parliament

/-- Explicit rejection reasons; unsupported procedures never fall through silently. -/
inductive RuleError where
  | unsupported | invalidConfiguration | invalidState | notMember | notChair
  | noQuorum | wrongPhase | floorOccupied | lacksFloor | noQuestion | wrongTarget
  | needsSecond | alreadySeconded | invalidAmendment | wrongPrecedence
  | judgmentRequired | staleJudgment | notAppealable | tooLate | debateClosed
  | speechLimit | speechTime | pendingSpeakers | duplicate | ineligibleVoter
  | chairVoteIrrelevant | consentObjected | invalidDate | expired | notDue
  | unknownCommittee | businessPending | noBusiness | terminal
  deriving DecidableEq, Repr

/-- The motion families implemented by this bounded procedure model. -/
inductive MotionKind where
  | main | primary | secondary | refer | postpone | previousQuestion | table
  | takeFromTable | recess | adjourn | withdrawal | appeal
  deriving DecidableEq, Repr, Inhabited

/-- A motion's family together with its content, target, or timing parameters. -/
inductive Motion (D : MotionDomain) where
  | main (text : D.Content)
  | primary (target : QuestionId) (edit : D.Primary)
  | secondary (target : QuestionId) (edit : D.Secondary)
  | refer (committee : CommitteeId)
  | postpone (dueDate : Date)
  | previousQuestion (through : QuestionId)
  | table
  | takeFromTable (target : QuestionId)
  | recess (untilSecond : Nat)
  | adjourn
  | withdrawal (target : QuestionId)
  | appeal (ruling : Nat)
  deriving DecidableEq

/-- Forget a motion's parameters to obtain its procedural family. -/
def Motion.kind {D : MotionDomain} : Motion D → MotionKind
  | .main _ => .main
  | .primary .. => .primary
  | .secondary .. => .secondary
  | .refer _ => .refer
  | .postpone _ => .postpone
  | .previousQuestion _ => .previousQuestion
  | .table => .table
  | .takeFromTable _ => .takeFromTable
  | .recess _ => .recess
  | .adjourn => .adjourn
  | .withdrawal _ => .withdrawal
  | .appeal _ => .appeal

/-- Precedence among the modeled ranked motions; incidental rules are separate. -/
def MotionKind.rank : MotionKind → Nat
  | .main | .takeFromTable | .withdrawal | .appeal => 0
  | .primary => 1
  | .secondary => 2
  | .refer => 3
  | .postpone => 4
  | .previousQuestion => 6
  | .table => 7
  | .recess => 8
  | .adjourn => 9

/-- Default debate eligibility, refined by context for appeals. -/
def MotionKind.debatable : MotionKind → Bool
  | .previousQuestion | .table | .takeFromTable | .recess | .adjourn | .withdrawal => false
  | _ => true

/-- Prescribed voting threshold for each modeled motion family. -/
def MotionKind.threshold : MotionKind → Threshold
  | .previousQuestion => .twoThirds
  | .appeal => .sustainChair
  | _ => .majority

/-- Questions remain distinguishable even if their textual contents coincide. -/
structure Question (D : MotionDomain) where
  /-- Identity retained across wording changes and suspension. -/
  id : QuestionId
  /-- Wording revision, incremented when an amendment is applied. -/
  version : Nat := 0
  /-- Member who proposed this question. -/
  maker : MemberId
  /-- Current wording and procedural parameters. -/
  motion : Motion D
  /-- Member who supplied the second, if any. -/
  seconder : Option MemberId := none
  /-- Whether an adopted Previous Question currently closes debate. -/
  closed : Bool := false
  /-- Whether required interpretive review has been resolved favorably. -/
  approved : Bool := false
  deriving DecidableEq

/-- The question version and outcome recorded at a decision boundary. -/
structure DecisionRecord (D : MotionDomain) where
  /-- Exact version of the question at its decision boundary. -/
  question : Question D
  /-- Whether the question was adopted; true sustains the chair on an appeal. -/
  adopted : Bool
  /-- Civil date of the decision. -/
  date : Date
  /-- Session in which the decision was made. -/
  session : Nat
  deriving DecidableEq

/-- Categories of interpretive questions exposed to an external handler. -/
inductive IssueKind where
  | admissibility | germaneness | urgency | sameQuestion | dilatory | pointOfOrder
  deriving DecidableEq, Repr, Inhabited

/-- Prospective remedies; past decisions are never silently rewritten. -/
inductive Remedy where
  | none | releaseFloor | discardProposal | cancelPoll | reopenDebate
  deriving DecidableEq, Repr, Inhabited

/-- A judgment concerns the exact proposal and meeting revision in its context. -/
structure JudgmentRequest (D : MotionDomain) where
  /-- Unique request identity from the assembly's allocator. -/
  id : Nat
  /-- Revision at issuance, echoed by every valid reply. -/
  revision : Nat
  /-- The interpretive issue being submitted. -/
  issue : IssueKind
  /-- Proposed question under review, absent for a point of order. -/
  proposal : Option (Question D)
  /-- Snapshot of the pending series, including wording versions. -/
  context : List (Question D)
  /-- Snapshot of suspended questions available for semantic comparison. -/
  suspended : List (Question D) := []
  /-- Prior decision versions available for renewal and admissibility judgments. -/
  history : List (DecisionRecord D) := []
  /-- Member who raised the question requiring interpretation. -/
  raisedBy : MemberId
  /-- Recorded reason for requesting a ruling. -/
  reason : String
  /-- Whether the model permits an appeal from this ruling. -/
  appealable : Bool := true
  /-- Whether an appeal from this request admits debate. -/
  debatable : Bool := true
  /-- Prospective action requested by a point of order. -/
  remedy : Remedy := .none
  deriving DecidableEq

/-- Interpretive answers are data; no claim of semantic truth is built into this type. -/
structure Ruling where
  /-- Approve the proposal, or uphold the point of order and apply its remedy. -/
  allowed : Bool
  /-- Explanation supplied by the interpretive handler. -/
  reason : String
  deriving DecidableEq, Repr

/-- An answered judgment awaiting completion of its appeal opportunity. -/
structure JudgmentRecord (D : MotionDomain) where
  /-- The original request and its frozen context. -/
  request : JudgmentRequest D
  /-- The chair's recorded interpretive answer. -/
  answer : Ruling
  /-- Assembly revision at which the answer was recorded. -/
  revision : Nat
  deriving DecidableEq

/-- Reason an entire question series is suspended. -/
inductive Disposition where
  | tabled | postponed (dueDate : Date) | referred (committee : CommitteeId)
  deriving DecidableEq, Repr

/-- The business classes modeled after opening formalities. -/
inductive BusinessClass where
  | reports | unfinished | newBusiness
  deriving DecidableEq, Repr, Inhabited

/-- A suspended main motion together with its adhering questions and carryover data. -/
structure BusinessBundle (D : MotionDomain) where
  /-- Identity of the bundle's main motion. -/
  id : QuestionId
  /-- The pending series, immediately pending question first. -/
  questions : List (Question D)
  /-- Table, postponement, or committee referral. -/
  disposition : Disposition
  /-- Session in which the series was suspended. -/
  session : Nat
  /-- Civil date on which the series was suspended. -/
  date : Date
  /-- Last session of availability; committee referrals have no such expiry. -/
  expiresAfterSession : Option Nat
  /-- Business class from which the series was suspended. -/
  businessClass : BusinessClass := .newBusiness
  deriving DecidableEq

/-- Coarse control phase of a meeting. -/
inductive Phase where
  | dormant | business | voting | consent | recessed | adjourned
  deriving DecidableEq, Repr, Inhabited

/-- A speech occurrence retained for per-question daily limits. -/
structure Speech where
  /-- Identity of the question addressed. -/
  question : QuestionId
  /-- Identity of the speaker. -/
  member : MemberId
  /-- Civil date on which the speech began. -/
  date : Date
  deriving DecidableEq, Repr

/-- Current floor ownership and speech-clock information. -/
structure Floor where
  /-- Recognized member holding the floor. -/
  member : MemberId
  /-- Clock reading at recognition or speech start. -/
  sinceSecond : Nat
  /-- Whether the recognized member has begun a counted speech. -/
  speaking : Bool := false
  deriving DecidableEq, Repr

/-- A member's latest openly recorded choice in a poll. -/
structure Ballot where
  /-- Voting member's roster identity. -/
  member : MemberId
  /-- Latest choice, including explicit abstention. -/
  vote : Vote
  deriving DecidableEq, Repr

/-- An open poll for one immediately pending question. -/
structure Poll where
  /-- Identity of the question being voted on. -/
  question : QuestionId
  /-- Latest choices, with at most one entry per member in a valid state. -/
  ballots : List Ballot := []
  deriving DecidableEq, Repr

namespace Poll

/-- A new choice replaces this member's previous choice; abstention removes it from the tally. -/
def record (p : Poll) (member : MemberId) (vote : Vote) : Poll :=
  { p with ballots := ⟨member, vote⟩ :: p.ballots.filter (fun b => b.member != member) }

/-- Count affirmative and negative choices, ignoring abstentions. -/
def tally (p : Poll) : Tally :=
  ⟨(p.ballots.filter (fun b => b.vote == .yes)).length,
    (p.ballots.filter (fun b => b.vote == .no)).length⟩

/-- Remove a member's choice when testing its effect on the result. -/
def without (p : Poll) (member : MemberId) : Poll :=
  { p with ballots := p.ballots.filter (fun b => b.member != member) }

end Poll

/-- Observable effects emitted only by an accepted transaction. -/
inductive Event where
  | opened (meeting session : Nat)
  | attendance (member : MemberId) (present : Bool)
  | recognized (member : MemberId)
  | spoke (question : QuestionId) (member : MemberId)
  | proposed (question : QuestionId) (kind : MotionKind) (maker : MemberId)
  | seconded (question : QuestionId) (member : MemberId)
  | stated (question : QuestionId)
  | judgmentRequested (request : Nat) (issue : IssueKind)
  | ruled (request : Nat) (answer : Ruling)
  | appealResolved (request : Nat) (sustained : Bool)
  | voteOpened (question : QuestionId)
  | voteCast (question : QuestionId) (member : MemberId) (vote : Vote)
  | decided (question : QuestionId) (adopted : Bool) (tally : Tally)
  | consentOpened (question : QuestionId)
  | objection (question : QuestionId) (member : MemberId)
  | consentGranted (question : QuestionId)
  | withdrawn (question : QuestionId)
  | suspended (question : QuestionId) (disposition : Disposition)
  | resumed (question : QuestionId)
  | expired (question : QuestionId)
  | recessed (untilSecond : Nat)
  | adjourned (meeting : Nat)
  | timeAdvanced (date : Date) (second : Nat)
  | businessAdvanced (businessClass : BusinessClass)
  deriving DecidableEq, Repr

/-- Input commands carry identities supplied by the host application. -/
inductive Command (D : MotionDomain) where
  | openMeeting (actor : MemberId)
  | advanceBusiness (actor : MemberId)
  | attendance (actor member : MemberId) (present : Bool)
  | requestFloor (actor : MemberId)
  | recognize (actor member : MemberId)
  | speak (actor : MemberId)
  | yieldFloor (actor : MemberId)
  | propose (actor : MemberId) (motion : Motion D)
  | second (actor : MemberId)
  | stateQuestion (actor : MemberId)
  | lackSecond (actor : MemberId)
  | withdraw (actor : MemberId)
  | pointOfOrder (actor : MemberId) (reason : String) (remedy : Remedy)
  | answerJudgment (actor request revision : Nat) (answer : Ruling)
  | continueAfterRuling (actor : MemberId)
  | openVote (actor : MemberId)
  | vote (actor : MemberId) (choice : Vote)
  | announce (actor : MemberId)
  | seekConsent (actor : MemberId)
  | object (actor : MemberId)
  | closeConsent (actor : MemberId)
  | report (actor : MemberId) (committee : CommitteeId) (question : QuestionId)
  | resumeDue (actor : MemberId) (question : QuestionId)
  | advanceTime (actor : MemberId) (date : Date) (second : Nat)
  | resumeRecess (actor : MemberId)
  | nextMeeting (actor : MemberId) (calendar : Calendar) (newSession : Bool)
  | unsupported (name : String)
  deriving DecidableEq

/-- Execution context saved while a point of order interrupts proceedings. -/
structure ReviewContext (D : MotionDomain) where
  /-- Phase to resume after the ruling and any appeal. -/
  phase : Phase
  /-- Interrupted floor ownership, subject to presence on restoration. -/
  floor : Option Floor
  /-- Proposal temporarily displaced by the interruption. -/
  proposal : Option (Question D)
  /-- Open poll temporarily displaced by the interruption. -/
  poll : Option Poll
  deriving DecidableEq

/-- Complete executable state of one configured assembly. -/
structure AssemblyState (D : MotionDomain) where
  /-- Fixed roster and membership rights. -/
  members : List Member
  /-- Identity authorized to perform chair commands. -/
  chair : MemberId
  /-- Registered committee identities available for referral. -/
  committees : List CommitteeId := []
  /-- Current meeting, session, and carryover calendar. -/
  calendar : Calendar
  /-- Current control phase. -/
  phase : Phase := .dormant
  /-- Current portion of the modeled order of business. -/
  businessClass : BusinessClass := .reports
  /-- Members whose presence is currently recorded. -/
  present : List MemberId := []
  /-- Current floor ownership, if any. -/
  floor : Option Floor := none
  /-- Distinct members awaiting recognition. -/
  requests : List MemberId := []
  /-- Speech history used to enforce daily limits. -/
  speeches : List Speech := []
  /-- Active question series, immediately pending question first. -/
  pending : List (Question D) := []
  /-- Motion made but not yet stated by the chair. -/
  proposal : Option (Question D) := none
  /-- Tabled, postponed, and referred question series. -/
  suspended : List (BusinessBundle D) := []
  /-- Resolved question versions in reverse chronological order. -/
  history : List (DecisionRecord D) := []
  /-- Outstanding external interpretive request. -/
  judgment : Option (JudgmentRequest D) := none
  /-- Answered request whose appeal opportunity remains open. -/
  ruling : Option (JudgmentRecord D) := none
  /-- Context interrupted by a point of order. -/
  review : Option (ReviewContext D) := none
  /-- Original proposal temporarily displaced by an appeal. -/
  heldProposal : Option (Question D) := none
  /-- Current open poll, if any. -/
  poll : Option Poll := none
  /-- Recorded objection to the most recent consent request. -/
  consentObjector : Option MemberId := none
  /-- Monotone seconds supplied by the host within a civil date. -/
  nowSecond : Nat := 0
  /-- Clock deadline of the current recess. -/
  recessUntil : Nat := 0
  /-- Fresh identifier above every live question identity. -/
  nextId : Nat := 0
  /-- Number of accepted transactions since initialization. -/
  revision : Nat := 0
  deriving DecidableEq

namespace AssemblyState

/-- Test whether an identity occurs in the configured roster. -/
def isMember {D : MotionDomain} (s : AssemblyState D) (member : MemberId) : Bool :=
  s.members.any (fun m => m.id == member)

/-- Test roster membership and recorded presence together. -/
def isPresent {D : MotionDomain} (s : AssemblyState D) (member : MemberId) : Bool :=
  s.isMember member && s.present.contains member

/-- Test present membership and the right to vote. -/
def canVote {D : MotionDomain} (s : AssemblyState D) (member : MemberId) : Bool :=
  s.present.contains member && s.members.any (fun m => m.id == member && m.votes)

/-- Count present members eligible to contribute to quorum. -/
def quorumCount {D : MotionDomain} (s : AssemblyState D) : Nat :=
  (s.members.filter (fun m => m.countsForQuorum && s.present.contains m.id)).length

/-- Count the full membership entitled to vote. -/
def votingCount {D : MotionDomain} (s : AssemblyState D) : Nat :=
  (s.members.filter (·.votes)).length

/-- Count currently present members entitled to vote. -/
def presentVoters {D : MotionDomain} (s : AssemblyState D) : Nat :=
  (s.members.filter (fun m => m.votes && s.present.contains m.id)).length

/-- Compare eligible presence with the configured quorum. -/
def hasQuorum {D : MotionDomain} (rules : Rules) (s : AssemblyState D) : Bool :=
  rules.quorum ≤ s.quorumCount

/-- Retrieve the immediately pending question, if any. -/
def activeQuestion {D : MotionDomain} (s : AssemblyState D) : Option (Question D) :=
  s.pending.head?

/-- All live question versions, including interrupted and suspended proposals. -/
def allQuestions {D : MotionDomain} (s : AssemblyState D) : List (Question D) :=
  s.pending ++ s.proposal.toList ++ s.heldProposal.toList ++
    s.review.toList.flatMap (fun r => r.proposal.toList) ++ s.suspended.flatMap (·.questions)

/-- Every amendment refers to a matching parent later in its pending series. -/
def ValidTargets {D : MotionDomain} : List (Question D) → Prop
  | [] => True
  | q :: qs =>
    (match q.motion with
     | .main _ => qs = []
     | .primary parent _ => ∃ target ∈ qs, target.id = parent ∧ target.motion.kind = .main
     | .secondary parent _ => ∃ target ∈ qs,
         target.id = parent ∧ target.motion.kind = .primary
     | _ => True) ∧ ValidTargets qs

instance instDecidableValidTargets {D : MotionDomain} (qs : List (Question D)) :
    Decidable (ValidTargets qs) :=
  match qs with
  | [] => isTrue trivial
  | q :: qs =>
    letI := instDecidableValidTargets qs
    by unfold ValidTargets; cases q.motion <;> infer_instance

/-- Structural integrity checked at initialization and each transaction boundary. -/
def WellFormed {D : MotionDomain} (s : AssemblyState D) : Prop :=
  (s.members.map (·.id)).Nodup ∧ s.present.Nodup ∧
  (∀ m ∈ s.present, s.isMember m = true) ∧
  (s.allQuestions.map (·.id)).Nodup ∧
  (∀ q ∈ s.allQuestions, q.id < s.nextId) ∧
  (∀ p ∈ s.poll.toList, (p.ballots.map (·.member)).Nodup) ∧
  s.calendar.Valid ∧ s.requests.Nodup ∧
  (∀ m ∈ s.requests, s.isPresent m = true) ∧
  (∀ f ∈ s.floor.toList, s.isPresent f.member = true) ∧
  ValidTargets s.pending ∧ (∀ b ∈ s.suspended, ValidTargets b.questions)

instance {D : MotionDomain} (s : AssemblyState D) : Decidable s.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _))

end AssemblyState

end Parliament
