/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Procedure.Agenda

/-!
# Transactional engine and certified legal steps

The boundary validates structural invariants and event safety as well as deriving the
command's premises. A rejected transaction returns no replacement state or events.
-/

@[expose] public section

namespace Parliament

variable {D : MotionDomain}

/-- External role authorization, independent of motion-specific premises. -/
def Authorized (s : AssemblyState D) : Command D → Prop
  | .openMeeting a | .advanceBusiness a | .attendance a .. | .recognize a _ | .stateQuestion a |
    .lackSecond a | .answerJudgment a .. | .continueAfterRuling a | .openVote a |
    .announce a | .seekConsent a | .closeConsent a | .report a .. | .resumeDue a _ |
    .advanceTime a .. | .resumeRecess a | .nextMeeting a .. => a = s.chair
  | .requestFloor a | .speak a | .yieldFloor a | .propose a _ | .second a |
    .withdraw a | .pointOfOrder a .. | .vote a _ | .object a => s.isPresent a = true
  | .unsupported _ => True

instance (s : AssemblyState D) (command : Command D) : Decidable (Authorized s command) := by
  cases command <;> unfold Authorized <;> infer_instance

/-- The source question may be decided without quorum only for the modeled emergencies. -/
def DecisionAuthorized (rules : Rules) (s : AssemblyState D) (id : QuestionId) : Prop :=
  ∃ q ∈ s.pending, q.id = id ∧
    (Procedure.allowsNoQuorum q.motion = true ∨ s.hasQuorum rules = true)

instance (rules : Rules) (s : AssemblyState D) (id : QuestionId) :
    Decidable (DecisionAuthorized rules s id) :=
  inferInstanceAs (Decidable (∃ q ∈ s.pending, _))

/-- A counted decision agrees with its actual source poll and the prescribed threshold. -/
def CountedDecision (rules : Rules) (s : AssemblyState D) (id : QuestionId)
    (adopted : Bool) (tally : Tally) : Prop :=
  ∃ q ∈ s.pending, ∃ poll ∈ s.poll.toList,
    q.id = id ∧ poll.question = id ∧ tally = poll.tally ∧
      adopted = Procedure.outcome rules s q poll

instance (rules : Rules) (s : AssemblyState D) (id : QuestionId)
    (adopted : Bool) (tally : Tally) : Decidable (CountedDecision rules s id adopted tally) :=
  inferInstanceAs (Decidable (∃ q ∈ s.pending, ∃ poll ∈ s.poll.toList, _))

/-- Event contracts checked independently of the procedural rule program. -/
def EventSafe (rules : Rules) (s : AssemblyState D) : Event → Prop
  | .decided id adopted tally =>
    (adopted = true → DecisionAuthorized rules s id) ∧
    (s.phase = .voting → CountedDecision rules s id adopted tally)
  | .consentGranted id => DecisionAuthorized rules s id
  | .voteCast _ member _ => s.canVote member = true
  | .recognized member => s.isPresent member = true
  | _ => True

instance (rules : Rules) (s : AssemblyState D) (event : Event) :
    Decidable (EventSafe rules s event) := by
  cases event <;> unfold EventSafe <;> infer_instance

/-- Every event emitted by a transaction satisfies its independent contract. -/
def EventsSafe (rules : Rules) (s : AssemblyState D) (events : List Event) : Prop :=
  ∀ e ∈ events, EventSafe rules s e

instance (rules : Rules) (s : AssemblyState D) (events : List Event) :
    Decidable (EventsSafe rules s events) := inferInstanceAs (Decidable (∀ e ∈ events, _))

/-- Inference semantics: the rule program derives a candidate and its contracts hold. -/
inductive LegalStep (rules : Rules) (s : AssemblyState D) (command : Command D) :
    AssemblyState D → List Event → Prop where
  | derive (valid : s.WellFormed) (authorized : Authorized s command)
      {candidate : AssemblyState D} {events : List Event}
      (derivation : RuleProgram.Derives (Procedure.procedure rules s command) (candidate, events))
      (preserves : candidate.WellFormed) (safe : EventsSafe rules s events) :
      LegalStep rules s command { candidate with revision := s.revision + 1 } events

/-- Check a command atomically. Invalid commands produce neither state nor events. -/
def step (rules : Rules) (s : AssemblyState D) (command : Command D) :
    Except RuleError (AssemblyState D × List Event) :=
  if !decide s.WellFormed then .error .invalidState
  else if !decide (Authorized s command) then .error .notMember
  else match (Procedure.procedure rules s command).evaluate with
  | .error error => .error error
  | .ok (candidate, events) =>
    if decide (candidate.WellFormed ∧ EventsSafe rules s events) then
      .ok ({ candidate with revision := s.revision + 1 }, events)
    else .error .invalidState

theorem step_sound (rules : Rules) (s next : AssemblyState D) (command : Command D)
    (events : List Event) (h : step rules s command = .ok (next, events)) :
    LegalStep rules s command next events := by
  unfold step at h
  split at h
  next hbad => contradiction
  next hv =>
    have valid : s.WellFormed := by simpa using hv
    split at h
    next hbad => contradiction
    next ha =>
      have authorized : Authorized s command := by simpa using ha
      split at h
      next error he => contradiction
      next candidate es he =>
        split at h
        next hc =>
          have checks : candidate.WellFormed ∧ EventsSafe rules s es := by simpa using hc
          cases h
          exact .derive valid authorized
            ((RuleProgram.evaluate_iff _ _).mp he) checks.1 checks.2
        next hc => contradiction

theorem step_complete (rules : Rules) (s next : AssemblyState D) (command : Command D)
    (events : List Event) (h : LegalStep rules s command next events) :
    step rules s command = .ok (next, events) := by
  cases h with
  | derive valid authorized derivation preserves safe =>
    simp [step, valid, authorized, (RuleProgram.evaluate_iff _ _).mpr derivation,
      preserves, safe]

theorem step_iff (rules : Rules) (s next : AssemblyState D) (command : Command D)
    (events : List Event) :
    step rules s command = .ok (next, events) ↔ LegalStep rules s command next events :=
  ⟨step_sound rules s next command events, step_complete rules s next command events⟩

theorem LegalStep.authorized {rules : Rules} {s next : AssemblyState D}
    {command : Command D} {events : List Event}
    (h : LegalStep rules s command next events) : Authorized s command := by
  cases h with | derive _ authorized _ _ _ => exact authorized

theorem LegalStep.wellFormed {rules : Rules} {s next : AssemblyState D}
    {command : Command D} {events : List Event}
    (h : LegalStep rules s command next events) : next.WellFormed := by
  cases h with
  | derive _ _ _ preserves _ => exact preserves

theorem LegalStep.eventsSafe {rules : Rules} {s next : AssemblyState D}
    {command : Command D} {events : List Event}
    (h : LegalStep rules s command next events) : EventsSafe rules s events := by
  cases h with | derive _ _ _ _ safe => exact safe

theorem LegalStep.deterministic {rules : Rules} {s next next' : AssemblyState D}
    {command : Command D} {events events' : List Event}
    (h : LegalStep rules s command next events) (h' : LegalStep rules s command next' events') :
    next = next' ∧ events = events' := by
  have he := (step_complete rules s next command events h).symm.trans
    (step_complete rules s next' command events' h')
  exact Prod.mk.inj (Except.ok.inj he)

theorem LegalStep.revision {rules : Rules} {s next : AssemblyState D}
    {command : Command D} {events : List Event}
    (h : LegalStep rules s command next events) : next.revision = s.revision + 1 := by
  cases h
  rfl

theorem LegalStep.substantiveDecision_quorum {rules : Rules} {s next : AssemblyState D}
    {command : Command D} {events : List Event} {id : QuestionId} {tally : Tally}
    (h : LegalStep rules s command next events)
    (he : Event.decided id true tally ∈ events)
    (ordinary : ∀ q ∈ s.pending, q.id = id → Procedure.allowsNoQuorum q.motion = false) :
    s.hasQuorum rules = true := by
  have safe := h.eventsSafe _ he
  obtain ⟨q, hq, hid, hquorum⟩ := safe.1 rfl
  rcases hquorum with emergency | quorum
  · simp [ordinary q hq hid] at emergency
  · exact quorum

theorem LegalStep.countedDecision {rules : Rules} {s next : AssemblyState D}
    {command : Command D} {events : List Event} {id : QuestionId} {tally : Tally}
    {adopted : Bool} (h : LegalStep rules s command next events)
    (voting : s.phase = .voting) (he : Event.decided id adopted tally ∈ events) :
    CountedDecision rules s id adopted tally := (h.eventsSafe _ he).2 voting

/-- Construct a validated empty session. Membership changes require a new configuration. -/
def initializeAssembly (D : MotionDomain) (rules : Rules) (members : List Member)
    (chair : MemberId) (calendar : Calendar) (committees : List CommitteeId := []) :
    Except RuleError (AssemblyState D) :=
  let s : AssemblyState D := { members, chair, calendar, committees }
  if decide s.WellFormed && rules.quorum > 0 && rules.speechesPerQuestion > 0 &&
      rules.speechSeconds > 0 && decide committees.Nodup then .ok s
  else .error .invalidConfiguration

end Parliament
