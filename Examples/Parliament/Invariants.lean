/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Interaction

/-! # Consequences of the meeting invariants and voting operations -/

public section

namespace Parliament

theorem Poll.record_lastChoice (poll : Poll) (member : MemberId) (vote : Vote) :
    ((poll.record member vote).ballots.filter (fun b => b.member == member)) =
      [⟨member, vote⟩] := by
  simp [Poll.record, List.filter_filter]

theorem Poll.record_idempotent (poll : Poll) (member : MemberId) (vote : Vote) :
    (poll.record member vote).record member vote = poll.record member vote := by
  simp [Poll.record, List.filter_filter]

theorem Poll.record_replaces (poll : Poll) (member : MemberId) (old new : Vote) :
    (poll.record member old).record member new = poll.record member new := by
  simp [Poll.record, List.filter_filter]

theorem LegalStep.uniqueQuestionIds {D : MotionDomain} {rules : Rules}
    {s next : AssemblyState D} {command : Command D} {events : List Event}
    (h : LegalStep rules s command next events) : (next.allQuestions.map (·.id)).Nodup :=
  h.wellFormed.2.2.2.1

theorem LegalStep.uniqueVoters {D : MotionDomain} {rules : Rules}
    {s next : AssemblyState D} {command : Command D} {events : List Event}
    (h : LegalStep rules s command next events) (poll : Poll) (hp : poll ∈ next.poll.toList) :
    (poll.ballots.map (·.member)).Nodup := h.wellFormed.2.2.2.2.2.1 poll hp

theorem LegalStep.validAmendmentTargets {D : MotionDomain} {rules : Rules}
    {s next : AssemblyState D} {command : Command D} {events : List Event}
    (h : LegalStep rules s command next events) : AssemblyState.ValidTargets next.pending :=
  h.wellFormed.2.2.2.2.2.2.2.2.2.2.1

/-- Handler implementation does not affect step safety: it only selects certified directions. -/
theorem handler_independent_safety {D : MotionDomain} (rules : Rules)
    (handler : (s : AssemblyState D) → Option (EnabledInput rules s)) (s : AssemblyState D)
    (input : EnabledInput rules s) (_h : handler s = some input) :
    input.next.WellFormed := input.legal.wellFormed

end Parliament
