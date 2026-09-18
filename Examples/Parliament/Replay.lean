/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Engine

/-! # Replay, legal traces, and the decision register -/

@[expose] public section

namespace Parliament

variable {D : MotionDomain}

/-- The first rejected command together with its successfully replayed prefix. -/
structure ReplayError (D : MotionDomain) where
  /-- Zero-based index of the rejected command in the supplied journal. -/
  index : Nat
  /-- First command that failed validation. -/
  command : Command D
  /-- Rule rejection returned by that command. -/
  error : RuleError
  /-- State reached immediately before rejection. -/
  state : AssemblyState D
  /-- Successfully applied commands preceding the rejection. -/
  acceptedPrefix : List (Command D)
  /-- Events produced by the accepted prefix only. -/
  events : List Event

/-- Replay stops at the first rejection and preserves the accepted prefix. -/
def replay (rules : Rules) (s : AssemblyState D) : List (Command D) →
    Except (ReplayError D) (AssemblyState D × List Event)
  | [] => .ok (s, [])
  | command :: commands =>
    match step rules s command with
    | .error error => .error ⟨0, command, error, s, [], []⟩
    | .ok (next, events) =>
      match replay rules next commands with
      | .ok (last, later) => .ok (last, events ++ later)
      | .error error => .error { error with
          index := error.index + 1, acceptedPrefix := command :: error.acceptedPrefix,
          events := events ++ error.events }

/-- Inductive finite composition of legal steps, preserving event order. -/
inductive LegalTrace (rules : Rules) : AssemblyState D → List (Command D) →
    AssemblyState D → List Event → Prop where
  | nil (s : AssemblyState D) : LegalTrace rules s [] s []
  | cons {s mid last : AssemblyState D} {command : Command D} {commands : List (Command D)}
      {events later : List Event}
      (head : LegalStep rules s command mid events)
      (tail : LegalTrace rules mid commands last later) :
      LegalTrace rules s (command :: commands) last (events ++ later)

theorem replay_sound (rules : Rules) (s : AssemblyState D) (commands : List (Command D))
    (last : AssemblyState D) (events : List Event)
    (h : replay rules s commands = .ok (last, events)) :
    LegalTrace rules s commands last events := by
  induction commands generalizing s events with
  | nil =>
    cases h
    exact .nil _
  | cons command commands ih =>
    cases hs : step rules s command with
    | error error => simp [replay, hs] at h
    | ok result =>
      rcases result with ⟨mid, first⟩
      cases ht : replay rules mid commands with
      | error error => simp [replay, hs, ht] at h
      | ok result =>
        rcases result with ⟨last', later⟩
        have he : (last', first ++ later) = (last, events) := by
          simpa [replay, hs, ht] using h
        cases he
        exact .cons (step_sound rules s mid command first hs) (ih mid later ht)

theorem replay_complete {rules : Rules} {s last : AssemblyState D}
    {commands : List (Command D)} {events : List Event}
    (h : LegalTrace rules s commands last events) :
    replay rules s commands = .ok (last, events) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [replay, step_complete _ _ _ _ _ head, ih]

theorem replay_iff (rules : Rules) (s : AssemblyState D) (commands : List (Command D))
    (last : AssemblyState D) (events : List Event) :
    replay rules s commands = .ok (last, events) ↔ LegalTrace rules s commands last events :=
  ⟨replay_sound rules s commands last events, replay_complete⟩

theorem LegalTrace.wellFormed {rules : Rules} {s last : AssemblyState D}
    {commands : List (Command D)} {events : List Event}
    (h : LegalTrace rules s commands last events) (initial : s.WellFormed) : last.WellFormed := by
  induction h with
  | nil _ => exact initial
  | cons head tail ih => exact ih head.wellFormed

theorem LegalTrace.append {rules : Rules} {s mid last : AssemblyState D}
    {first second : List (Command D)} {events later : List Event}
    (h : LegalTrace rules s first mid events) (h' : LegalTrace rules mid second last later) :
    LegalTrace rules s (first ++ second) last (events ++ later) := by
  induction h with
  | nil _ => exact h'
  | cons head tail ih => simpa [List.append_assoc] using LegalTrace.cons head (ih h')

theorem replay_deterministic {rules : Rules} {s a b : AssemblyState D}
    {commands : List (Command D)} {ea eb : List Event}
    (ha : replay rules s commands = .ok (a, ea)) (hb : replay rules s commands = .ok (b, eb)) :
    a = b ∧ ea = eb := Prod.mk.inj (Except.ok.inj (ha.symm.trans hb))

/-- A rejection retains exactly a successfully replayable prefix and the failing transaction. -/
theorem replay_error_prefix (rules : Rules) (commands : List (Command D))
    (s : AssemblyState D) (error : ReplayError D)
    (h : replay rules s commands = .error error) :
    replay rules s error.acceptedPrefix = .ok (error.state, error.events) ∧
      step rules error.state error.command = .error error.error ∧
      error.index = error.acceptedPrefix.length := by
  induction commands generalizing s error with
  | nil => simp [replay] at h
  | cons command commands ih =>
    cases hs : step rules s command with
    | error reason =>
      simp only [replay, hs, Except.error.injEq] at h
      subst error
      exact ⟨rfl, hs, rfl⟩
    | ok result =>
      rcases result with ⟨mid, first⟩
      cases ht : replay rules mid commands with
      | ok result => simp [replay, hs, ht] at h
      | error later =>
        simp only [replay, hs, ht, Except.error.injEq] at h
        subst error
        obtain ⟨hp, hf, hi⟩ := ih mid later ht
        exact ⟨by simp [replay, hs, hp], hf, by simpa using hi⟩

/-- Resolved wording and outcomes in chronological order, paired with `minutes` for rendering. -/
def decisionRegister (s : AssemblyState D) : List (DecisionRecord D) := s.history.reverse

/-- Events suitable for a decision register. Wording is resolved from the command journal. -/
def Event.isMinute : Event → Bool
  | .proposed .. | .stated _ | .ruled .. | .appealResolved .. | .decided .. |
    .consentGranted _ | .withdrawn _ | .suspended .. | .resumed _ | .expired _ |
    .opened .. | .recessed _ | .adjourned _ => true
  | _ => false

/-- Project a journal's events to its decision and business register. -/
def minutes (events : List Event) : List Event := events.filter Event.isMinute

theorem minutes_append (a b : List Event) : minutes (a ++ b) = minutes a ++ minutes b := by
  simp [minutes]

theorem speech_not_in_minutes (events : List Event) (q : QuestionId) (m : MemberId) :
    Event.spoke q m ∉ minutes events := by
  simp [minutes, Event.isMinute]

end Parliament
