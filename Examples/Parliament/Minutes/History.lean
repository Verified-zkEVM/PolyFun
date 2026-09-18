/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Interaction

/-! # Certified, extensible meeting histories -/

@[expose] public section

namespace Parliament

variable {D : MotionDomain}

/-- Accepted inputs in chronological order, indexed by their initial and final states. -/
inductive History (rules : Rules) (initial : AssemblyState D) : AssemblyState D → Type where
  | nil : History rules initial initial
  | snoc {state : AssemblyState D} (past : History rules initial state)
      (input : EnabledInput rules state) : History rules initial input.next

/-- The raw command journal; certificates are reconstructed rather than serialized. -/
def History.commands {rules : Rules} {initial state : AssemblyState D} :
    History rules initial state → List (Command D)
  | .nil => []
  | .snoc past input => past.commands ++ [input.command]

/-- Observable effects of the accepted history. -/
def History.events {rules : Rules} {initial state : AssemblyState D} :
    History rules initial state → List Event
  | .nil => []
  | .snoc past input => past.events ++ input.events

theorem History.legalTrace {rules : Rules} {initial state : AssemblyState D}
    (history : History rules initial state) :
    LegalTrace rules initial history.commands state history.events := by
  induction history with
  | nil => exact .nil _
  | snoc past input ih =>
    simpa [History.commands, History.events] using
      ih.append (LegalTrace.cons input.legal (.nil input.next))

theorem History.replays {rules : Rules} {initial state : AssemblyState D}
    (history : History rules initial state) :
    replay rules initial history.commands = .ok (state, history.events) :=
  replay_complete history.legalTrace

/-- An initialized assembly with its exact accepted execution history. -/
structure Journal (D : MotionDomain) (rules : Rules) where
  /-- Validated starting state, before any commands. -/
  initial : AssemblyState D
  /-- Structural integrity of the starting state. -/
  initialValid : initial.WellFormed
  /-- State after the accepted commands. -/
  state : AssemblyState D
  /-- Certified path from initialization to the current state. -/
  history : History rules initial state

/-- Start a journal only from a structurally valid assembly. -/
def Journal.start (rules : Rules) (initial : AssemblyState D) :
    Except RuleError (Journal D rules) :=
  if h : initial.WellFormed then .ok ⟨initial, h, initial, .nil⟩
  else .error .invalidState

/-- Extend through the existing polynomial meeting system's update operation. -/
def Journal.accept {rules : Rules} (journal : Journal D rules)
    (input : EnabledInput rules journal.state) : Journal D rules :=
  ⟨journal.initial, journal.initialValid,
    (meetingSystem D rules).update journal.state input, .snoc journal.history input⟩

/-- Validate a raw command without changing the original journal on rejection. -/
def Journal.submit {rules : Rules} (journal : Journal D rules) (command : Command D) :
    Except RuleError (Journal D rules) := do
  let input ← checkInput rules journal.state command
  pure (journal.accept input)

/-- Replay additional commands, identifying the first failing relative index. -/
def Journal.replay {rules : Rules} (journal : Journal D rules) :
    List (Command D) → Except (Nat × RuleError) (Journal D rules)
  | [] => .ok journal
  | command :: commands =>
    match journal.submit command with
    | .error error => .error (0, error)
    | .ok next =>
      match next.replay commands with
      | .ok result => .ok result
      | .error (index, error) => .error (index + 1, error)

theorem Journal.wellFormed {rules : Rules} (journal : Journal D rules) :
    journal.state.WellFormed := journal.history.legalTrace.wellFormed journal.initialValid

theorem Journal.accept_commands {rules : Rules} (journal : Journal D rules)
    (input : EnabledInput rules journal.state) :
    (journal.accept input).history.commands = journal.history.commands ++ [input.command] := rfl

theorem Journal.accept_update {rules : Rules} (journal : Journal D rules)
    (input : EnabledInput rules journal.state) :
    (journal.accept input).state = (meetingSystem D rules).update journal.state input := rfl

end Parliament
