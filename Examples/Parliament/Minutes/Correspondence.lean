/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Minutes.Document

/-! # Reconstruction and incremental documents agree for the same accepted journal -/

public section

namespace Parliament

variable {D : MotionDomain}

/-- No choice of proof or reconstruction path changes the document for a fixed command history. -/
theorem History.entries_determined {rules : Rules} {initial a b : AssemblyState D}
    (first : History rules initial a) (second : History rules initial b)
    (same : first.commands = second.commands) : first.entries = second.entries := by
  induction first generalizing b with
  | nil =>
    cases second with
    | nil => rfl
    | snoc past input => simp [History.commands] at same
  | @snoc source past input ih =>
    cases second with
    | nil => simp [History.commands] at same
    | @snoc otherSource otherPast otherInput =>
      have parts : past.commands = otherPast.commands ∧ input.command = otherInput.command :=
        List.append_singleton_inj.mp same
      have states : source = otherSource :=
        (replay_deterministic past.replays (by rw [parts.1]; exact otherPast.replays)).1
      subst otherSource
      have entries := ih otherPast parts.1
      rcases input with ⟨command, next, events, legal⟩
      rcases otherInput with ⟨otherCommand, otherNext, otherEvents, otherLegal⟩
      dsimp at parts
      obtain ⟨_, rfl⟩ := parts
      obtain ⟨rfl, rfl⟩ := legal.deterministic otherLegal
      simp only [History.entries, entries]

/-- Reconstructing a journal leaves every per-meeting draft unchanged. -/
theorem draftMinutes_reconstruction {rules : Rules} (first second : Journal D rules)
    (initial : first.initial = second.initial)
    (commands : first.history.commands = second.history.commands) (meeting : Nat) :
    (draftMinutes first meeting).entries = (draftMinutes second meeting).entries := by
  rcases first with ⟨initial₁, valid₁, state₁, history₁⟩
  rcases second with ⟨initial₂, valid₂, state₂, history₂⟩
  dsimp at initial commands ⊢
  subst initial₂
  simp only [draftMinutes, DraftMinutes.entries,
    History.entries_determined history₁ history₂ commands]

end Parliament
