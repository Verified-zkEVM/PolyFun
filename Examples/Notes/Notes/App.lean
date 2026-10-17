/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Notes.Dialogue
public import PolyFun.PFunctor.Dynamical.DynComputation.Resumable

/-! # A resumable local Notes application

The machine exposes reading, printing and persistence as polynomial operations. The real backend
and the memory tests execute the same machine. A candidate becomes committed only on successful
persistence. History navigation is display state, not a command in the notebook journal.
-/

@[expose] public section

namespace Notes

open PolyFunIO

/-- Handler-facing display state; `none` follows the live journal. -/
structure View where
  /-- Selected journal prefix, or the live revision. -/
  cursor : Option Nat := none
  deriving DecidableEq, Repr

/-- The domain journal and ephemeral view remain visibly separate. -/
structure Session where
  /-- Last acknowledged certified notebook. -/
  journal : Journal
  /-- Ephemeral read-only navigation, never serialized. -/
  view : View := {}

/-- Render exact text with stable IDs and explicit version labels. -/
def render (session : Session) : String :=
  let revision := session.view.cursor.getD session.journal.commands.length
  match session.journal.at revision with
  | .error error => error.message
  | .ok notes =>
    let label := if session.view.cursor.isSome then " (history; use live to edit)" else ""
    s!"Revision {revision}{label}\n" ++
    String.intercalate "\n" (notes.zipIdx.map fun (note, id) ↦
      s!"[{id} v{note.version}] {note.text}")

/-- Effects expose the IO boundary, not the filesystem implementation. -/
inductive Effect where
  | read
  | tell (message : String)
  | preview (notes : Notebook)

/-- Every fallible backend operation has an explicit error response. -/
def InteractionEffects : PFunctor where
  A := Effect
  B
    | .read => Except String Action
    | .tell _ => Except String Unit
    | .preview _ => Except String (Except InputError (Option Command))

/-- Storage is a separate capability from every interactive or speculative workflow. -/
def StorageEffects : PFunctor := ⟨Journal, fun _ => Except String Unit⟩

/-- The application requests interaction or storage, retaining dependent response types. -/
abbrev Effects := InteractionEffects + StorageEffects

/-- Returning machine phases retain the last acknowledged session. -/
inductive State where
  | ready (session : Session)
  | preview (session : Session)
  | saving (session : Session) (candidate : Journal)
  | notice (session : Session) (text : String) (exitCode : Option UInt32 := none)
  | done (session : Session) (code : UInt32)

/-- Pending writes never appear as committed state. -/
def State.committed : State → Journal
  | .ready s | .preview s | .saving s _ | .notice s .. | .done s _ => s.journal

/-- Navigate without recording or changing a notebook command. -/
def navigate (session : Session) (cursor : Option Nat) : Session :=
  { session with view := ⟨cursor.map (min session.journal.commands.length)⟩ }

@[simp] theorem navigate_journal (session : Session) (cursor : Option Nat) :
    (navigate session cursor).journal = session.journal := rfl

/-- Pure UI dispatch prepares a write or retains the current committed journal. -/
def handle (session : Session) : Action → State
  | .preview =>
    if session.view.cursor.isSome then .notice session "History is read-only; enter live to edit."
    else .preview session
  | .command command =>
    if session.view.cursor.isSome then .notice session "History is read-only; enter live to edit."
    else match session.journal.accept command with
      | .error error => .notice session error.message
      | .ok candidate => .saving session candidate
  | .history revision => let s := navigate session (some revision); .notice s (render s)
  | .back =>
    let s := navigate session (some (session.view.cursor.getD session.journal.commands.length - 1))
    .notice s (render s)
  | .forward =>
    let s := navigate session (some (session.view.cursor.getD session.journal.commands.length + 1))
    .notice s (render s)
  | .live => let s := navigate session none; .notice s (render s)
  | .list => .notice session (render session)
  | .quit => .done session 0
  | .invalid message => .notice session message

/-- No UI action changes committed data before the persistence acknowledgement. -/
theorem handle_committed (session : Session) (action : Action) :
    (handle session action).committed = session.journal := by
  cases action <;> simp only [handle]
  · split
    · rfl
    · split <;> rfl
  · split <;> rfl
  all_goals rfl

/-- One effect, or a final result. -/
def machineStep : State → (Session × UInt32) ⊕ Effects.Obj State
  | .done session code => .inl (session, code)
  | .ready session => .inr ⟨.inl .read, fun response ↦ match response with
      | .ok action => handle session action
      | .error error => .notice session error (some 1)⟩
  | .preview session => .inr ⟨.inl (.preview session.journal.notes), fun response ↦
      match response with
      | .error error => .notice session error (some 1)
      | .ok (.error error) => .notice session error.message
      | .ok (.ok none) => .notice session "Cancelled; no command submitted."
      | .ok (.ok (some command)) => handle session (.command command)⟩
  | .saving session candidate => .inr ⟨.inr candidate, fun response ↦ match response with
      | .ok () => .notice ⟨candidate, {}⟩ s!"Saved revision {candidate.commands.length}."
      | .error error => .notice session
          ("Save failed; stop and reload the journal before retrying. " ++ error) (some 1)⟩
  | .notice session text code => .inr ⟨.inl (.tell text), fun response ↦ match response with
      | .error _ => .done session 1
      | .ok () => match code with
        | some code => .done session code
        | none => .ready session⟩

/-- The generic resumable driver supplies the application loop. -/
def application : PFunctor.DynSystem.DynComputation Effects Session (Session × UInt32) :=
  .ofStep machineStep .ready

end Notes
