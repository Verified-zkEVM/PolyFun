/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Lean.Data.Json
public import Mathlib.Data.List.Basic

/-! # A tiny local notebook

IDs are creation positions. Editing appends a version; it never changes an ID or deletes text.
The expected version prevents an old view from silently overwriting a newer edit. Text is opaque:
the model neither trims whitespace nor interprets Markdown. There is no parliamentary machinery.
-/

@[expose] public section

namespace Notes

/-- A note retains its current text and every earlier version, oldest first. -/
structure Note where
  /-- Current opaque text. -/
  text : String
  /-- Earlier text, oldest first. -/
  previous : List String := []
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- Versions start at zero and increase once per accepted edit. -/
def Note.version (note : Note) : Nat := note.previous.length

/-- Full replacement is deliberately the only editing operation. -/
def Note.edit (note : Note) (text : String) : Note :=
  ⟨text, note.previous ++ [note.text]⟩

@[simp] theorem Note.version_edit (note : Note) (text : String) :
    (note.edit text).version = note.version + 1 := by simp [version, edit]

/-- The initial text and every accepted replacement remain available. -/
def Note.versions (note : Note) : List String := note.previous ++ [note.text]

@[simp] theorem Note.versions_edit (note : Note) (text : String) :
    (note.edit text).versions = note.versions ++ [text] := rfl

/-- A notebook has no hidden clock, random ID allocator, or filesystem dependency. -/
abbrev Notebook := List Note

/-- Only these two operations can modify the notebook. -/
inductive Command where
  | create (text : String)
  | edit (id expectedVersion : Nat) (text : String)
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- Expected domain failures, distinct from input and filesystem failures. -/
inductive Error where
  | unknownNote (id : Nat)
  | staleVersion (expected actual : Nat)
  deriving DecidableEq, Repr

/-- A diagnostic that is useful without knowing Lean constructor names. -/
def Error.message : Error → String
  | .unknownNote id => s!"No note has ID {id}."
  | .staleVersion expected actual =>
    s!"Stale edit: expected version {expected}, but the current version is {actual}."

/-- Validate first; a rejected edit has no successor state. -/
def step (notes : Notebook) : Command → Except Error Notebook
  | .create text => .ok (notes ++ [⟨text, []⟩])
  | .edit id expected text => do
    let some note := notes[id]? | throw (.unknownNote id)
    if note.version != expected then throw (.staleVersion expected note.version)
    return notes.set id (note.edit text)

/-- Replay is the authoritative decoder of the command journal. -/
def replay (commands : List Command) : Except Error Notebook := commands.foldlM step []

/-- A committed journal carries evidence that its cached notebook is exactly its replay. -/
structure Journal where
  /-- Accepted inputs in execution order. -/
  commands : List Command
  /-- Cached result of replaying the accepted inputs. -/
  notes : Notebook
  valid : replay commands = .ok notes

/-- The empty local notebook. -/
def Journal.empty : Journal := ⟨[], [], rfl⟩

/-- Extend a certified cache by one checked step. Loading still validates the entire journal. -/
def Journal.accept (journal : Journal) (command : Command) : Except Error Journal :=
  match h : step journal.notes command with
  | .error error => .error error
  | .ok notes => .ok ⟨journal.commands ++ [command], notes, by
      simp only [replay, List.foldlM_append]
      change (replay journal.commands >>= fun initial => [command].foldlM step initial) = _
      rw [journal.valid]
      simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
      exact h⟩

/-- History browsing reconstructs a prefix and cannot mutate the committed journal. -/
def Journal.at (journal : Journal) (revision : Nat) : Except Error Notebook :=
  replay (journal.commands.take revision)

/-- The portable file contains commands, never a purported proof or cached notebook. -/
structure WireJournal where
  /-- Explicit schema and command-semantics version. -/
  version : Nat := 1
  /-- Inputs replayed and checked on load. -/
  commands : List Command := []
  deriving Lean.ToJson, Lean.FromJson

/-- Reject unknown formats and illegal histories instead of repairing them. -/
def WireJournal.restore (wire : WireJournal) : Except String Journal := do
  if wire.version != 1 then throw "Unsupported Notes journal version."
  match h : replay wire.commands with
  | .error error => throw error.message
  | .ok notes => return ⟨wire.commands, notes, h⟩

/-- A persisted snapshot serializes exactly the accepted commands. -/
def Journal.wire (journal : Journal) : WireJournal := ⟨1, journal.commands⟩

end Notes
