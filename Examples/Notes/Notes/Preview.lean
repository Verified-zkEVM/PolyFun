/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Notes.Model
public import PolyFunIO.Console
public import PolyFun.PFunctor.Free.Cursor.Occurrence

/-! # Read-only edit preparation

The dialogue has console capability only. It returns an ordinary command on confirmation;
the application must revalidate that command and acknowledge persistence separately.
Typed cursor branching can compare save and cancel without asking for either answer.
-/

@[expose] public section

namespace Notes.Preview

open PolyFunIO PFunctor

/-- One pending edit, before asking whether to submit it. -/
structure Proposal where
  /-- Command revalidated by the writer if selected. -/
  command : Command
  /-- Original text, with whitespace retained. -/
  original : String
  /-- Proposed replacement, with whitespace retained. -/
  replacement : String
  deriving DecidableEq, Repr

/-- Collect and validate a proposal without obtaining any storage capability. -/
def prepare (notes : Notebook) : Form Proposal := do
  let id ← Form.natural "Note ID: "
  let version ← Form.natural "Expected version: "
  let text ← Form.text "Replacement text: "
  let command := Command.edit id version text
  match step notes command with
  | .error error => throw (.invalid error.message)
  | .ok _ =>
    let some original := notes[id]? | throw (.invalid "Unknown note.")
    return ⟨command, original.text, text⟩

/-- Stable query at which a prepared edit can be inspected under explicit choices. -/
def decision : ConsoleOp := .readLine "save / cancel: "

/-- Display both texts before asking for a decision. EOF and cancellation submit nothing. -/
def confirm (proposal : Proposal) : Form (Option Command) := do
  Form.write s!"Original:\n{proposal.original}\nProposed:\n{proposal.replacement}\n"
  let answer ← monadLift (FreeM.lift (P := Console) decision)
  match answer.map (·.trimAscii.toString) with
  | some "save" => return some proposal.command
  | some "cancel" => return none
  | none => throw .endOfInput
  | _ => throw (.invalid "Choose save or cancel; no command submitted.")

/-- The same finite workflow drives real streams, memory tests, and representation demos. -/
def form (notes : Notebook) : Form (Option Command) := do
  confirm (← prepare notes)

/-- Run preparation once and retain typed paths for save and cancel. Both suffixes are
console-only, and the decision query itself is not issued to the handler. -/
def compare (notes : Notebook) :=
  FreeM.Cursor.forkAtWith (P := Console) decision (form notes).run 0
    (some "save") (some "cancel")

end Notes.Preview
