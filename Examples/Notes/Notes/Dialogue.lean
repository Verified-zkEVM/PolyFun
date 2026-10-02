/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Notes.Model
public import PolyFunIO.Console

/-! # Typed note commands and navigation

Forms collect an action without changing a notebook. Interpret them with a console handler;
the application machine decides whether an action can prepare a journal update.
-/

@[expose] public section

namespace Notes

open PolyFunIO

/-- UI actions include read-only navigation as well as domain commands. -/
inductive Action where
  | command (command : Command)
  | preview
  | history (revision : Nat)
  | back | forward | live | list | quit
  | invalid (message : String)

/-- A typed free program; the console is supplied later. -/
def commandForm (name : String) : Form Action := do
  match name with
  | "new" => return .command (.create (← Form.text "Text (one line, preserved exactly): "))
  | "edit" => return .command (.edit (← Form.natural "Note ID: ")
      (← Form.natural "Expected version: ") (← Form.text "Replacement text: "))
  | "preview" => return .preview
  | "history" => return .history (← Form.natural "Journal revision: ")
  | "back" => return .back
  | "forward" => return .forward
  | "live" => return .live
  | "list" => return .list
  | "quit" => return .quit
  | _ =>
    if name.startsWith "{" then
      match Lean.Json.parse name >>= Lean.fromJson? (α := Command) with
      | .ok command => return .command command
      | .error error => throw (.invalid error)
    else throw (.invalid
      "Use new, edit, preview, list, history, back, forward, live, quit, or command JSON.")

/-- Reading a whole action is separate from constructing any committed domain state. -/
def readForm : Form Action := do
  commandForm (← Form.text "notes> ").trimAscii.toString

end Notes
