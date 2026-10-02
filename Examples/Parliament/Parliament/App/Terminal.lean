/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Parliament.App.Dialogue

/-! # Terminal interpretation of the parliamentary dialogues -/

@[expose] public section

namespace Parliament.App.Terminal

open Lean PolyFunIO Dialogue

/-- Display text and immediately flush the terminal prompt. -/
def print (text : String) : IO Unit := do
  consoleIOHandler (← IO.getStdin) (← IO.getStdout) (.write text)

/-- EOF is explicit, including when the operator stops midway through a guided action. -/
def line (prompt : String) : IO (Option String) := do
  consoleIOHandler (← IO.getStdin) (← IO.getStdout) (.readLine prompt)

/-- Show actual pending wording and outstanding interpretive information before requesting input. -/
def readAction (state : AssemblyState wordDomain) (viewing : Option Nat) : IO Action := do
  if let some revision := viewing then
    print s!"Read-only history at revision {revision}; enter live to edit.\n"
  else
    print s!"\nMeeting {state.calendar.meeting}; revision {state.revision}; \
      {phaseText state.phase}\n"
    for question in state.pending do print (questionText question ++ "\n")
    if let some proposal := state.proposal then
      print ("Proposed: " ++ questionText proposal ++ "\n")
    if let some request := state.judgment then
      print s!"Judgment {request.id}, issuance revision {request.revision}: {request.reason}\n"
  let some text ← line "Action (help, status, history, back, forward, live, judge, compareRuling, \
    export, quit, \
    command name, or JSON): "
    | return .quit
  let text := text.trimAscii.toString
  match text with
  | "quit" =>
    return .quit
  | "export" =>
    return .export
  | "judge" =>
    return .judge
  | "compareRuling" => return .compareRuling
  | "status" =>
    return .status
  | "history" =>
    match ← (Form.natural "Revision: ").runIO with
    | .error error => return .invalid error.message
    | .ok revision => return .inspect revision
  | "back" => return .back
  | "forward" => return .forward
  | "live" => return .live
  | "help" =>
    print (String.intercalate ", " commandNames ++ "\n")
    print "Enter a name for guided parameters, or paste a full command JSON object.\n"
    return .status
  | _ =>
    if text.startsWith "{" then
      return match decodeJson text with
        | .ok cmd => .command cmd
        | .error error => .invalid error
    else if commandNames.contains text then
      return match ← (command text).runIO with
        | .ok cmd => .command cmd
        | .error error => .invalid error.message
    else return .invalid "unknown action; use help"

/-- A failed or cancelled dialogue never submits a ruling. -/
def judgment (request : JudgmentRequest wordDomain) : IO (Option (JudgmentReply request)) := do
  match ← (judgmentForm request).runIO with
  | .ok reply => return reply
  | .error error => print (error.message ++ "\n"); return none

end Parliament.App.Terminal
