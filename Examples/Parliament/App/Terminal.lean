/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.App.Machine

/-! # Line-oriented terminal input, with a guided path for every modeled command -/

@[expose] public section

namespace Parliament.App.Terminal

open Lean

/-- Display text and immediately flush the terminal prompt. -/
def print (text : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr text
  stdout.flush

/-- EOF is explicit, including when the operator stops midway through a guided action. -/
def line (prompt : String) : IO (Option String) := do
  print prompt
  let text ← (← IO.getStdin).getLine
  if text.isEmpty then return none
  return some (text.trimAscii.toString)

/-- Required input in the guided parser; cancellation never creates a partial command. -/
def required (prompt : String) : ExceptT String IO String := do
  match ← line prompt with
  | none => throw "end of input during action; no command submitted"
  | some text => pure text

/-- Parse one typed JSON value used for a command parameter. -/
def value {α : Type} [FromJson α] (prompt : String) : ExceptT String IO α := do
  let text ← required prompt
  match decodeJson text with
  | .ok result => pure result
  | .error error => throw error

/-- Prompt for a Gregorian date in an unambiguous machine-readable form. -/
def date : ExceptT String IO Date :=
  value "Date as JSON {\"year\":2026,\"month\":1,\"day\":15}: "

/-- Guided motion construction retains structured word edits and question identities. -/
def motion : ExceptT String IO (Motion wordDomain) := do
  let kind ← required "Motion (main, primary, secondary, refer, postpone, previousQuestion, \
    table, takeFromTable, recess, adjourn, withdrawal, appeal): "
  match kind with
  | "main" => pure (.main (← value (α := List String) "Wording as a JSON array of words: "))
  | "primary" => pure (.primary (← value "Target question ID: ")
      (← value (α := WordEdit)
        "Edit as JSON {\"start\":0,\"count\":1,\"words\":[\"replacement\"]}: "))
  | "secondary" => pure (.secondary (← value "Target amendment ID: ")
      (← value (α := WordSecondary)
        "Secondary edit as JSON (wording/edit or narrow/offset,count): "))
  | "refer" => pure (.refer (← value "Committee ID: "))
  | "postpone" => pure (.postpone (← date))
  | "previousQuestion" => pure (.previousQuestion (← value "Last question ID in scope: "))
  | "table" => pure .table
  | "takeFromTable" => pure (.takeFromTable (← value "Tabled main question ID: "))
  | "recess" => pure (.recess (← value "Recess deadline, clock seconds: "))
  | "adjourn" => pure .adjourn
  | "withdrawal" => pure (.withdrawal (← value "Question ID: "))
  | "appeal" => pure (.appeal (← value "Ruling request ID: "))
  | _ => throw "unknown motion kind"

/-- Guided construction covers every public procedural command. -/
def command (name : String) : ExceptT String IO (Command wordDomain) := do
  if name == "unsupported" then return .unsupported (← required "Procedure name: ")
  let actor ← value "Actor member ID: "
  match name with
  | "openMeeting" => pure (.openMeeting actor)
  | "advanceBusiness" => pure (.advanceBusiness actor)
  | "attendance" => pure (.attendance actor (← value "Member ID: ")
      (← value "Present (true/false): "))
  | "requestFloor" => pure (.requestFloor actor)
  | "recognize" => pure (.recognize actor (← value "Member ID: "))
  | "speak" => pure (.speak actor)
  | "yieldFloor" => pure (.yieldFloor actor)
  | "propose" => pure (.propose actor (← motion))
  | "second" => pure (.second actor)
  | "stateQuestion" => pure (.stateQuestion actor)
  | "lackSecond" => pure (.lackSecond actor)
  | "withdraw" => pure (.withdraw actor)
  | "pointOfOrder" => pure (.pointOfOrder actor (← required "Reason: ")
      (← value "Remedy as JSON string (none, releaseFloor, discardProposal, \
        cancelPoll, reopenDebate): "))
  | "answerJudgment" => pure (.answerJudgment actor (← value "Request ID: ")
      (← value "Issuance revision: ")
      ⟨← value "Allowed (true/false): ", ← required "Explanation: "⟩)
  | "continueAfterRuling" => pure (.continueAfterRuling actor)
  | "openVote" => pure (.openVote actor)
  | "vote" => pure (.vote actor (← value "Choice as JSON string (yes/no/abstain): "))
  | "announce" => pure (.announce actor)
  | "seekConsent" => pure (.seekConsent actor)
  | "object" => pure (.object actor)
  | "closeConsent" => pure (.closeConsent actor)
  | "report" => pure (.report actor (← value "Committee ID: ") (← value "Main question ID: "))
  | "resumeDue" => pure (.resumeDue actor (← value "Main question ID: "))
  | "advanceTime" => pure (.advanceTime actor (← date) (← value "Clock seconds: "))
  | "resumeRecess" => pure (.resumeRecess actor)
  | "nextMeeting" => pure (.nextMeeting actor
      (← value "Calendar JSON (today, nextRegular, meeting, session, termsContinue): ")
      (← value "New session (true/false): "))
  | _ => throw "unknown command; enter help to list actions"

/-- All procedural names accepted by the guided terminal. -/
def commandNames : List String := ["openMeeting", "advanceBusiness", "attendance", "requestFloor",
  "recognize", "speak", "yieldFloor", "propose", "second", "stateQuestion", "lackSecond",
  "withdraw",
  "pointOfOrder", "answerJudgment", "continueAfterRuling", "openVote", "vote", "announce",
  "seekConsent", "object", "closeConsent", "report", "resumeDue", "advanceTime", "resumeRecess",
  "nextMeeting", "unsupported"]

/-- Show actual pending wording and outstanding interpretive information before requesting input. -/
def readAction (state : AssemblyState wordDomain) : IO Action := do
  print s!"\nMeeting {state.calendar.meeting}; revision {state.revision}; {phaseText state.phase}\n"
  for question in state.pending do print (questionText question ++ "\n")
  if let some proposal := state.proposal then print ("Proposed: " ++ questionText proposal ++ "\n")
  if let some request := state.judgment then
    print s!"Judgment {request.id}, issuance revision {request.revision}: {request.reason}\n"
  let some text ← line "Action (help, status, judge, export, quit, command name, or JSON): "
    | return .quit
  match text with
  | "quit" => return .quit
  | "export" => return .export
  | "judge" => return .judge
  | "status" => return .status
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
      return match ← (command text).run with
        | .ok cmd => .command cmd
        | .error error => .invalid error
    else return .invalid "unknown action; use help"

/-- Human interpretation is an IO response to an exact request, with explicit cancellation. -/
def judgment (request : JudgmentRequest wordDomain) : IO (Option (JudgmentReply request)) := do
  print s!"Judgment {request.id}: {issueText request.issue}\n{request.reason}\n"
  if let some q := request.proposal then print ("Proposal: " ++ questionText q ++ "\n")
  for q in request.context do print ("Pending: " ++ questionText q ++ "\n")
  for q in request.suspended do print ("Suspended: " ++ questionText q ++ "\n")
  for decision in request.history.reverse do
    print s!"Prior decision ({if decision.adopted then "adopted" else "not adopted"}): \
      {questionText decision.question}\n"
  let some text ← line "Ruling (allow, deny, cancel): " | return none
  if text == "cancel" then return none
  if text != "allow" && text != "deny" then
    print "Invalid ruling; cancelled without a reply.\n"
    return none
  let some reason ← line "Explanation: " | return none
  return some ⟨⟨text == "allow", reason⟩⟩

end Parliament.App.Terminal
