/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Parliament.App.Machine
public import PolyFunIO.Console

/-! # Pure typed dialogues shared by terminal and in-memory interpreters -/

@[expose] public section

namespace Parliament.App.Dialogue

open Lean PolyFunIO

/-- Gregorian fields are typed independently and checked by the domain engine. -/
def date : Form Date := do
  return ⟨← Form.natural "Year: ", ← Form.natural "Month: ", ← Form.natural "Day: "⟩

/-- Plain motion text uses the word domain; Notes is the example for exact opaque text. -/
def words (prompt : String) : Form (List String) := do
  return (← Form.text prompt).splitOn " " |>.filter (· != "")

/-- The guided editor exposes word positions directly. -/
def wordEdit : Form WordEdit := do
  return ⟨← Form.natural "First word index (zero based): ",
    ← Form.natural "Number of words to remove: ", ← words "Replacement words: "⟩

/-- Target a versioned minutes document, not an old substantive question. -/
def minutesRef : Form MinutesRef := do
  return ⟨← Form.natural "Recorded meeting ID: ", ← Form.natural "Document version: "⟩

/-- Every motion uses typed fields and readable choices. -/
def motion : Form (Motion wordDomain) := do
  let kind ← Form.text "Motion (main, primary, secondary, refer, postpone, previousQuestion, \
    table, takeFromTable, recess, adjourn, withdrawal, appeal, correctMinutes): "
  match kind.trimAscii.toString with
  | "main" =>
    return .main (← words "Motion wording: ")
  | "correctMinutes" =>
    return .correctMinutes (← minutesRef) (← words "Replacement minutes: ")
  | "primary" =>
    return .primary (← Form.natural "Target question ID: ") (← wordEdit)
  | "secondary" =>
    let target ← Form.natural "Target amendment ID: "
    let narrow ← Form.choice "Edit type (wording/narrow): " [("wording", false), ("narrow", true)]
    let edit ← if narrow then
        pure (.narrow (← Form.natural "Offset: ") (← Form.natural "Count: "))
      else pure (.wording (← wordEdit))
    return .secondary target edit
  | "refer" =>
    return .refer (← Form.natural "Committee ID: ")
  | "postpone" =>
    return .postpone (← date)
  | "previousQuestion" =>
    return .previousQuestion (← Form.natural "Last question ID in scope: ")
  | "table" =>
    return .table
  | "takeFromTable" =>
    return .takeFromTable (← Form.natural "Tabled question ID: ")
  | "recess" =>
    return .recess (← Form.natural "Recess deadline, clock seconds: ")
  | "adjourn" =>
    return .adjourn
  | "withdrawal" =>
    return .withdrawal (← Form.natural "Question ID: ")
  | "appeal" =>
    return .appeal (← Form.natural "Ruling request ID: ")
  | _ => throw (.invalid "Unknown motion kind.")

/-- Guided construction covers every public procedural command. -/
def command (name : String) : Form (Command wordDomain) := do
  if name == "unsupported" then return .unsupported (← Form.text "Procedure name: ")
  let actor ← Form.natural "Actor member ID: "
  match name with
  | "openMeeting" =>
    return .openMeeting actor
  | "submitMinutesDraft" =>
    return .submitMinutesDraft actor
      (← Form.natural "Completed meeting ID: ") (← Form.natural "Adjournment revision: ")
      (← words "Submitted minutes text: ")
  | "openMinutesReview" =>
    return .openMinutesReview actor (← minutesRef)
  | "closeMinutesReview" =>
    return .closeMinutesReview actor (← minutesRef)
  | "giveMinutesCorrectionNotice" =>
    return .giveMinutesCorrectionNotice actor
      (← minutesRef) (← words "Notified replacement text: ")
  | "advanceBusiness" =>
    return .advanceBusiness actor
  | "attendance" =>
    return .attendance actor (← Form.natural "Member ID: ")
      (← Form.boolean "Present (yes/no): ")
  | "requestFloor" =>
    return .requestFloor actor
  | "recognize" =>
    return .recognize actor (← Form.natural "Member ID: ")
  | "speak" =>
    return .speak actor
  | "yieldFloor" =>
    return .yieldFloor actor
  | "propose" =>
    return .propose actor (← motion)
  | "second" =>
    return .second actor
  | "stateQuestion" =>
    return .stateQuestion actor
  | "lackSecond" =>
    return .lackSecond actor
  | "withdraw" =>
    return .withdraw actor
  | "pointOfOrder" =>
    return .pointOfOrder actor (← Form.text "Reason: ")
      (← Form.choice "Remedy (none/releaseFloor/discardProposal/cancelPoll/reopenDebate): "
        [("none", .none), ("releaseFloor", .releaseFloor), ("discardProposal", .discardProposal),
         ("cancelPoll", .cancelPoll), ("reopenDebate", .reopenDebate)])
  | "answerJudgment" =>
    return .answerJudgment actor (← Form.natural "Request ID: ")
      (← Form.natural "Issuance revision: ")
      ⟨← Form.boolean "All obligations satisfied (yes/no): ", ← Form.text "Evidence/explanation: "⟩
  | "continueAfterRuling" =>
    return .continueAfterRuling actor
  | "openVote" =>
    return .openVote actor
  | "vote" =>
    return .vote actor (← Form.choice "Choice (yes/no/abstain): "
      [("yes", .yes), ("no", .no), ("abstain", .abstain)])
  | "announce" =>
    return .announce actor
  | "seekConsent" =>
    return .seekConsent actor
  | "object" =>
    return .object actor
  | "closeConsent" =>
    return .closeConsent actor
  | "report" =>
    return .report actor (← Form.natural "Committee ID: ")
      (← Form.natural "Main question ID: ")
  | "resumeDue" =>
    return .resumeDue actor (← Form.natural "Main question ID: ")
  | "advanceTime" =>
    return .advanceTime actor (← date) (← Form.natural "Clock seconds: ")
  | "resumeRecess" =>
    return .resumeRecess actor
  | "nextMeeting" =>
    let today ← date
    let nextRegular ← date
    let meeting ← Form.natural "Next meeting ID: "
    let session ← Form.natural "Session ID: "
    let termsContinue ← Form.boolean "Membership terms continue (yes/no): "
    return .nextMeeting actor { today, nextRegular, meeting, session, termsContinue }
      (← Form.boolean "New session (yes/no): ")
  | _ => throw (.invalid "Unknown command; enter help to list actions.")

/-- All procedural names accepted by the guided terminal. -/
def commandNames : List String := ["openMeeting", "advanceBusiness", "attendance", "requestFloor",
  "recognize", "speak", "yieldFloor", "propose", "second", "stateQuestion", "lackSecond",
  "withdraw",
  "pointOfOrder", "answerJudgment", "continueAfterRuling", "openVote", "vote", "announce",
  "seekConsent", "object", "closeConsent", "report", "resumeDue", "advanceTime", "resumeRecess",
  "nextMeeting", "unsupported", "submitMinutesDraft", "openMinutesReview", "closeMinutesReview",
  "giveMinutesCorrectionNotice"]

/-- Typed human interpretation shared by real and in-memory consoles. -/
def judgmentForm (request : JudgmentRequest wordDomain) :
    Form (Option (JudgmentReply request)) := do
  Form.write s!"Judgment {request.id}: {issueText request.issue}\n{request.reason}\n"
  Form.write ("Obligations: " ++
    String.intercalate ", " (request.obligations.map issueText) ++ "\n")
  if let some q := request.proposal then Form.write ("Proposal: " ++ questionText q ++ "\n")
  for q in request.context do Form.write ("Pending: " ++ questionText q ++ "\n")
  for q in request.suspended do Form.write ("Suspended: " ++ questionText q ++ "\n")
  for decision in request.history.reverse do
    Form.write s!"Prior decision ({if decision.adopted then "adopted" else "not adopted"}): \
      {questionText decision.question}\n"
  let answer ← Form.choice "Ruling (allow, deny, cancel): "
    [("allow", some true), ("deny", some false), ("cancel", none)]
  let some allowed := answer | return none
  return some ⟨⟨allowed, ← Form.text "Explanation: "⟩⟩

end Parliament.App.Dialogue
