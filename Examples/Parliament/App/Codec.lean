/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Minutes.Document
public import Lean

/-! # Versioned wire data; only commands and configuration are trusted after validation -/

@[expose] public section

namespace Parliament

open Lean

deriving instance ToJson, FromJson for Date, Vote, Threshold, Denominator, Tally,
  Rules, Member, Calendar, WordEdit, WordSecondary, MotionKind, IssueKind, Remedy,
  Ruling, Disposition, BusinessClass, DecisionMethod

/-- Monomorphic motion encoding for the first executable's word domain. -/
inductive WireMotion where
  | main (text : List String)
  | primary (target : QuestionId) (edit : WordEdit)
  | secondary (target : QuestionId) (edit : WordSecondary)
  | refer (committee : CommitteeId)
  | postpone (dueDate : Date)
  | previousQuestion (through : QuestionId)
  | table
  | takeFromTable (target : QuestionId)
  | recess (untilSecond : Nat)
  | adjourn
  | withdrawal (target : QuestionId)
  | appeal (ruling : Nat)
  deriving ToJson, FromJson

/-- Erase the wire wrapper without changing any motion parameters. -/
def WireMotion.toMotion : WireMotion → Motion wordDomain
  | .main text => .main text
  | .primary target edit => .primary target edit
  | .secondary target edit => .secondary target edit
  | .refer committee => .refer committee
  | .postpone dueDate => .postpone dueDate
  | .previousQuestion through => .previousQuestion through
  | .table => .table
  | .takeFromTable target => .takeFromTable target
  | .recess untilSecond => .recess untilSecond
  | .adjourn => .adjourn
  | .withdrawal target => .withdrawal target
  | .appeal ruling => .appeal ruling

/-- Select the concrete word-domain wire representation. -/
def WireMotion.ofMotion : Motion wordDomain → WireMotion
  | .main text => .main text
  | .primary target edit => .primary target edit
  | .secondary target edit => .secondary target edit
  | .refer committee => .refer committee
  | .postpone dueDate => .postpone dueDate
  | .previousQuestion through => .previousQuestion through
  | .table => .table
  | .takeFromTable target => .takeFromTable target
  | .recess untilSecond => .recess untilSecond
  | .adjourn => .adjourn
  | .withdrawal target => .withdrawal target
  | .appeal ruling => .appeal ruling

theorem WireMotion.roundtrip (motion : Motion wordDomain) :
    (ofMotion motion).toMotion = motion := by cases motion <;> rfl

instance : ToJson (Motion wordDomain) := ⟨fun m => toJson (WireMotion.ofMotion m)⟩
instance : FromJson (Motion wordDomain) := ⟨fun j => WireMotion.toMotion <$> fromJson? j⟩

/-- Concrete command encoding; every current public command has a wire constructor. -/
inductive WireCommand where
  | openMeeting (actor : MemberId)
  | advanceBusiness (actor : MemberId)
  | attendance (actor member : MemberId) (present : Bool)
  | requestFloor (actor : MemberId)
  | recognize (actor member : MemberId)
  | speak (actor : MemberId)
  | yieldFloor (actor : MemberId)
  | propose (actor : MemberId) (motion : Motion wordDomain)
  | second (actor : MemberId)
  | stateQuestion (actor : MemberId)
  | lackSecond (actor : MemberId)
  | withdraw (actor : MemberId)
  | pointOfOrder (actor : MemberId) (reason : String) (remedy : Remedy)
  | answerJudgment (actor request revision : Nat) (answer : Ruling)
  | continueAfterRuling (actor : MemberId)
  | openVote (actor : MemberId)
  | vote (actor : MemberId) (choice : Vote)
  | announce (actor : MemberId)
  | seekConsent (actor : MemberId)
  | object (actor : MemberId)
  | closeConsent (actor : MemberId)
  | report (actor : MemberId) (committee : CommitteeId) (question : QuestionId)
  | resumeDue (actor : MemberId) (question : QuestionId)
  | advanceTime (actor : MemberId) (date : Date) (second : Nat)
  | resumeRecess (actor : MemberId)
  | nextMeeting (actor : MemberId) (calendar : Calendar) (newSession : Bool)
  | unsupported (name : String)
  deriving ToJson, FromJson

/-- Interpret a parsed wire command without adding implicit procedural actions. -/
def WireCommand.toCommand : WireCommand → Command wordDomain
  | .openMeeting a => .openMeeting a
  | .advanceBusiness a => .advanceBusiness a
  | .attendance a m p => .attendance a m p
  | .requestFloor a => .requestFloor a
  | .recognize a m => .recognize a m
  | .speak a => .speak a
  | .yieldFloor a => .yieldFloor a
  | .propose a m => .propose a m
  | .second a => .second a
  | .stateQuestion a => .stateQuestion a
  | .lackSecond a => .lackSecond a
  | .withdraw a => .withdraw a
  | .pointOfOrder a r m => .pointOfOrder a r m
  | .answerJudgment a r v answer => .answerJudgment a r v answer
  | .continueAfterRuling a => .continueAfterRuling a
  | .openVote a => .openVote a
  | .vote a v => .vote a v
  | .announce a => .announce a
  | .seekConsent a => .seekConsent a
  | .object a => .object a
  | .closeConsent a => .closeConsent a
  | .report a c q => .report a c q
  | .resumeDue a q => .resumeDue a q
  | .advanceTime a d s => .advanceTime a d s
  | .resumeRecess a => .resumeRecess a
  | .nextMeeting a c n => .nextMeeting a c n
  | .unsupported name => .unsupported name

/-- Encode a raw command with all identities and parameters preserved. -/
def WireCommand.ofCommand : Command wordDomain → WireCommand
  | .openMeeting a => .openMeeting a
  | .advanceBusiness a => .advanceBusiness a
  | .attendance a m p => .attendance a m p
  | .requestFloor a => .requestFloor a
  | .recognize a m => .recognize a m
  | .speak a => .speak a
  | .yieldFloor a => .yieldFloor a
  | .propose a m => .propose a m
  | .second a => .second a
  | .stateQuestion a => .stateQuestion a
  | .lackSecond a => .lackSecond a
  | .withdraw a => .withdraw a
  | .pointOfOrder a r m => .pointOfOrder a r m
  | .answerJudgment a r v answer => .answerJudgment a r v answer
  | .continueAfterRuling a => .continueAfterRuling a
  | .openVote a => .openVote a
  | .vote a v => .vote a v
  | .announce a => .announce a
  | .seekConsent a => .seekConsent a
  | .object a => .object a
  | .closeConsent a => .closeConsent a
  | .report a c q => .report a c q
  | .resumeDue a q => .resumeDue a q
  | .advanceTime a d s => .advanceTime a d s
  | .resumeRecess a => .resumeRecess a
  | .nextMeeting a c n => .nextMeeting a c n
  | .unsupported name => .unsupported name

theorem WireCommand.roundtrip (command : Command wordDomain) :
    (ofCommand command).toCommand = command := by cases command <;> rfl

instance : ToJson (Command wordDomain) := ⟨fun c => toJson (WireCommand.ofCommand c)⟩
instance : FromJson (Command wordDomain) := ⟨fun j => WireCommand.toCommand <$> fromJson? j⟩

instance : ToJson (Question wordDomain) := ⟨fun q => Json.mkObj [
  ("id", toJson q.id), ("version", toJson q.version), ("maker", toJson q.maker),
  ("motion", toJson q.motion)]⟩

instance : ToJson (MinuteAction wordDomain) := ⟨fun action => match action with
  | .opened => Json.mkObj [("kind", "opened")]
  | .decided q adopted method => Json.mkObj [("kind", "decided"),
      ("question", toJson q), ("adopted", toJson adopted), ("method", toJson method)]
  | .notSeconded q => Json.mkObj [("kind", "notSeconded"), ("question", toJson q)]
  | .withdrawn q => Json.mkObj [("kind", "withdrawn"), ("question", toJson q)]
  | .ruled id issue answer => Json.mkObj [("kind", "ruled"), ("request", toJson id),
      ("issue", toJson issue), ("answer", toJson answer)]
  | .appealResolved id sustained => Json.mkObj [("kind", "appealResolved"),
      ("request", toJson id), ("sustained", toJson sustained)]
  | .suspended q disposition => Json.mkObj [("kind", "suspended"),
      ("question", toJson q), ("disposition", toJson disposition)]
  | .resumed q => Json.mkObj [("kind", "resumed"), ("question", toJson q)]
  | .expired q => Json.mkObj [("kind", "expired"), ("question", toJson q)]
  | .recessed untilSecond => Json.mkObj [("kind", "recessed"), ("untilSecond", toJson untilSecond)]
  | .adjourned => Json.mkObj [("kind", "adjourned")]⟩

instance : ToJson (MinuteEntry wordDomain) := ⟨fun e => Json.mkObj [
  ("meeting", toJson e.meeting), ("session", toJson e.session), ("date", toJson e.date),
  ("second", toJson e.second), ("revision", toJson e.revision), ("eventIndex", toJson e.eventIndex),
  ("action", toJson e.action)]⟩

namespace App

/-- Human-supplied header data, separate from procedural facts. -/
structure Metadata where
  /-- Name of the assembly. -/
  organization : String
  /-- Display title for the meeting series. -/
  title : String
  /-- Optional location; absence is not filled with invented text. -/
  location : Option String := none
  /-- Optional clerk's name. -/
  clerk : Option String := none
  deriving DecidableEq, ToJson, FromJson

/-- Everything required to initialize and reproduce a word-domain assembly. -/
structure Configuration where
  /-- Frozen parliamentary rules. -/
  rules : Rules
  /-- Fixed membership roster. -/
  members : List Member
  /-- Presiding identity. -/
  chair : MemberId
  /-- Initial session calendar. -/
  calendar : Calendar
  /-- Registered committees. -/
  committees : List CommitteeId := []
  /-- Supplied document headers. -/
  metadata : Metadata
  deriving DecidableEq, ToJson, FromJson

/-- Validated empty journal for the supplied configuration. -/
def Configuration.start (config : Configuration) :
    Except String (Journal wordDomain config.rules) :=
  match initializeAssembly wordDomain config.rules config.members config.chair
      config.calendar config.committees with
  | .error error => .error s!"invalid configuration: {repr error}"
  | .ok initial =>
    match Journal.start config.rules initial with
    | .error error => .error s!"invalid initial state: {repr error}"
    | .ok journal => .ok journal

/-- The only persisted source of procedural truth; no saved state or event claims are loaded. -/
structure WireJournal where
  /-- Schema and procedure-semantics revision. -/
  version : Nat := 1
  /-- Initialization and supplied metadata. -/
  config : Configuration
  /-- Accepted commands, in execution order. -/
  commands : List (Command wordDomain)
  deriving DecidableEq, ToJson, FromJson

/-- Decode JSON with a stable, user-visible parse error. -/
def decodeJson {α : Type} [FromJson α] (text : String) : Except String α := do
  let json ← Json.parse text
  fromJson? json

/-- Canonical deterministic JSON, with a final newline. -/
def encodeJson {α : Type} [ToJson α] (value : α) : String := (toJson value).compress ++ "\n"

/-- Reconstruct all certificates from versioned input, stopping at the exact illegal command. -/
def WireJournal.restore (wire : WireJournal) :
    Except String (Journal wordDomain wire.config.rules) := do
  if wire.version != 1 then throw s!"unsupported journal version {wire.version}"
  let journal ← wire.config.start
  match journal.replay wire.commands with
  | .error (index, error) => throw s!"command {index}: {repr error}"
  | .ok result => pure result

/-- Capture a committed journal for persistence; proofs and computed states stay out of the wire. -/
def snapshot (config : Configuration) (journal : Journal wordDomain config.rules) : WireJournal :=
  ⟨1, config, journal.history.commands⟩

end App
end Parliament
