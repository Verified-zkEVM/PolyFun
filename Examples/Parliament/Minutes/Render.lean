/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.App.Codec
public import Examples.Parliament.Minutes.Correspondence

/-! # Typed presentation and canonical draft artifacts -/

@[expose] public section

namespace Parliament.App

open Lean

/-- A presentation block retains its typed procedural payload until final rendering. -/
inductive Block where
  | action (entry : MinuteEntry wordDomain)
  | unresolved (question : Question wordDomain)

/-- Lower the action sequence, followed by a separately labeled unresolved-business section. -/
def lower {rules : Rules} (journal : Journal wordDomain rules) : List Block :=
  journal.history.entries.map .action ++ (Parliament.unresolved journal).map .unresolved

/-- Recover only recorded action fields from typed presentation blocks. -/
def blockActions (blocks : List Block) : List (MinuteEntry wordDomain) :=
  blocks.filterMap fun block => match block with
    | .action entry => some entry
    | .unresolved _ => none

theorem lower_preserves_actions {rules : Rules} (journal : Journal wordDomain rules) :
    blockActions (lower journal) = journal.history.entries := by
  simp [blockActions, lower, List.filterMap_map]

/-- Escape supplied text as literal Markdown, including control characters and HTML delimiters. -/
def escapeMarkdown (text : String) : String :=
  String.ofList (text.toList.flatMap fun char =>
    if char == '\n' then ['\\', 'n']
    else if char == '\r' then ['\\', 'r']
    else if char == '\t' then ['\\', 't']
    else if char.toNat < 32 || char.toNat == 127 then ['?']
    else if "\\`*_{}[]()<>&#!|~+-.$".contains char then ['\\', char]
    else [char])

/-- Render dates without consulting the ambient clock. -/
def dateText (date : Date) : String := s!"{date.year}-{date.month}-{date.day}"

/-- Describe a bounded edit using its word coordinates and replacement wording. -/
def editText (edit : WordEdit) : String :=
  s!"replace {edit.count} words starting at {edit.start} with " ++
    (if edit.words.isEmpty then "no words" else String.intercalate " " edit.words)

/-- Describe procedural motions without exposing wire-format constructors in a document. -/
def motionText : Motion wordDomain → String
  | .main words => String.intercalate " " words
  | .primary target edit => s!"Amend question {target}: {editText edit}"
  | .secondary target (.wording edit) =>
    s!"Amend the replacement wording in amendment {target}: {editText edit}"
  | .secondary target (.narrow offset count) =>
    s!"Narrow the deletion in amendment {target}: offset {offset}, {count} words"
  | .refer committee => s!"Refer to committee {committee}"
  | .postpone date => s!"Postpone to {dateText date}"
  | .previousQuestion through => s!"Close debate through question {through}"
  | .table => "Lay the pending business on the table"
  | .takeFromTable target => s!"Take question {target} from the table"
  | .recess untilSecond => s!"Recess until clock second {untilSecond}"
  | .adjourn => "Adjourn"
  | .withdrawal target => s!"Request permission to withdraw question {target}"
  | .appeal request => s!"Appeal ruling {request}"

/-- Exact modeled main wording, or a complete readable description of a procedural motion. -/
def questionText (question : Question wordDomain) : String :=
  s!"Question {question.id}, version {question.version}, mover {question.maker}: " ++
    motionText question.motion

/-- Plain-language names for the interpretation categories presented to the chair. -/
def issueText : IssueKind → String
  | .admissibility => "admissibility"
  | .germaneness => "germaneness"
  | .urgency => "urgency"
  | .sameQuestion => "same question"
  | .dilatory => "dilatory use"
  | .pointOfOrder => "point of order"

/-- Plain-language meeting phases used by the terminal. -/
def phaseText : Phase → String
  | .dormant => "not opened"
  | .business => "business"
  | .voting => "counted voting"
  | .consent => "consent opportunity"
  | .recessed => "in recess"
  | .adjourned => "adjourned"

/-- Describe why a whole question series was suspended. -/
def dispositionText : Disposition → String
  | .tabled => "laid on the table"
  | .postponed date => s!"postponed to {dateText date}"
  | .referred committee => s!"referred to committee {committee}"

/-- A deterministic textual description of each action; consent and missing seconds stay
distinct. -/
def actionText : MinuteAction wordDomain → String
  | .opened => "Meeting opened."
  | .decided q adopted method =>
    let result := if q.motion.kind == .appeal then
        if adopted then "Ruling sustained" else "Ruling reversed"
      else if adopted then "Adopted" else "Not adopted"
    let basis := match method with
      | .consent => "by unanimous consent"
      | .counted tally => s!"by counted vote ({tally.yes} yes, {tally.no} no)"
    s!"{result} {basis}. {questionText q}"
  | .notSeconded q => s!"Not considered for lack of a second. {questionText q}"
  | .withdrawn q => s!"Withdrawn with assembly permission. {questionText q}"
  | .ruled id issue answer =>
    s!"Ruling {id} ({issueText issue}): " ++
      s!"{if answer.allowed then "allowed" else "denied"}. {answer.reason}"
  | .appealResolved id sustained =>
    s!"Appeal of ruling {id}: {if sustained then "sustained" else "reversed"}."
  | .suspended q disposition =>
    s!"Business suspended ({dispositionText disposition}). {questionText q}"
  | .resumed q => s!"Business resumed. {questionText q}"
  | .expired q => s!"Suspended business expired. {questionText q}"
  | .recessed untilSecond => s!"Recess until clock second {untilSecond}."
  | .adjourned => "Meeting adjourned."

/-- Render a typed block; user-supplied text cannot create Markdown structure. -/
def renderBlock : Block → String
  | .action entry =>
    s!"- Meeting {entry.meeting}, session {entry.session}, {dateText entry.date}, " ++
      s!"second {entry.second} [revision {entry.revision}, event {entry.eventIndex}]: " ++
      escapeMarkdown (actionText entry.action) ++ "\n"
  | .unresolved question => "- Unresolved: " ++ escapeMarkdown (questionText question) ++ "\n"

/-- Render a draft with deterministic metadata and an explicit current-meeting status. -/
def renderMarkdown {rules : Rules} (metadata : Metadata) (journal : Journal wordDomain rules) :
    String :=
  "# Draft—unapproved\n\n" ++ escapeMarkdown metadata.organization ++ "\n\n" ++
    escapeMarkdown metadata.title ++ "\n\n" ++
    (metadata.location.map (fun value => "Location: " ++ escapeMarkdown value ++ "\n\n")).getD "" ++
    (metadata.clerk.map (fun value => "Clerk: " ++ escapeMarkdown value ++ "\n\n")).getD "" ++
    s!"Source revision: {journal.state.revision}\n\n" ++
    s!"Current meeting {journal.state.calendar.meeting}: " ++
    (if journal.state.phase == .adjourned then "adjourned" else "unfinished") ++ "\n\n" ++
    "## Recorded actions\n\n" ++
    String.join (journal.history.entries.map (fun entry => renderBlock (.action entry))) ++
    "\n## Unresolved business\n\n" ++
    String.join ((Parliament.unresolved journal).map (fun q => renderBlock (.unresolved q)))

/-- Canonical structured minutes, including typed actions and separately unresolved wording. -/
def renderJson {rules : Rules} (metadata : Metadata) (journal : Journal wordDomain rules) :
    String :=
  encodeJson (Json.mkObj [
    ("version", toJson (1 : Nat)), ("status", "draft-unapproved"), ("metadata", toJson metadata),
    ("sourceRevision", toJson journal.state.revision),
    ("currentMeeting", toJson journal.state.calendar.meeting),
    ("adjourned", toJson (journal.state.phase == .adjourned)),
    ("entries", toJson (blockActions (lower journal))),
    ("unresolved", toJson (Parliament.unresolved journal))])

-- The certificate uniquely fixes both fields, so constructor injectivity adds no useful rule.
set_option genInjectivity false in
/-- Both exact payloads, indexed by the certified history from which they were derived. -/
structure Artifacts {rules : Rules} (metadata : Metadata) (journal : Journal wordDomain rules) where
  /-- Human-readable draft payload. -/
  markdown : String
  /-- Structured draft payload. -/
  json : String
  /-- Both payloads are exactly the canonical renderings of the same certified journal. -/
  faithful : markdown = renderMarkdown metadata journal ∧ json = renderJson metadata journal

/-- Construct the only payloads the application may request for minutes publication. -/
def artifacts {rules : Rules} (metadata : Metadata) (journal : Journal wordDomain rules) :
    Artifacts metadata journal := ⟨_, _, rfl, rfl⟩

/-- Revalidate observed file contents against the reconstructed journal, yielding exact
equalities. -/
def verifyArtifacts {rules : Rules} (metadata : Metadata) (journal : Journal wordDomain rules)
    (markdown json : String) : Except String (Artifacts metadata journal) :=
  if h : markdown = renderMarkdown metadata journal ∧ json = renderJson metadata journal then
    .ok ⟨markdown, json, h⟩
  else .error "export does not match the canonical draft for this journal revision"

theorem artifacts_fields {rules : Rules} (metadata : Metadata) (journal : Journal wordDomain rules)
    (output : Artifacts metadata journal) :
    output.markdown = (artifacts metadata journal).markdown ∧
      output.json = (artifacts metadata journal).json := output.faithful

/-- Replaying identical source commands gives byte-for-byte identical requested output strings. -/
theorem artifacts_reconstruction {rules : Rules} (metadata : Metadata)
    (first second : Journal wordDomain rules) (initial : first.initial = second.initial)
    (commands : first.history.commands = second.history.commands) :
    renderMarkdown metadata first = renderMarkdown metadata second ∧
      renderJson metadata first = renderJson metadata second := by
  rcases first with ⟨initial₁, valid₁, state₁, history₁⟩
  rcases second with ⟨initial₂, valid₂, state₂, history₂⟩
  dsimp at initial commands ⊢
  subst initial₂
  have states : state₁ = state₂ :=
    (replay_deterministic history₁.replays (by rw [commands]; exact history₂.replays)).1
  subst state₂
  have entries := History.entries_determined history₁ history₂ commands
  constructor
  · simp only [renderMarkdown, entries, unresolved]
  · simp only [renderJson, lower_preserves_actions, entries, unresolved]

end Parliament.App
