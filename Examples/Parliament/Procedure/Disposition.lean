/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Procedure.Helpers

/-! # Disposing of questions, suspending business, and restoring context -/

@[expose] public section

namespace Parliament
namespace Procedure

open RuleProgram

variable {D : MotionDomain}

/-- Last session of ordinary availability under quarter and membership constraints. -/
def expiry (s : AssemblyState D) : Nat :=
  if s.calendar.termsContinue && s.calendar.today.withinQuarter s.calendar.nextRegular then
    s.calendar.session + 1
  else s.calendar.session

/-- Move the entire main-motion series into a disposition-specific bundle. -/
def suspend (s : AssemblyState D) (disposition : Disposition) : RuleProgram (Result D) := do
  let main ← need (s.pending.find? (fun q => q.motion.kind == .main)) .noQuestion
  let expires := match disposition with
    | .referred _ => none
    | _ => some (expiry s)
  let questions := match disposition with
    | .referred _ => s.pending.map (fun q => { q with closed := false })
    | _ => s.pending
  let bundle : BusinessBundle D :=
    { id := main.id, questions, disposition, session := s.calendar.session,
      date := s.calendar.today, expiresAfterSession := expires, businessClass := s.businessClass }
  pure ({ s with
    pending := [], floor := none, requests := [],
    suspended := s.suspended ++ [bundle] }, [.suspended main.id disposition])

/-- Strip obsolete postponement questions and exhausted debate orders on restoration. -/
def restoredQuestions (s : AssemblyState D) (b : BusinessBundle D) : List (Question D) :=
  let questions := b.questions.filter fun q =>
    match q.motion with
    | .postpone dueDate => s.calendar.today.ordinal < dueDate.ordinal
    | _ => true
  if b.session < s.calendar.session then questions.map (fun q => { q with closed := false })
  else questions

/-- Restore a suspended series and remove its stored bundle. -/
def restoreBundle (s : AssemblyState D) (b : BusinessBundle D) : AssemblyState D :=
  { s with
    pending := restoredQuestions s b, floor := none, requests := [],
    suspended := s.suspended.filter (fun x => x.id != b.id) }

/-- Apply a primary edit to its main motion and increment that motion's version. -/
def amendPrimary (s : AssemblyState D) (parent : QuestionId) (edit : D.Primary) :
    RuleProgram (AssemblyState D) := do
  let target ← need (s.pending.find? (fun q => q.id == parent)) .wrongTarget
  match target.motion with
  | .main text =>
    let changed ← need (D.apply text edit) .invalidAmendment
    pure { s with
      pending := s.pending.map fun q =>
      if q.id == parent then { q with motion := .main changed, version := q.version + 1 }
      else q }
  | _ => .reject .invalidAmendment

/-- Apply a secondary edit and increment the affected primary amendment's version. -/
def amendSecondary (s : AssemblyState D) (parent : QuestionId) (edit : D.Secondary) :
    RuleProgram (AssemblyState D) := do
  let target ← need (s.pending.find? (fun q => q.id == parent)) .wrongTarget
  match target.motion with
  | .primary mainId primary =>
    let main ← need (s.pending.find? (fun q => q.id == mainId)) .wrongTarget
    match main.motion with
    | .main text =>
      let changed ← need (D.applySecondary text primary edit) .invalidAmendment
      pure { s with
        pending := s.pending.map fun q =>
        if q.id == parent then
          { q with motion := .primary mainId changed, version := q.version + 1 }
        else q }
    | _ => .reject .invalidAmendment
  | _ => .reject .invalidAmendment

/-- Close debate from the immediately pending question through a specified target. -/
def closeThrough (questions : List (Question D)) (target : QuestionId) : List (Question D) :=
  match questions with
  | [] => []
  | q :: qs => { q with closed := true } ::
      if q.id == target then qs else closeThrough qs target

/-- Execute the effect of the immediately pending question after resolving its vote. -/
def dispose (s : AssemblyState D) (adopted : Bool) : RuleProgram (Result D) := do
  let q ← question s
  let base := { s with
    pending := s.pending.tail, phase := .business, poll := none,
    floor := none, requests := [], consentObjector := none,
    history := ⟨q, adopted, s.calendar.today, s.calendar.session⟩ :: s.history }
  match q.motion with
  | .appeal rulingId =>
    let r ← need s.ruling .staleJudgment
    ensure (r.request.id == rulingId) .staleJudgment
    let allowed := if adopted then r.answer.allowed else !r.answer.allowed
    pure (finishRuling base r allowed, [.appealResolved rulingId adopted])
  | motion =>
    if !adopted then pure (base, [])
    else match motion with
    | .main _ => pure (base, [])
    | .primary parent edit => pure (← amendPrimary base parent edit, [])
    | .secondary parent edit => pure (← amendSecondary base parent edit, [])
    | .previousQuestion target =>
      pure ({ base with pending := closeThrough base.pending target }, [])
    | .table => suspend base .tabled
    | .postpone dueDate => suspend base (.postponed dueDate)
    | .refer committee => suspend base (.referred committee)
    | .takeFromTable target =>
      let b ← need (s.suspended.find? (fun b => b.id == target)) .noBusiness
      pure (restoreBundle base b, [.resumed target])
    | .recess endSecond =>
      pure ({ base with phase := .recessed, recessUntil := endSecond }, [.recessed endSecond])
    | .adjourn =>
      pure ({ base with phase := .adjourned }, [.adjourned s.calendar.meeting])
    | .withdrawal target =>
      let remaining := base.pending.dropWhile (fun q => q.id != target)
      ensure (!remaining.isEmpty) .wrongTarget
      pure ({ base with pending := remaining.tail }, [.withdrawn target])
    | .appeal _ => .reject .invalidState

end Procedure
end Parliament
