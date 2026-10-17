/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Parliament.Minutes.Render
public import PolyFun.PFunctor.Free.Cursor.Occurrence

/-! # Hypothetical rulings without persistence

Both alternatives use the live command checker, including closing the appeal opportunity under
the explicit assumption that no appeal is taken. This predicts procedural successors, not the
substantive correctness of a ruling. The program has only a judgment capability, never storage.
-/

@[expose] public section

namespace Parliament.App.Preview

open PFunctor

/-- Check an answer and the subsequent no-appeal continuation on a hypothetical journal. -/
def outcome (config : Configuration) (journal : Journal wordDomain config.rules)
    {request : JudgmentRequest wordDomain} (reply : JudgmentReply request) : String :=
  match checkInput config.rules journal.state (reply.command journal.state.chair) with
  | .error error => "Ruling rejected: " ++ error.message
  | .ok input =>
    let candidate := journal.accept input
    match checkInput config.rules candidate.state (.continueAfterRuling candidate.state.chair) with
    | .error error => "No-appeal continuation rejected: " ++ error.message
    | .ok next => renderMarkdown config.metadata (candidate.accept next)

/-- A single typed ruling query followed by pure command checking. -/
def program (config : Configuration) (journal : Journal wordDomain config.rules)
    (request : JudgmentRequest wordDomain) : FreeM (JudgmentSig wordDomain) String :=
  FreeM.liftBind request fun reply => pure (outcome config journal reply)

/-- Compare explicit allow/deny answers without requesting or recording a real ruling. -/
def compare (config : Configuration) (journal : Journal wordDomain config.rules) : String :=
  match journal.state.judgment with
  | none => "No judgment is outstanding."
  | some request =>
    let computation := program config journal request
    let branches := FreeM.Cursor.forkAtWith (P := JudgmentSig wordDomain) request computation 0
      ⟨⟨true, "Hypothetical allow"⟩⟩ ⟨⟨false, "Hypothetical deny"⟩⟩
    -- No query remains: the selected query is supplied explicitly and both suffixes are pure.
    let view := branches.liftM (m := Except String)
      (fun _ => .error "Comparison unexpectedly requested a ruling.")
    match view with
    | .error error => error
    | .ok none => "No matching judgment occurrence."
    | .ok (some view) =>
      "HYPOTHETICAL ONLY: current live state; assumes no appeal. Nothing saved or published.\n" ++
      "ALLOW\n" ++ FreeM.output computation view.firstPath ++
      "\nDENY\n" ++ FreeM.output computation view.secondPath ++
      "\nUse judge to enter an actual ruling; neither alternative is a recommendation."

end Parliament.App.Preview
