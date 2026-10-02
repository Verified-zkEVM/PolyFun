/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Displayed.Cursor
public import PolyFun.PFunctor.Handler.Stateful

/-! # A reviewable edit plan with source metadata

Approval and application are separate effects. The same finite program can be inspected with
a typed cursor, run against a scripted reviewer, or presented with different explanations.
Displayed decorations attach source information without inventing another program AST.
An over-decoration certifies that every displayed source location is a positive line number;
it does not certify that a filesystem still contains the proposed original text.
-/

@[expose] public section

namespace PolyFunExamples.ReviewableWorkflows

open PFunctor FreeM FreeM.Displayed

/-- One opaque text replacement; storage/version checks remain the application's responsibility. -/
structure Edit where
  /-- Text shown before confirmation. -/
  before : String
  /-- Text submitted only after approval. -/
  after : String
  deriving DecidableEq, Repr

/-- Review requests return decisions; applying an edit returns an acknowledgement. -/
inductive Operation where
  | review (edit : Edit)
  | apply (edit : Edit)

/-- The dependent response type prevents treating an acknowledgement as an approval. -/
abbrev Effects : PFunctor where
  A := Operation
  B
    | .review _ => Bool
    | .apply _ => Unit

/-- Approve or skip a proposal before continuing with the remaining plan. -/
def plan : List Edit → FreeM Effects Unit
  | [] => .pure ()
  | edit :: rest => .liftBind (.review edit) fun approved ↦
      if approved then .liftBind (.apply edit) fun _ ↦ plan rest else plan rest

/-- Source location and explanatory text are a presentation layer, not effect operations. -/
structure Source where
  /-- Human-readable source name. -/
  file : String
  /-- One-based source line, checked by the over-decoration. -/
  line : Nat
  /-- Explanation presented beside the proposal. -/
  explanation : String
  deriving DecidableEq, Repr

/-- Attach metadata using the existing empty decoration and its nodewise map. -/
def annotate (source : Source) (edits : List Edit) :
    Decoration (fun _ ↦ Source) (plan edits) :=
  Decoration.map (fun _ (_ : PUnit.{1}) ↦ source) _ (Decoration.empty _)

/-- Source validity depends on the metadata value stored at that exact node. -/
abbrev ValidSource (_ : Operation) (source : Source) := PLift (0 < source.line)

/-- A concrete two-edit review session. -/
def edits : List Edit := [⟨"Draft", "Reviewed"⟩, ⟨"TODO", "Done"⟩]

/-- The displayed location used in the session. -/
def source : Source := ⟨"draft.txt", 1, "Review each replacement before applying it."⟩

/-- A dependent certificate attached to each node through the extended-context bridge. -/
def checkedMetadata : Decoration (Decoration.Context.extend (fun _ ↦ Source) ValidSource)
    (plan edits) :=
  Decoration.map (fun _ (_ : PUnit.{1}) ↦ ⟨source, ⟨by decide⟩⟩) _ (Decoration.empty _)

/-- Forgetting only the certificate recovers the explanatory metadata. -/
def metadata := (Decoration.toOver (plan edits) checkedMetadata).1

/-- Recover the genuinely dependent over-layer without rebuilding the program. -/
def evidence : Decoration.Over (fun _ ↦ Source) ValidSource (plan edits) metadata :=
  (Decoration.toOver _ checkedMetadata).2

/-- After rejecting the first edit, the cursor points at the second review, not an application. -/
def afterRejection : Cursor (plan edits) := Cursor.down false (Cursor.root (plan edits.tail))

/-- The remaining explanation is retained when navigating to a residual program. -/
example : (Decoration.restrict afterRejection metadata).1 = source := rfl

/-- Source validity travels with the selected explanation. -/
def remainingEvidence := Decoration.Over.restrict afterRejection metadata evidence

/-- Changing explanations commutes with navigation; neither operation changes the program. -/
theorem presentation_natural (reword : Source → Source) :
    Decoration.restrict afterRejection
        (Decoration.map (fun _ ↦ reword) (plan edits) metadata) =
      Decoration.map (fun _ ↦ reword) afterRejection.residual
        (Decoration.restrict afterRejection metadata) :=
  Decoration.restrict_map _ _ _

/-- Testable interpretation records exactly the edits acknowledged by the application effect. -/
def reviewer (approve : Edit → Bool) : Handler.Stateful Id (List Edit) Effects
  | .review edit, applied => (approve edit, applied)
  | .apply edit, applied => ((), applied ++ [edit])

/-- Rejecting every proposal performs no application effect, for an arbitrary batch. -/
theorem reject_preserves (batch applied : List Edit) :
    (reviewer (fun _ ↦ false)).run (plan batch) applied = ((), applied) := by
  induction batch with
  | nil => rfl
  | cons edit rest ih =>
    rw [plan, Handler.Stateful.run_liftBind]
    exact ih

/-- The script rejects the first edit and approves only the second. -/
example : (reviewer (fun edit ↦ edit.before == "TODO")).run (plan edits) [] =
    ((), [⟨"TODO", "Done"⟩]) := rfl

end PolyFunExamples.ReviewableWorkflows
