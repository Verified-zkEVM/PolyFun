/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Parliament.Content

/-! # Submitted minutes text, approval, and append-only corrections

These are document data, not the derived action register. Attribution records what was submitted,
by whom, and from which revision; it does not certify the truth of the text. Approval freezes the
original document. Later corrections append receipts, leaving that original recoverable.
-/

@[expose] public section

namespace Parliament

/-- Optimistic reference to one meeting's current document version. -/
structure MinutesRef where
  /-- Meeting whose minutes are being edited. -/
  meeting : Nat
  /-- Expected version before the proposed edit. -/
  version : Nat
  deriving DecidableEq, Repr

/-- A document submitted by the configured secretary for a completed meeting. -/
structure MinutesSubmission (D : MotionDomain) where
  /-- Completed meeting being recorded. -/
  meeting : Nat
  /-- Revision of that meeting's recorded adjournment. -/
  sourceRevision : Nat
  /-- Attributed submitting member. -/
  secretary : MemberId
  /-- Original submission, retained even after correction. -/
  text : D.Content
  deriving DecidableEq

/-- An adopted replacement, cross-referenced to the meeting that adopted it. -/
structure MinutesCorrection (D : MotionDomain) where
  /-- Meeting that adopted the correction. -/
  meeting : Nat
  /-- Accepted decision revision. -/
  revision : Nat
  /-- Full replacement reading; not an overwrite of the approved original. -/
  text : D.Content
  deriving DecidableEq

/-- Original approval metadata and exact approved text. -/
structure MinutesApproval (D : MotionDomain) where
  /-- Meeting in which initial approval was declared. -/
  meeting : Nat
  /-- Accepted approval revision. -/
  revision : Nat
  /-- Draft version that was approved. -/
  version : Nat
  /-- Exact immutable original approved text. -/
  text : D.Content
  deriving DecidableEq

/-- Draft changes and postapproval corrections have deliberately different storage. -/
structure MinutesDocument (D : MotionDomain) where
  /-- Attributed original text and source snapshot. -/
  submission : MinutesSubmission D
  /-- Text under initial review, frozen on approval. -/
  draft : D.Content
  /-- Number of adopted preapproval corrections. -/
  draftVersion : Nat := 0
  /-- Original approval, absent while still a draft. -/
  approval : Option (MinutesApproval D) := none
  /-- Later adopted corrections, oldest first. -/
  corrections : List (MinutesCorrection D) := []
  deriving DecidableEq

/-- The visible text applies receipts without overwriting the original approval. -/
def MinutesDocument.text {D : MotionDomain} (doc : MinutesDocument D) : D.Content :=
  match doc.corrections.getLast? with
  | some receipt => receipt.text
  | none => doc.approval.map (·.text) |>.getD doc.draft

/-- Each adopted correction advances the document version once. -/
def MinutesDocument.ref {D : MotionDomain} (doc : MinutesDocument D) : MinutesRef :=
  ⟨doc.submission.meeting, doc.draftVersion + doc.corrections.length⟩

/-- Before approval replace the draft; afterward append a cross-reference and replacement. -/
def MinutesDocument.correct {D : MotionDomain} (doc : MinutesDocument D)
    (receipt : MinutesCorrection D) : MinutesDocument D :=
  if doc.approval.isSome then { doc with corrections := doc.corrections ++ [receipt] }
  else { doc with draft := receipt.text, draftVersion := doc.draftVersion + 1 }

/-- Approval agrees with the frozen draft; an unapproved document has no later receipts. -/
def MinutesDocument.WellFormed {D : MotionDomain} (doc : MinutesDocument D) : Prop :=
  (∀ approved ∈ doc.approval.toList,
    approved.version = doc.draftVersion ∧ approved.text = doc.draft) ∧
  (doc.approval = none → doc.corrections = [])

instance {D : MotionDomain} (doc : MinutesDocument D) : Decidable doc.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The raw correction operation preserves document coherence, before any transaction gate. -/
theorem MinutesDocument.correct_wellFormed {D : MotionDomain}
    (doc : MinutesDocument D) (receipt : MinutesCorrection D) (h : doc.WellFormed) :
    (doc.correct receipt).WellFormed := by
  rcases h with ⟨ha, hc⟩
  unfold correct
  split
  · rename_i hsome
    refine ⟨ha, ?_⟩
    intro hnone
    change doc.approval = none at hnone
    simp [hnone] at hsome
  · rename_i hnone
    have hn : doc.approval = none := by simpa using hnone
    simp [WellFormed, hn, hc hn]

/-- Initial approval freezes the draft without replacing an existing approval. -/
def MinutesDocument.approve {D : MotionDomain} (doc : MinutesDocument D)
    (meeting revision : Nat) : MinutesDocument D :=
  if doc.approval.isSome then doc
  else { doc with approval := some ⟨meeting, revision, doc.draftVersion, doc.draft⟩ }

theorem MinutesDocument.approve_wellFormed {D : MotionDomain}
    (doc : MinutesDocument D) (meeting revision : Nat) (h : doc.WellFormed) :
    (doc.approve meeting revision).WellFormed := by
  unfold approve
  split
  · exact h
  · simp [WellFormed]

/-- Corrections cannot rewrite either the submitted snapshot or the approved original. -/
theorem MinutesDocument.correct_preserves_original {D : MotionDomain}
    (doc : MinutesDocument D) (receipt : MinutesCorrection D) :
    (doc.correct receipt).submission = doc.submission ∧
    (doc.correct receipt).approval = doc.approval := by
  unfold correct
  split <;> exact ⟨rfl, rfl⟩

/-- Narrow prior-meeting notice: the notified replacement must remain exactly unchanged.
Meeting-call notice and judgments about a broader semantic scope are outside this subset. -/
structure MinutesNotice (D : MotionDomain) where
  /-- Version to which the notified correction applies. -/
  target : MinutesRef
  /-- Exact notified wording in this narrow notice profile. -/
  text : D.Content
  /-- Meeting in which notice was given. -/
  meeting : Nat
  /-- Date used for the quarterly-interval check. -/
  date : Date
  /-- Present member who gave notice. -/
  actor : MemberId
  deriving DecidableEq

end Parliament
