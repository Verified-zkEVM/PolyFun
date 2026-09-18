/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Foundation

/-!
# Motion content and structural amendment operations

The content adapter decides whether an edit can be applied, not whether its meaning
is germane. Semantic questions are exposed through the judgment interaction.
-/

@[expose] public section

namespace Parliament

/-- An executable adapter for question wording and its two amendment degrees. -/
structure MotionDomain where
  /-- The text or structured content of a main motion. -/
  Content : Type
  /-- An edit to main-motion content. -/
  Primary : Type
  /-- An edit to a pending primary amendment. -/
  Secondary : Type
  contentEq : DecidableEq Content
  primaryEq : DecidableEq Primary
  secondaryEq : DecidableEq Secondary
  /-- Apply a primary edit, rejecting structurally invalid operations. -/
  apply : Content → Primary → Option Content
  /-- Change a primary edit in the context of its original main motion. -/
  applySecondary : Content → Primary → Secondary → Option Primary

attribute [instance] MotionDomain.contentEq MotionDomain.primaryEq MotionDomain.secondaryEq

/-- Replace a contiguous range of words. Zero length inserts words. -/
structure WordEdit where
  /-- Zero-based index of the first word to replace. -/
  start : Nat
  /-- Number of original words removed. -/
  count : Nat
  /-- Replacement words; empty for a deletion. -/
  words : List String
  deriving DecidableEq, Repr

namespace WordEdit

/-- Apply an in-bounds word replacement, insertion, or deletion. -/
def apply (text : List String) (edit : WordEdit) : Option (List String) :=
  if edit.start + edit.count ≤ text.length then
    some (text.take edit.start ++ edit.words ++ text.drop (edit.start + edit.count))
  else none

theorem apply_in_bounds (text : List String) (edit : WordEdit) (out : List String)
    (h : apply text edit = some out) : edit.start + edit.count ≤ text.length := by
  unfold apply at h
  split at h
  next hbound => exact hbound
  next => contradiction

end WordEdit

/-- Secondary edits either change proposed wording or narrow a proposed deletion. -/
inductive WordSecondary where
  | wording (edit : WordEdit)
  | narrow (offset count : Nat)
  deriving DecidableEq, Repr

/-- Edit proposed replacement wording or narrow a proposed deletion. -/
def applyWordSecondary (text : List String) (primary : WordEdit)
    (secondary : WordSecondary) : Option WordEdit := do
  let _ ← primary.apply text
  match secondary with
  | .wording edit =>
    if primary.words.isEmpty then none
    else
      let words ← edit.apply primary.words
      if words.isEmpty then none else some { primary with words }
  | .narrow offset count =>
    if primary.words.isEmpty && 0 < count && offset + count ≤ primary.count then
      some { primary with start := primary.start + offset, count }
    else none

/-- An executable content instance for ordinary word amendments. -/
def wordDomain : MotionDomain where
  Content := List String
  Primary := WordEdit
  Secondary := WordSecondary
  contentEq := inferInstance
  primaryEq := inferInstance
  secondaryEq := inferInstance
  apply := WordEdit.apply
  applySecondary := applyWordSecondary

end Parliament
