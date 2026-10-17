/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Bound

/-!
# Roll bounds through error-handling transformers

A console form in `ExceptT String (FreeM Console)` reads lines and may reject its input. The
transformer lemmas bound each step by its own reads: sequencing forms adds their bounds in one
step, and a rejection performs no further read. `OptionT` forms behave the same way.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.BoundTransformer

open _root_.PFunctor

/-- Each query shows a prompt and reads one line. -/
abbrev Console : PFunctor.{0, 0} := ⟨String, fun _ => String⟩

/-- A console form that may reject its input. -/
abbrev Form := ExceptT String (FreeM Console)

/-- Read one line. -/
def text (prompt : String) : Form String := ExceptT.lift (FreeM.lift prompt)

/-- Read one line and parse a natural number, rejecting anything else. -/
def natural (prompt : String) : Form Nat := do
  let line ← text prompt
  match line.toNat? with
  | some n => pure n
  | none => throw s!"not a number: {line}"

/-- Read two numbers and return their sum. -/
def sum : Form Nat := do
  let first ← natural "first"
  let second ← natural "second"
  pure (first + second)

/-- The bind bound for forms is the transformer lemma itself. -/
theorem form_bind_bound {α β : Type} (first : Form α) (next : α → Form β) {a b : Nat}
    (hfirst : first.run.IsTotalRollBound a)
    (hnext : ∀ value, (next value).run.IsTotalRollBound b) :
    (first >>= next).run.IsTotalRollBound (a + b) :=
  FreeM.isTotalRollBound_exceptT_bind hfirst hnext

theorem text_bound (prompt : String) : (text prompt).run.IsTotalRollBound 1 :=
  (FreeM.isTotalRollBound_exceptT_lift_iff _ _).mpr
    ((FreeM.isRollBound_lift_iff _ _ _ _).mpr one_pos)

/-- A rejected line exits without a further read. -/
theorem natural_bound (prompt : String) : (natural prompt).run.IsTotalRollBound 1 :=
  FreeM.isTotalRollBound_exceptT_bind (n₂ := 0) (text_bound prompt) fun line => by
    cases line.toNat? with
    | some n => exact FreeM.isTotalRollBound_exceptT_pure n 0
    | none => exact FreeM.isTotalRollBound_exceptT_throw _ 0

theorem sum_bound : sum.run.IsTotalRollBound 2 :=
  FreeM.isTotalRollBound_exceptT_bind (natural_bound _) fun _ =>
    FreeM.isTotalRollBound_exceptT_bind (n₂ := 0) (natural_bound _) fun _ =>
      FreeM.isTotalRollBound_exceptT_pure _ 0

/-- The bound is not vacuous: a form that reads a line has no zero bound. -/
example : ¬ (text "name").run.IsTotalRollBound 0 := fun h =>
  absurd ((FreeM.isRollBound_lift_iff _ _ _ _).mp
    ((FreeM.isTotalRollBound_exceptT_lift_iff _ _).mp h)) (lt_irrefl 0)

/-- An error short-circuits the continuation, whatever it does. -/
example (next : Nat → Form Nat) :
    (throw "rejected" >>= next : Form Nat).run.IsTotalRollBound 0 := by
  simp

/-- A form that gives up on an empty line, in `OptionT`. -/
def nonempty (prompt : String) : OptionT (FreeM Console) String := do
  let line ← OptionT.lift (FreeM.lift prompt)
  if line.isEmpty then failure else pure line

theorem nonempty_bound (prompt : String) : (nonempty prompt).run.IsTotalRollBound 1 :=
  FreeM.isTotalRollBound_optionT_bind (n₂ := 0)
    ((FreeM.isTotalRollBound_optionT_lift_iff _ _).mpr
      ((FreeM.isRollBound_lift_iff _ _ _ _).mpr one_pos))
    fun line => by
      cases line.isEmpty
      · exact FreeM.isTotalRollBound_optionT_pure line 0
      · exact FreeM.isTotalRollBound_optionT_failure 0

end PolyFunTest.PFunctor.BoundTransformer
