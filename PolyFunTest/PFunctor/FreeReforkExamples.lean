/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Cursor.Refork
public import PolyFunTest.PFunctor.FreeCursorOccurrenceExamples

/-! # Free-program reforking examples -/

@[expose] public section

open PFunctor

universe uA uB uα uκ uβ

namespace PFunctor.FreeM.Cursor

example : (locateAt? ExampleOp.target rootProgram rootFalsePath 0).isSome := by
  decide

example : (locateAt? ExampleOp.target nestedProgram nestedFalsePath 0).isSome := by
  rw [locateAt?_isSome_iff_lt_occurrences]
  decide

/-- The terminating branch contains no second target occurrence. -/
example : locateAt? ExampleOp.target nestedProgram nestedFalsePath 1 = none := rfl

/-- The continuing branch does contain a second target occurrence. -/
example : (locateAt? ExampleOp.target nestedProgram nestedTrueTruePath 1).isSome := by
  rw [locateAt?_isSome_iff_lt_occurrences]
  decide

/-- A root-only target program contains no noise occurrence. -/
example : locateAt? ExampleOp.noise rootProgram rootTruePath 0 = none := rfl

example : forkAt ExampleOp.target rootProgram 0 =
    reforkAt ExampleOp.target rootProgram 0 :=
  forkAt_eq_reforkAt ExampleOp.target rootProgram 0

example : forkAt ExampleOp.target nestedProgram 0 =
    reforkAt ExampleOp.target nestedProgram 0 :=
  forkAt_eq_reforkAt ExampleOp.target nestedProgram 0

/-- Reject equal focused answers and retain observably different forks. -/
def classifyDifferent (view : ForkView ExampleOp.target nestedProgram 0) :
    Option (Nat × Nat) :=
  if view.firstAnswer = view.secondAnswer then none
  else some (output nestedProgram view.firstPath,
    output nestedProgram view.secondPath)

example : classifyDifferent nestedFork = some (101, 211) := rfl

def equalAnswerFork : ForkView ExampleOp.target rootProgram 0 where
  occurrence := .here _
  first := ⟨false, ⟨⟩⟩
  second := ⟨false, ⟨⟩⟩

example : (if equalAnswerFork.firstAnswer = equalAnswerFork.secondAnswer then
      none else some (equalAnswerFork.firstAnswer, equalAnswerFork.secondAnswer)) =
    none := rfl

/-- Rejecting selection performs no reforking. -/
example : reforkBy ExampleOp.target rootProgram
    (fun _ => (none : Option Unit)) (fun _ => 0)
    (fun _ _ => ()) =
    FreeM.liftBind ExampleOp.target fun _ => pure none := rfl

/-- Accepted selection retains independently sampled, observably distinct
answers in the two output components. -/
example : FreeM.map (Option.map SelectedForkView.outputs)
      (reforkSelected ExampleOp.target rootProgram
        (fun _ => some ()) (fun _ => 0)) =
    FreeM.liftBind ExampleOp.target fun first =>
      FreeM.liftBind ExampleOp.target fun second =>
        pure (some (rootValue first, rootValue second)) := rfl

/-- Selecting a missing ordinal returns `none` after only the original
program execution; no second target query is introduced. -/
example : reforkSelected ExampleOp.target rootProgram
      (fun _ => some ()) (fun _ => 1) =
    FreeM.liftBind ExampleOp.target fun _ => pure none := rfl

/-- A rejecting classifier is applied after both completions. -/
example : filterMapReforkAt ExampleOp.target rootProgram 0 (fun _ =>
      (none : Option Unit)) =
    FreeM.liftBind ExampleOp.target fun _ =>
      FreeM.liftBind ExampleOp.target fun _ => pure none := rfl

example : filterMapReforkAt ExampleOp.target nestedProgram 0 classifyDifferent =
    FreeM.bind (withPath nestedProgram) fun path =>
      match locateAt? ExampleOp.target nestedProgram path 0 with
      | none => pure none
      | some located =>
          FreeM.map (fun second => classifyDifferent {
            occurrence := located.occurrence
            first := located.completion
            second := second }) located.occurrence.complete :=
  filterMapReforkAt_eq_bind_complete ExampleOp.target nestedProgram 0 classifyDifferent

/-- The dynamic API keeps operation, answer, output, selector, and observer
universes independent. -/
def universeCanary {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    {α : Type uα} {κ : Type uκ} {β : Type uβ}
    (target : P.A) (program : FreeM P α)
    (select : α → Option κ) (index : κ → Nat)
    (observe : (k : κ) → ForkView target program (index k) → β) :
    FreeM P (Option β) :=
  reforkBy target program select index observe

/-- Mapping over fixed reforking needs equality only on positions, not on
every dependent answer family. -/
example {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    {α : Type uα} (target : P.A) (program : FreeM P α) (n : Nat) :
    FreeM.map id (reforkAt target program n) =
      FreeM.bind (withPath program) fun path =>
        match locateAt? target program path n with
        | none => pure none
        | some located => FreeM.map (id ∘ some) located.refork :=
  map_reforkAt target program n id

end PFunctor.FreeM.Cursor
