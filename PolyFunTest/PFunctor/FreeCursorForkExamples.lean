/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Cursor.Fork
public import PolyFunTest.PFunctor.FreeCursorOccurrenceExamples

/-! # Free-program occurrence-forking examples -/

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
    locateAndForkAt ExampleOp.target rootProgram 0 :=
  forkAt_eq_locateAndForkAt ExampleOp.target rootProgram 0

example : forkAt ExampleOp.target nestedProgram 0 =
    locateAndForkAt ExampleOp.target nestedProgram 0 :=
  forkAt_eq_locateAndForkAt ExampleOp.target nestedProgram 0

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

/-- Rejecting selection performs no second completion. -/
example : locateAndForkBy ExampleOp.target rootProgram
    (fun _ => (none : Option Unit)) (fun _ => 0)
    (fun _ _ => ()) =
    FreeM.liftBind ExampleOp.target fun _ => pure none := rfl

/-- Accepted selection retains independently sampled, observably distinct
answers in the two output components. -/
example : FreeM.map (Option.map SelectedForkView.outputs)
      (locateAndForkSelected ExampleOp.target rootProgram
        (fun _ => some ()) (fun _ => 0)) =
    FreeM.liftBind ExampleOp.target fun first =>
      FreeM.liftBind ExampleOp.target fun second =>
        pure (some (rootValue first, rootValue second)) := rfl

/-- Selecting a missing ordinal returns `none` after only the original
program execution; no second target query is introduced. -/
example : locateAndForkSelected ExampleOp.target rootProgram
      (fun _ => some ()) (fun _ => 1) =
    FreeM.liftBind ExampleOp.target fun _ => pure none := rfl

/-! ## Output-dependent selection -/

/-- The first output selects both a label and a different target ordinal. -/
def selectOrdinalFromOutput (result : Nat) : Option Bool :=
  if result < 200 then some false else some true

/-- The low-output label selects the first target; the high-output label
selects the second target. -/
def ordinalOfLabel : Bool → Nat
  | false => 0
  | true => 1

/-- Retain enough data to distinguish the selected label, occurrence, focused
answers, and both completed outputs. -/
def observeOutputDependent (label : Bool)
    (view : ForkView ExampleOp.target nestedProgram (ordinalOfLabel label)) :
    Bool × Bool × Bool × Nat × Nat :=
  (label, view.firstAnswer, view.secondAnswer,
    output nestedProgram view.firstPath, output nestedProgram view.secondPath)

def outputDependentFork :
    FreeM ExampleQuery (Option (Bool × Bool × Bool × Nat × Nat)) :=
  locateAndForkBy ExampleOp.target nestedProgram selectOrdinalFromOutput
    ordinalOfLabel observeOutputDependent

/-- A low first output selects ordinal zero and independently takes the
continuing branch on its second completion. -/
def outputDependentLowPath : Path outputDependentFork :=
  ⟨noiseOne, ⟨false, ⟨true, ⟨false, ⟨⟩⟩⟩⟩⟩

example : output outputDependentFork outputDependentLowPath =
    some (false, false, true, 101, 210) := rfl

/-- A high first output selects ordinal one and resamples only that target. -/
def outputDependentHighPath : Path outputDependentFork :=
  ⟨noiseOne, ⟨true, ⟨true, ⟨false, ⟨⟩⟩⟩⟩⟩

example : output outputDependentFork outputDependentHighPath =
    some (true, true, false, 211, 210) := rfl

/-- A rejecting classifier is applied after both completions. -/
example : filterMapLocateAndForkAt ExampleOp.target rootProgram 0 (fun _ =>
      (none : Option Unit)) =
    FreeM.liftBind ExampleOp.target fun _ =>
      FreeM.liftBind ExampleOp.target fun _ => pure none := rfl

example : filterMapLocateAndForkAt ExampleOp.target nestedProgram 0
    classifyDifferent =
    FreeM.bind (withPath nestedProgram) fun path =>
      match locateAt? ExampleOp.target nestedProgram path 0 with
      | none => pure none
      | some located =>
          FreeM.map (fun second => classifyDifferent {
            occurrence := located.occurrence
            first := located.completion
            second := second }) located.occurrence.complete :=
  filterMapLocateAndForkAt_eq_bind_complete ExampleOp.target nestedProgram 0
    classifyDifferent

/-- The dynamic API keeps operation, answer, output, selector, and observer
universes independent. -/
def universeCanary {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    {α : Type uα} {κ : Type uκ} {β : Type uβ}
    (target : P.A) (program : FreeM P α)
    (select : α → Option κ) (index : κ → Nat)
    (observe : (k : κ) → ForkView target program (index k) → β) :
    FreeM P (Option β) :=
  locateAndForkBy target program select index observe

/-- Mapping over fixed occurrence forking needs equality only on positions,
not on every dependent answer family. -/
example {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    {α : Type uα} (target : P.A) (program : FreeM P α) (n : Nat) :
    FreeM.map id (locateAndForkAt target program n) =
      FreeM.bind (withPath program) fun path =>
        match locateAt? target program path n with
        | none => pure none
        | some located => FreeM.map (id ∘ some) located.fork :=
  map_locateAndForkAt target program n id

end PFunctor.FreeM.Cursor
