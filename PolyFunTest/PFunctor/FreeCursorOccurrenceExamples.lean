/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Cursor.Occurrence

/-! # Typed free-program occurrence examples -/

@[expose] public section

open PFunctor

namespace PFunctor.FreeM.Cursor

/-- Operations whose answer type genuinely depends on the selected position. -/
inductive ExampleOp
  | noise
  | target
  deriving DecidableEq

/-- Noise returns a finite tag; target queries return a branch bit. -/
abbrev ExampleAnswer : ExampleOp → Type
  | .noise => Fin 2
  | .target => Bool

abbrev ExampleQuery : PFunctor := ⟨ExampleOp, ExampleAnswer⟩

def noiseOne : Fin 2 := 1

/-- A root target whose answer is directly observable in the output. -/
def rootValue (answer : Bool) : Nat :=
  if answer = true then 11 else 7

def rootProgram : FreeM ExampleQuery Nat :=
  FreeM.liftBind ExampleOp.target fun answer => pure (rootValue answer)

def rootFalsePath : Path rootProgram := ⟨false, ⟨⟩⟩

def rootTruePath : Path rootProgram := ⟨true, ⟨⟩⟩

/-- The first target may terminate immediately or expose a second target.
Both the residual shape and final output depend on earlier answers. -/
def nestedProgram : FreeM ExampleQuery Nat :=
  FreeM.liftBind ExampleOp.noise fun tag =>
    FreeM.liftBind ExampleOp.target fun first =>
      match first with
      | false => pure (100 + tag.val)
      | true =>
          FreeM.liftBind ExampleOp.target fun second =>
            pure (200 + 10 * tag.val + if second = true then 1 else 0)

def nestedFalsePath : Path nestedProgram :=
  ⟨noiseOne, ⟨false, ⟨⟩⟩⟩

def nestedTrueTruePath : Path nestedProgram :=
  ⟨noiseOne, ⟨true, ⟨true, ⟨⟩⟩⟩⟩

/-- The first target, reached after a non-target prefix. -/
def nestedOccurrence : Occurrence ExampleOp.target nestedProgram 0 :=
  .stepOther (by decide) noiseOne (.here _)

/-- Two completions with different focused answers and residual shapes. -/
def nestedFork : ForkView ExampleOp.target nestedProgram 0 where
  occurrence := nestedOccurrence
  first := ⟨false, ⟨⟩⟩
  second := ⟨true, ⟨true, ⟨⟩⟩⟩

example : nestedOccurrence.toCursor.residual =
    FreeM.liftBind ExampleOp.target nestedOccurrence.resume := rfl

example : nestedOccurrence.before =
    [(⟨ExampleOp.noise, noiseOne⟩ : ExampleQuery.Idx)] := rfl

example : nestedOccurrence.plug false ⟨⟩ = nestedFalsePath := rfl

example : nestedOccurrence.plug true ⟨true, ⟨⟩⟩ = nestedTrueTruePath := rfl

example : nestedFork.firstAnswer = false := rfl

example : nestedFork.secondAnswer = true := rfl

example : PFunctor.TraceList.getAt? (Path.trace nestedProgram nestedFork.first.path)
    ExampleOp.target 0 = some nestedFork.first.answer := by
  exact Occurrence.getAt?_trace_completion_path nestedOccurrence nestedFork.first

example : output nestedProgram nestedFork.firstPath = 101 := rfl

example : output nestedProgram nestedFork.secondPath = 211 := rfl

example : FreeM ExampleQuery
    {result : Split ExampleOp.target nestedProgram 0 // result.Valid} :=
  splitAtValid ExampleOp.target nestedProgram 0

example :
    FreeM.bind (splitAtValid ExampleOp.target nestedProgram 0)
        (fun result => result.val.complete) =
      withPath nestedProgram :=
  splitAtValid_bind_complete ExampleOp.target nestedProgram 0

example : forkAt ExampleOp.target nestedProgram 0 =
    FreeM.bind (splitAtValid ExampleOp.target nestedProgram 0)
      (fun result => result.val.completeFork) :=
  (splitAtValid_bind_completeFork ExampleOp.target nestedProgram 0).symm

end PFunctor.FreeM.Cursor
