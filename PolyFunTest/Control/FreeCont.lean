/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.FreeCont

/-!
# Church-encoded free transformer examples

Regression tests for effect injection, base-monad lifting, CPS elimination,
and the retraction onto upstream inductive free syntax.
-/

@[expose] public section

namespace PolyFunTest.FreeCont

/-- One effect operation returning a natural number. -/
inductive Ask : Type → Type where
  | ask : Ask Nat

/-- A Church-encoded program combining a base `Option` action with an `Ask`
request. -/
def program : FreeContT Ask Option Nat := do
  let base ← (monadLift (some 2) : FreeContT Ask Option Nat)
  let answer ← FreeContT.liftF Ask.ask
  pure (base + answer)

/-- Interpret `Ask` by replying with `3`. -/
def askHandler {α : Type} : Ask α → ContT Nat Option α
  | .ask => fun next => next 3

example : program.run askHandler some = some 5 :=
  rfl

/-- Lifting a failing base computation does not bypass the base monad or call
the final continuation. -/
def failedProgram : FreeContT Ask Option Nat :=
  monadLift none

example : failedProgram.run askHandler some = none :=
  rfl

/-- A Boolean-valued operation used to ensure `liftBind` preserves and invokes
its response-dependent continuation. -/
inductive Choose : Type → Type where
  | choose : Choose Bool

/-- The two responses take observably different continuation branches. -/
def branchProgram : FreeContM Choose Nat :=
  FreeContT.liftBind Choose.choose fun answer =>
    FreeContT.pure (if answer then 7 else 11)

/-- Interpret `Choose` with a fixed response. -/
def chooseHandler (answer : Bool) {α : Type} : Choose α → ContT Nat Id α
  | .choose => fun next => next answer

example : branchProgram.run (chooseHandler true) id = 7 :=
  rfl

example : branchProgram.run (chooseHandler false) id = 11 :=
  rfl

/-- A one-node inductive program used to pin the upstream bridge. -/
def sampleSyntax : Cslib.FreeM Ask Nat :=
  Cslib.FreeM.lift Ask.ask

example : FreeContM.toFreeM (Cslib.FreeM.toFreeContM sampleSyntax) = sampleSyntax := by
  simp

/-- The syntax bridge also preserves response-dependent continuations, rather
than only the one-node identity continuation above. -/
def branchingSyntax : Cslib.FreeM Choose Nat :=
  Cslib.FreeM.liftBind Choose.choose fun answer =>
    pure (if answer then 7 else 11)

example : FreeContM.toFreeM (Cslib.FreeM.toFreeContM branchingSyntax) = branchingSyntax := by
  simp

end PolyFunTest.FreeCont
