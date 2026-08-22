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

/-- A one-node inductive program used to pin the upstream bridge. -/
def sampleSyntax : Cslib.FreeM Ask Nat :=
  Cslib.FreeM.lift Ask.ask

example : FreeContM.toFreeM (Cslib.FreeM.toFreeContM sampleSyntax) = sampleSyntax := by
  simp

end PolyFunTest.FreeCont
