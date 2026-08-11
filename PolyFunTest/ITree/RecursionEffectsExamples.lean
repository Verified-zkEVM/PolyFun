/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Rec.Facts
public import PolyFun.ITree.Events.StateFacts
public import PolyFun.ITree.Events.ExceptionFacts

/-! # Recursive procedures and effect runners

Executable examples for the recursive-call equations and the canonical state
and exception interpreters.
-/

@[expose] public section

namespace PolyFunTest.RecursionEffects

attribute [local implicit_reducible] ITree.interpState ITree.runState ITree.interpExcept
  ITree.interpMrec ITree.fixRec ITree.CallE

open ITree

inductive ExternalShape where
  | read

def External : PFunctor where
  A := ExternalShape
  B _ := Nat

attribute [local implicit_reducible] External

def stateProgram : ITree (StateE Nat + External) Nat :=
  ITree.query (F := StateE Nat + External)
    (Sum.inl StateE.Shape.get) fun s : Nat =>
      ITree.query (F := StateE Nat + External)
        (Sum.inl (StateE.Shape.put (s + 1))) fun _ : PUnit =>
          ITree.pure s

example : runState stateProgram 4 =
    ITree.step (ITree.step (ITree.pure (F := External) (5, 4))) := by
  rw [runState_eq_interpState]
  unfold stateProgram
  rw [interpState_get, interpState_put, interpState_pure]

/-- The state bind law threads the updated state into the continuation while
retaining the program's return value. -/
example : interpState
    (ITree.bind stateProgram fun n =>
      ITree.pure (F := StateE Nat + External) (n + 10)) 4 =
    ITree.step (ITree.step (ITree.pure (F := External) (5, 14))) := by
  rw [interpState_bind]
  simp only [interpState_pure]
  rw [show interpState stateProgram 4 =
    ITree.step (ITree.step (ITree.pure (F := External) (5, 4))) by
      unfold stateProgram
      rw [interpState_get, interpState_put, interpState_pure]]
  rw [bind_step, bind_step, bind_pure_left]

def stateExternal : ITree (StateE Nat + External) Nat :=
  ITree.query (F := StateE Nat + External) (Sum.inr ExternalShape.read)
    (fun n : Nat => ITree.pure n)

example : runState stateExternal 4 =
    ITree.query ExternalShape.read
      (fun n => ITree.pure (F := External) (4, n)) := by
  rw [runState_eq_interpState]
  unfold stateExternal
  rw [interpState_query_external]
  congr 1
  funext n
  rw [interpState_pure]

def throws : ITree (ExceptE String + External) Nat :=
  ITree.query (F := ExceptE String + External) (Sum.inl "boom") PEmpty.elim

example : runExcept throws =
    ITree.pure (F := External) (Except.error "boom") := by
  rw [runExcept_eq_interpExcept]
  unfold throws
  rw [interpExcept_throw]

/-- The exception bind law bypasses a continuation after the first error. -/
example : interpExcept
    (ITree.bind throws fun n =>
      ITree.pure (F := ExceptE String + External) (n + 1)) =
    ITree.pure (F := External) (Except.error "boom") := by
  rw [interpExcept_bind]
  simp only [interpExcept_pure]
  rw [show interpExcept throws =
    ITree.pure (F := External) (Except.error "boom") by
      unfold throws
      rw [interpExcept_throw]]
  rw [bind_pure_left]

def succeeds : ITree (ExceptE String + External) Nat :=
  ITree.query (F := ExceptE String + External) (Sum.inr ExternalShape.read)
    (fun n : Nat => ITree.pure n)

example : runExcept succeeds =
    ITree.query ExternalShape.read
      (fun n => ITree.pure (F := External) (Except.ok n)) := by
  rw [runExcept_eq_interpExcept]
  unfold succeeds
  rw [interpExcept_query_external]
  congr 1
  funext n
  rw [interpExcept_pure]

def countdownBody : Nat → ITree (CallE Nat Nat + External) Nat
  | 0 => ITree.pure 0
  | n + 1 => ITree.query (F := CallE Nat Nat + External) (Sum.inl n)
      (fun r : Nat => ITree.pure (r + 1))

example (n : Nat) :
    fixRec countdownBody (n + 1) =
      ITree.step (ITree.bind (fixRec countdownBody n)
        (fun r => ITree.pure (F := External) (r + 1))) := by
  rw [fixRec_eq_interpMrec]
  rw [show countdownBody (n + 1) = ITree.query (F := CallE Nat Nat + External)
      (Sum.inl n) (fun r : Nat => ITree.pure (r + 1)) from rfl]
  rw [interpMrec_query_recursive]
  congr 1
  rw [interpMrec_bind, ← fixRec_eq_interpMrec]
  apply congrArg (ITree.bind (fixRec countdownBody n))
  funext a
  rw [interpMrec_pure]

example (n : Nat) :
    ITree.recursiveHandler (D := CallE Nat Nat) (E := External)
        countdownBody (Sum.inl n) =
      ITree.mutualRec (D := CallE Nat Nat) (E := External)
        countdownBody n := rfl

example :
    ITree.recursiveHandler (D := CallE Nat Nat) (E := External)
        countdownBody (Sum.inr ExternalShape.read) =
      ITree.Handler.id External ExternalShape.read := rfl

example (n : Nat) :
    ITree.WeakBisim
      (ITree.interpMrec countdownBody
        (ITree.lift (F := CallE Nat Nat + External) (Sum.inl n)))
      (ITree.recursiveHandler (D := CallE Nat Nat) (E := External)
        countdownBody (Sum.inl n)) :=
  ITree.interpMrec_lift_inl (D := CallE Nat Nat) (E := External)
    countdownBody n

example :
    ITree.WeakBisim
      (ITree.interpMrec countdownBody
        (ITree.lift (F := CallE Nat Nat + External)
          (Sum.inr ExternalShape.read)))
      (ITree.recursiveHandler (D := CallE Nat Nat) (E := External)
        countdownBody (Sum.inr ExternalShape.read)) :=
  ITree.interpMrec_lift_inr (D := CallE Nat Nat) (E := External)
    countdownBody ExternalShape.read

/-! The runners retain the intended independent universes. -/

def LargeExternal : PFunctor.{0, 1} where
  A := Bool
  B _ := Type

def largeStateRunner (t : ITree (StateE Type + LargeExternal) Bool) :
    Type → ITree LargeExternal (Type × Bool) :=
  interpState t

def WideExternal : PFunctor.{0, 2} where
  A := Bool
  B _ := Type 1

def largeExceptionRunner
    (t : ITree (ExceptE.{1, 2} Type + WideExternal) Bool) :
    ITree WideExternal (Except Type Bool) :=
  interpExcept t

end PolyFunTest.RecursionEffects
