/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.Machine
public import PolyFun.PFunctor.Dynamical.DynComputation.Bounded
meta import PolyFun.ITree.Machine
meta import PolyFun.PFunctor.Dynamical.DynComputation.Bounded

/-!
# Interaction trees as machines: examples

The denotation of `ITree.toDynComputation` on each constructor, through the resumption-with-tau
equations. A silent step is a query at the `y` summand; a visible event is a query at `F`.
-/

public section

open PFunctor

namespace ITree.MachineExamples

variable {F : PFunctor.{0, 0}} {α : Type}

example (a : α) :
    (ITree.toDynComputation (F := F)).denote (ITree.pure a) = Resumption.pure a := by
  simp

example (t : ITree F α) :
    (ITree.toDynComputation (F := F)).denote (ITree.step t) =
      Resumption.query (p := F + PFunctor.y) (Sum.inr PUnit.unit)
        (fun _ => ITree.toResumptionWithTau t) := by
  simp

example (position : F.A) (next : F.B position → ITree F α) :
    (ITree.toDynComputation (F := F)).denote (ITree.query position next) =
      Resumption.query (p := F + PFunctor.y) (Sum.inl position)
        (fun direction => ITree.toResumptionWithTau (next direction)) := by
  simp

/-- The dynamical-system reading unfolds to the raw M-type tree. -/
example (t : ITree F α) : (ITree.toDynSystem (F := F) (α := α)).behavior t = t.toM := by
  rw [ITree.behavior_toDynSystem]

/-! The adapter is executable: a bounded run of a tree with one silent step and one visible
query needs two units of fuel, one for each. -/

/-- A single Boolean query. -/
abbrev Coin : PFunctor := ⟨Unit, fun _ => Bool⟩

/-- One silent step, then a query whose answer selects the returned value. -/
def coinTree : ITree Coin ℕ :=
  ITree.step (ITree.query () fun b => ITree.pure (if b then 7 else 11))

/-- Answer every query with `b`. -/
def answer (b : Bool) : PFunctor.Handler Id (Coin + PFunctor.y) := fun
  | .inl _ => b
  | .inr _ => PUnit.unit

/-- info: [none, some 7, some 11] -/
#guard_msgs in
#eval [Id.run ((ITree.toDynComputation.run 1 coinTree).liftM (answer true)),
  Id.run ((ITree.toDynComputation.run 2 coinTree).liftM (answer true)),
  Id.run ((ITree.toDynComputation.run 2 coinTree).liftM (answer false))]

end ITree.MachineExamples
