/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Trace

/-! # Finite ITree observation examples -/

@[expose] public section

namespace PolyFunTest.TraceExamples

inductive Command where
  | choose

@[reducible] def ChoiceE : PFunctor where
  A := Command
  B _ := Bool

open ITree

def chooseNat : ITree ChoiceE Nat :=
  ITree.query (F := ChoiceE) Command.choose fun answer : Bool =>
    ITree.pure (if answer then 1 else 0)

example : [Observation.ret 7] ∈
    ITree.traces (ITree.pure (F := ChoiceE) 7) :=
  ret_mem_traces 7

example : [Observation.ret 8] ∉
    ITree.traces (ITree.pure (F := ChoiceE) 7) := by
  simp

example : [Observation.event Command.choose true] ∉
    ITree.traces (ITree.pure (F := ChoiceE) 7) := by
  simp

example : [Observation.event Command.choose true, Observation.ret 1] ∈
    ITree.traces chooseNat := by
  unfold chooseNat
  apply event_cons_mem_traces (F := ChoiceE) (α := Nat)
    (observations := [Observation.ret 1]) Command.choose
    (fun answer : Bool => ITree.pure (if answer then 1 else 0)) true
  simp

example : [Observation.event Command.choose false, Observation.ret 0] ∈
    ITree.traces chooseNat := by
  unfold chooseNat
  apply event_cons_mem_traces (F := ChoiceE) (α := Nat)
    (observations := [Observation.ret 0]) Command.choose
    (fun answer : Bool => ITree.pure (if answer then 1 else 0)) false
  simp

example : ITree.traces (ITree.step chooseNat) = ITree.traces chooseNat :=
  traces_step chooseNat

example (t s : ITree ChoiceE Nat) (h : WeakBisim t s) :
    ITree.traces t = ITree.traces s :=
  traces_eq_of_weakBisim h

/-! Observation, event-reply, and return universes remain independent. -/

def LargeReplyE : PFunctor.{0, 1} where
  A := Bool
  B _ := Type

def mixedUniverseTraces (t : ITree LargeReplyE (Type 1)) :
    Set (List (Observation LargeReplyE (Type 1))) :=
  ITree.traces t

end PolyFunTest.TraceExamples
