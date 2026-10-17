/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.Observe
public import PolyFun.PFunctor.Dynamical.DynComputation.Pending
public import PolyFun.Realizability.Quantitative.Recost

/-!
# Execution prefixes across public abstraction boundaries

Machine traces and pending queries need no resource backend. State, interface,
answer and result universes remain independent. The quantitative adapter reuses
the same carrier, including when its cost annotation changes.
-/


public section

open PFunctor PFunctor.DynSystem

universe u uA uB uα uβ

variable {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

example (machine : DynComputation.{u} P α β) {start middle finish : machine.State}
    (first : machine.ExecutionTrace start middle) (second : machine.ExecutionTrace middle finish) :
    (first.append second).length = first.length + second.length :=
  DynComputation.ExecutionTrace.length_append first second

example (machine : DynComputation.{u} P α β) {start finish : machine.State}
    (trace : machine.ExecutionTrace start finish) :
    trace.toPrefix.last = finish := trace.last_toPrefix

example (machine : DynComputation.{u} P α β) {state : machine.State} {a : P.A}
    {next : P.B a → machine.State}
    (h : machine.view state = .inr ⟨a, next⟩) (answer : P.B a) :
    (DynComputation.Pending.ofView h).resume answer = next answer :=
  DynComputation.Pending.resume_ofView h answer

example (machine : DynComputation.{u} P α β) {W : Type*} [Monoid W]
    (observe : machine.toDynSystem.EventMap W)
    {start : machine.State} {n m : Nat} (first : Prefix machine.toDynSystem start n)
    (second : Prefix machine.toDynSystem first.last m) :
    (first.append second).accumulate observe =
      first.accumulate observe * second.accumulate observe :=
  Prefix.accumulate_append observe first second

example (machine : DynComputation.{u} P α β) {W : Type*} [Monoid W]
    (observe : machine.toDynSystem.EventMap W) (fuel : Nat) (state : machine.State)
    (accumulated : W) :
    FreeM.map (DynComputation.Chunk.map Prod.fst Prod.fst)
        ((machine.withAccumulator observe).unrollChunk fuel (state, accumulated)) =
      machine.unrollChunk fuel state :=
  machine.map_unrollChunk_withAccumulator observe fuel state accumulated

example (machine : DynComputation.{u} P α β) {W : Type*} [Monoid W]
    (observe : machine.toDynSystem.EventMap W) {start finish : machine.State}
    (trace : machine.ExecutionTrace start finish) (accumulated : W) :
    (machine.withAccumulator observe).ExecutionTrace (start, accumulated)
      (finish, accumulated * trace.accumulate observe) :=
  trace.withAccumulator observe accumulated

/-- The accumulator law does not require a commutative monoid or shared universes. -/
example (machine : DynComputation.{u} P α β) {W : Type*} [Monoid W]
    (observe : machine.toDynSystem.EventMap W) (fuel : Nat) (state : machine.State)
    (left right : W) :
    (machine.withAccumulator observe).unrollChunk fuel (state, left * right) =
      FreeM.map (DynComputation.Chunk.map (fun out => (out.1, left * out.2))
        (fun out => (out.1, left * out.2)))
        ((machine.withAccumulator observe).unrollChunk fuel (state, right)) :=
  machine.unrollChunk_withAccumulator_mul observe fuel state left right
