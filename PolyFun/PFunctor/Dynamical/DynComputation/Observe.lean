/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.Trace
public import PolyFun.PFunctor.Dynamical.DynComputation.Resumable

/-!
# State-aware observation of machine execution

An observation uses the state before a query and its typed answer. Accumulating
in a monoid retains ordered logs as well as additive costs. The wrapper records
observations in its residual state, including when a chunk pauses before return.
Terminal observation consumes no fuel and adds no query observation.
-/

public section

namespace PFunctor.DynSystem.DynComputation

universe u uA uB uα uβ uW

variable {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {W : Type uW} [Monoid W]

/-- Record each actual transition without changing its operation or answer. -/
@[expose] def observeStep (machine : DynComputation.{u} P α β)
    (observe : machine.toDynSystem.EventMap W) :
    machine.State × W → (β × W) ⊕ P.Obj (machine.State × W)
  | (state, accumulated) => match h : machine.view state with
    | .inl value => .inl (value, accumulated)
    | .inr ⟨a, next⟩ => .inr ⟨a, fun answer =>
        (next answer, accumulated * observe.atOut (ExecutionTrace.out_eq_of_view_query h) answer)⟩

/-- A machine with a persistent accumulator, initialized by the caller. -/
@[expose, implicit_reducible] def withAccumulator (machine : DynComputation.{u} P α β)
    (observe : machine.toDynSystem.EventMap W) :
    DynComputation.{max u uW} P (α × W) (β × W) :=
  .ofStep (machine.observeStep observe) (fun input => (machine.init input.1, input.2))

/-- The accumulated machine exposes its computational transition. -/
theorem view_withAccumulator (machine : DynComputation.{u} P α β)
    (observe : machine.toDynSystem.EventMap W) (state : machine.State × W) :
    (machine.withAccumulator observe).view state = machine.observeStep observe state :=
  view_ofStep _ _ _

/-- Returning a value preserves the accumulated observations. -/
@[simp] theorem view_withAccumulator_pure (machine : DynComputation.{u} P α β)
    (observe : machine.toDynSystem.EventMap W) {state : machine.State} {value : β}
    (h : machine.view state = .inl value) (accumulated : W) :
    (machine.withAccumulator observe).view (state, accumulated) = .inl (value, accumulated) := by
  rw [view_withAccumulator]
  simp only [observeStep]
  split
  · rename_i value' hv
    cases Sum.inl.inj (hv.symm.trans h)
    rfl
  · rename_i a next hv
    have heq := hv.symm.trans h
    cases heq

/-- Each query appends exactly its state-aware observation. -/
theorem view_withAccumulator_query (machine : DynComputation.{u} P α β)
    (observe : machine.toDynSystem.EventMap W) {state : machine.State} {a : P.A}
    {next : P.B a → machine.State} (h : machine.view state = .inr ⟨a, next⟩)
    (accumulated : W) :
    (machine.withAccumulator observe).view (state, accumulated) =
      .inr ⟨a, fun answer => (next answer,
        accumulated * observe.atOut (ExecutionTrace.out_eq_of_view_query h) answer)⟩ := by
  rw [view_withAccumulator]
  simp only [observeStep]
  split
  · rename_i value hv
    have heq := hv.symm.trans h
    cases heq
  · rename_i a' next' hv
    cases Sum.inr.inj (hv.symm.trans h)
    rfl

/-- Erasing observations preserves every bounded residual execution, including pauses. -/
theorem map_unrollChunk_withAccumulator (machine : DynComputation.{u} P α β)
    (observe : machine.toDynSystem.EventMap W) (fuel : Nat) (state : machine.State)
    (accumulated : W) :
    FreeM.map (Chunk.map Prod.fst Prod.fst)
        ((machine.withAccumulator observe).unrollChunk fuel (state, accumulated)) =
      machine.unrollChunk fuel state := by
  induction fuel generalizing state accumulated with
  | zero =>
      rcases h : machine.view state with value | ⟨a, next⟩
      · rw [unrollChunk_zero, unrollChunk_zero,
          machine.view_withAccumulator_pure observe h, h]
        rfl
      · rw [unrollChunk_zero, unrollChunk_zero,
          machine.view_withAccumulator_query observe h, h]
        rfl
  | succ fuel ih =>
      rcases h : machine.view state with value | ⟨a, next⟩
      · rw [unrollChunk_succ, unrollChunk_succ,
          machine.view_withAccumulator_pure observe h, h]
        rfl
      · rw [unrollChunk_succ, unrollChunk_succ,
          machine.view_withAccumulator_query observe h, h]
        change FreeM.liftBind a (fun answer =>
          FreeM.map (Chunk.map Prod.fst Prod.fst)
            ((machine.withAccumulator observe).unrollChunk fuel
              (next answer, accumulated * observe.atOut
                (ExecutionTrace.out_eq_of_view_query h) answer))) = _
        exact congrArg (FreeM.liftBind a) (funext fun answer => ih (next answer) _)

namespace ExecutionTrace

variable {machine : DynComputation.{u} P α β}

/-- Accumulate the generic orbit observations of a machine trace. -/
@[expose] def accumulate (observe : machine.toDynSystem.EventMap W)
    {start finish : machine.State} (trace : machine.ExecutionTrace start finish) : W :=
  trace.toPrefix.accumulate observe

@[simp] theorem accumulate_nil (observe : machine.toDynSystem.EventMap W)
    (state : machine.State) : (nil state).accumulate observe = 1 := by
  change ((nil state).toPrefix.events observe).prod = 1
  rw [toPrefix_nil]
  exact congrArg List.prod (Prefix.events_nil observe)

@[simp] theorem accumulate_query (observe : machine.toDynSystem.EventMap W)
    {state finish : machine.State} {a : P.A} {next : P.B a → machine.State}
    (h : machine.view state = .inr ⟨a, next⟩) (answer : P.B a)
    (tail : machine.ExecutionTrace (next answer) finish) :
    (query h answer tail).accumulate observe =
      observe.atOut (out_eq_of_view_query h) answer * tail.accumulate observe := by
  change ((query h answer tail).toPrefix.events observe).prod = _
  have hevents := congrArg (Prefix.events observe) (toPrefix_query h answer tail)
  have hstep := Prefix.events_stepOfOut observe (out_eq_of_view_query h) answer tail.toPrefix
  exact (congrArg List.prod (hevents.trans hstep)).trans List.prod_cons

/-- Observations compose across any adjacent syntactic prefixes. -/
theorem accumulate_append (observe : machine.toDynSystem.EventMap W)
    {start middle finish : machine.State} (first : machine.ExecutionTrace start middle)
    (second : machine.ExecutionTrace middle finish) :
    (first.append second).accumulate observe =
      first.accumulate observe * second.accumulate observe := by
  induction first with
  | nil => simp only [append, accumulate_nil, one_mul]
  | query h answer tail ih => simp only [append, accumulate_query, ih, mul_assoc]

/-- Every source trace lifts with its exact accumulated observations as the endpoint. -/
def withAccumulator (observe : machine.toDynSystem.EventMap W)
    {start finish : machine.State} (trace : machine.ExecutionTrace start finish)
    (accumulated : W) :
    (machine.withAccumulator observe).ExecutionTrace (start, accumulated)
      (finish, accumulated * trace.accumulate observe) :=
  match trace with
  | .nil state => by simpa only [accumulate_nil, mul_one] using
      (nil (state, accumulated) : (machine.withAccumulator observe).ExecutionTrace _ _)
  | .query h answer tail => by
      simpa only [accumulate_query, mul_assoc] using
        query (machine.view_withAccumulator_query observe h accumulated) answer
          (tail.withAccumulator observe
            (accumulated * observe.atOut (out_eq_of_view_query h) answer))

end ExecutionTrace
end PFunctor.DynSystem.DynComputation
