/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.TraceCost
public import PolyFun.PFunctor.Free.Support

/-!
# Executing and charging finite machine prefixes

`runPrefix` executes at most the given number of visible queries, retaining the actual reached
state and accumulated transition resources. The final observation is charged separately by
`observedCost`. Every result is witnessed by a fully syntactic `ExecutionTrace`, including a
fuel-exhausted run that has not returned. Erasing state and cost recovers ordinary bounded
unrolling of the same machine.
-/

public section

universe u v w

open MonadAttach

namespace PFunctor.DynSystem.DynComputation.QuantitativeRealization

variable {p : PFunctor.{u, u}} {α β : Type u}
  {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {bd : Boundary C p α β}

/-- Execute a finite prefix and charge each transition as it happens. -/
@[expose]
def runPrefix (R : QuantitativeRealization Q bd) :
    ℕ → R.machine.State → FreeM p (R.machine.State × ExecutionCost)
  | 0, state => pure (state, 0)
  | n + 1, state => match R.machine.view state with
    | .inl _ => pure (state, 0)
    | .inr ⟨position, next⟩ =>
        FreeM.liftBind position fun direction =>
          (fun out => (out.1, RankedResource.queryStepCost R state position direction + out.2)) <$>
            R.runPrefix n (next direction)

/-- A returned state stays fixed at every larger prefix budget and executes no transitions. -/
@[simp]
theorem runPrefix_return (R : QuantitativeRealization Q bd) (n : ℕ)
    (state : R.machine.State) (value : β) (hview : R.machine.view state = .inl value) :
    R.runPrefix n state = pure (state, 0) := by
  cases n <;> simp [runPrefix, hview]

/-- Adjacent executed prefixes compose by continuing at the reached state and adding the
actual transition resources, including the peak-size maxima in `ExecutionCost` addition. -/
theorem runPrefix_add (R : QuantitativeRealization Q bd) (n m : ℕ)
    (state : R.machine.State) :
    R.runPrefix (n + m) state = (do
      let first ← R.runPrefix n state
      let second ← R.runPrefix m first.1
      return (second.1, first.2 + second.2)) := by
  induction n generalizing state with
  | zero => simp [runPrefix]
  | succ n ih =>
      cases hview : R.machine.view state with
      | inl value => simp [runPrefix, hview]
      | inr query =>
          rcases query with ⟨position, next⟩
          simp only [Nat.succ_add, runPrefix, hview]
          apply congrArg (FreeM.liftBind position)
          funext direction
          simp [ih, map_bind, bind_map_left, add_assoc]

/-- Observe whether the reached state has returned, without consuming another query. -/
@[expose]
def returned (R : QuantitativeRealization Q bd) (state : R.machine.State) : Option β :=
  match R.machine.view state with
  | .inl value => some value
  | .inr _ => none

/-- Charge initialization and the final observation around an accumulated transition cost. -/
@[expose]
def observedCost (R : QuantitativeRealization Q bd) (input : α)
    (out : R.machine.State × ExecutionCost) : ExecutionCost :=
  ExecutionCost.ofWork (Q.cost R.initCode input) + out.2 +
    ExecutionCost.ofWork (Q.cost R.headCode out.1) +
    ExecutionCost.observe (Q.size R.state out.1) (Q.size bd.head (R.machine.head out.1))

/-- Cost erasure recovers the ordinary bounded machine semantics, including unresolved `none`. -/
theorem map_returned_runPrefix (R : QuantitativeRealization Q bd)
    (n : ℕ) (state : R.machine.State) :
    (fun out => R.returned out.1) <$> R.runPrefix n state = R.machine.unroll n state := by
  induction n generalizing state with
  | zero => cases hview : R.machine.view state <;> simp [runPrefix, unroll, returned, hview]
  | succ n ih =>
      cases hview : R.machine.view state with
      | inl value => simp [runPrefix, unroll, returned, hview]
      | inr query =>
          rcases query with ⟨position, next⟩
          simp only [runPrefix, unroll, hview]
          apply congrArg (FreeM.liftBind position)
          funext direction
          simpa only [FreeM.map_eq_map, Functor.map_map, Function.comp_def] using
            ih (next direction)

/-- Every returned state and transition charge is realized by an actual syntactic prefix. -/
theorem runPrefix_trace (R : QuantitativeRealization Q bd) (n : ℕ)
    (state : R.machine.State) :
    AllOutputs (fun out => ∃ trace : ExecutionTrace R state out.1, trace.cost = out.2)
      (R.runPrefix n state) := by
  induction n generalizing state with
  | zero =>
      rw [runPrefix, allOutputs_pure]
      exact ⟨.nil state, rfl⟩
  | succ n ih =>
      cases hview : R.machine.view state with
      | inl value =>
          rw [runPrefix, hview, allOutputs_pure]
          exact ⟨.nil state, rfl⟩
      | inr query =>
          rcases query with ⟨position, next⟩
          rw [runPrefix, hview, FreeM.allOutputs_liftBind]
          intro direction
          rw [allOutputs_map]
          intro tail htail
          obtain ⟨trace, hcost⟩ := ih (next direction) tail htail
          exact ⟨.query hview direction trace, by
            simp [ExecutionTrace.cost, RankedResource.queryStepCost, hcost]⟩

/-- A prefix uses at most its query budget. If it is unresolved, it consumed that entire budget. -/
theorem runPrefix_queries (R : QuantitativeRealization Q bd) (n : ℕ)
    (state : R.machine.State) :
    AllOutputs (fun out => out.2.queries ≤ n ∧ (R.returned out.1 = none → out.2.queries = n))
      (R.runPrefix n state) := by
  induction n generalizing state with
  | zero => simp [runPrefix, allOutputs_pure]
  | succ n ih =>
      cases hview : R.machine.view state with
      | inl value => simp [runPrefix, hview, allOutputs_pure, returned]
      | inr query =>
          rcases query with ⟨position, next⟩
          rw [runPrefix, hview, FreeM.allOutputs_liftBind]
          intro direction
          rw [allOutputs_map]
          intro tail htail
          obtain ⟨hle, heq⟩ := ih (next direction) tail htail
          change
            (RankedResource.queryStepCost R state position direction + tail.2).queries ≤ n + 1 ∧
            (R.returned tail.1 = none →
              (RankedResource.queryStepCost R state position direction + tail.2).queries = n + 1)
          simp only [RankedResource.queryStepCost, ExecutionCost.queries_add,
            ExecutionCost.queries_ofWork, ExecutionCost.queries_observe,
            ExecutionCost.queries_query, Nat.zero_add]
          exact ⟨by omega, fun h => by rw [heq h]; omega⟩

/-- The recorded complete resource vector is the cost of the witnessing machine trace. -/
theorem observedCost_eq_executionCost (R : QuantitativeRealization Q bd) (input : α)
    (out : R.machine.State × ExecutionCost)
    (trace : ExecutionTrace R (R.machine.init input) out.1) (hcost : trace.cost = out.2) :
    R.observedCost input out = R.executionCost input trace := by
  simp only [observedCost, executionCost, hcost]

end PFunctor.DynSystem.DynComputation.QuantitativeRealization
