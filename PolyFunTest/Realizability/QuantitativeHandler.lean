/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Realizability.QuantitativeStrength
public import PolyFun.Realizability.Quantitative.Handler

/-!
# Stateful handler substitution checks

A counting lens forwards each Boolean query unchanged and increments a natural-number counter.

On the constant-cost fixture:
- substitution along the lens is `Handler.Stateful.run` of its handler, and computes the counter;
- the product machine exposes the forwarded query, accepts the matching answer with the counter
  incremented, and rejects a mismatched tag;
- the one-query realization's exact bound transfers to the product machine under the cost laws,
  with the adversary's query count and concrete work;
- when the inner contract allows no answer, the product machine runs within no bound at all, so
  the progress hypothesis of `RunsWithinUnder.wrapState` is necessary.
-/

public section

namespace PFunctor.QuantitativeHandlerTest

open DynSystem.DynComputation QuantitativeBoundedClosureTest QuantitativeStrengthTest

/-- Forward each query unchanged and count the queries answered. -/
def countingLens : StateLens boolResponse boolResponse ℕ where
  pos query := query.1
  answer _ value := value
  update query _ := query.2 + 1

example : countingLens.mapFreeM (FreeM.lift (P := boolResponse) PUnit.unit) 3 =
    FreeM.liftBind PUnit.unit fun answer ↦ FreeM.pure (answer, 4) := rfl

example (program : FreeM boolResponse Bool) (state : ℕ) :
    countingLens.mapFreeM program state = countingLens.toStateful.run program state :=
  countingLens.mapFreeM_eq_run program state

/- The product machine exposes the forwarded query, takes the matching answer to the next state
with the counter incremented, and rejects nothing it can answer. -/
example : (firstQueryMachine.wrapState countingLens).head (none, 3) = Sum.inr PUnit.unit := by
  rw [head_wrapState]
  rfl

example : (firstQueryMachine.wrapState countingLens).update? ((none, 3), ⟨PUnit.unit, true⟩) =
    some (some true, 4) := rfl

/-- Pinned representation of the counter in the unconstrained fixture class. -/
abbrev counterRep : StepClass.unconstrained.{0, 0}.Str ℕ := PUnit.unit

/-- The counting lens carries constant-cost code in the fixture. -/
def countingAdmissible :
    StateLens.QuantitativelyAdmissible (p := boolResponse) (r := boolResponse) unitCostBackend
      firstQueryBoundary counterRep PUnit.unit PUnit.unit countingLens where
  onPos := PUnit.unit
  onPull := PUnit.unit

/-- The product realization of the first query against the counting lens. -/
abbrev countingRealization :
    QuantitativeRealization unitCostBackend
      (firstQueryBoundary.withHandler (r := boolResponse) counterRep PUnit.unit PUnit.unit) :=
  firstQueryRealization.wrapState counterRep PUnit.unit PUnit.unit countingAdmissible

/-- The law-derived handler carry for the one-query bound, with unit handler-state size, unit
per-call handler work and inner traffic `2` per step. -/
abbrev countingCarry (input : PUnit.{1} × ℕ) : Carry :=
  QuantitativeRealization.handlerLawCarry (Q := unitCostBackend) oneQueryBound
    (unitCostBackend.size firstQueryBoundary.input input.1) 1 1 1 2

/-- The one-query realization's exact bound transfers to the product machine. -/
theorem countingRunsWithin :
    countingRealization.RunsWithinUnder allowsBool fun input ↦
      oneQueryBound.handled oneQueryBound.queries (countingCarry input) 2 :=
  firstQueryRunsWithin.wrapState_of_laws (by intros; trivial) (by intros; exact ⟨false, trivial⟩)
    (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 2)
    (by intros; exact le_rfl) (by intros; exact le_rfl) (by intros; exact le_rfl)
    (by intros; exact le_rfl)

/- The handled bound keeps the adversary's single query and has concrete work: twice the source's
four units, `4 · 5` for initialization, two readouts of `1 + 10 · 5`, and one transition of
`1 + 42 · 5`. -/
example : (oneQueryBound.handled oneQueryBound.queries (countingCarry (PUnit.unit, 0)) 2).queries =
    1 := rfl

example : (oneQueryBound.handled oneQueryBound.queries (countingCarry (PUnit.unit, 0)) 2).work =
    341 := rfl

/-- With an inner contract that allows no answer, the product machine runs within no bound at all:
its first query has no allowed answer. -/
theorem not_runsWithinUnder_empty_inner (bound : PUnit.{1} × ℕ → ExecutionCost) :
    ¬ countingRealization.RunsWithinUnder (fun _ _ ↦ False) bound := by
  intro h
  obtain ⟨_, hfalse⟩ := h.traceProgress (PUnit.unit, 0) (.nil _) trivial
    (view_wrapState_of_query firstQueryMachine countingLens (state := (none, 0)) rfl)
  exact hfalse

end PFunctor.QuantitativeHandlerTest
