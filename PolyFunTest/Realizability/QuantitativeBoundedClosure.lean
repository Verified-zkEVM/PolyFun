/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Instances
public import PolyFun.Realizability.Quantitative.BoundedClosure

/-!
# Bounded quantitative-closure checks

Concrete checks for ranked termination, input precomposition, and result postcomposition. The
fixture backend assigns zero local work and zero representation size solely to exercise structural
trace transport and theorem elaboration. It is not an operational complexity backend and is not
evidence that any function is efficiently realizable. Application-level complexity tests must
instead provide executable code and inequalities over that code's actual cost.
-/

public section

namespace PFunctor.QuantitativeBoundedClosureTest

open DynSystem.DynComputation

/-- Synthetic structural-smoke backend, explicitly excluded from complexity evidence. -/
@[expose]
def zeroBackend : QuantitativeStepClass.{0, 0, 0} StepClass.unconstrained.{0, 0} where
  Realizer _ _ _ := PUnit
  size _ _ := 0
  cost _ _ := 0
  admissible _ := True.intro

instance : zeroBackend.HasCategory where
  identity _ := PUnit.unit
  compose _ _ := PUnit.unit
  composeOverhead _ _ _ := 0
  cost_compose_le _ _ _ := le_rfl

instance : zeroBackend.HasSum where
  inl _ _ := PUnit.unit
  inr _ _ := PUnit.unit
  elim _ _ := PUnit.unit

/-- Interface with one position and no possible answer. -/
abbrev emptyResponse : PFunctor.{0, 0} :=
  PFunctor.mk PUnit.{1} fun _ ↦ PEmpty.{1}

/-- Unconstrained unit boundary for the returning fixture. -/
abbrev unitBoundary : Boundary StepClass.unconstrained.{0, 0} emptyResponse
    PUnit.{1} PUnit.{1} :=
  Boundary.unconstrained emptyResponse PUnit.{1} PUnit.{1}

/-- An explicitly costed realization that returns its unit input immediately. -/
@[expose]
def returnRealization : QuantitativeRealization zeroBackend unitBoundary where
  machine := ofFn (p := emptyResponse) id
  state := PUnit.unit
  initCode := PUnit.unit
  headCode := PUnit.unit
  updateCode := PUnit.unit

/-- Rank zero is sufficient because every state of the fixture has already returned. -/
def returnRanked : RankedRunCertificate returnRealization (fun _ _ ↦ True) where
  rank _ := 0
  returns_of_rank_zero state _ := ⟨state, rfl⟩
  decreases _ direction := nomatch direction
  progress hview := by
    rw [show returnRealization.machine.view _ = Sum.inl PUnit.unit by rfl] at hview
    exact nomatch hview

/-- The all-zero exact bound for the cost-free returning fixture. -/
def zeroBound : PUnit.{1} → ExecutionCost := fun _ ↦ 0

/-- The ranked certificate and exact pathwise accounting close the full restricted run bound. -/
theorem returnRunsWithin :
    returnRealization.RunsWithinUnder (fun _ _ ↦ True) zeroBound := by
  apply returnRanked.runsWithinUnder zeroBound
  · intro input finish trace htrace
    have hview : returnRealization.machine.view
        (returnRealization.machine.init input) = Sum.inl input := by
      rfl
    obtain ⟨hfinish, hcost⟩ := trace.finish_eq_and_cost_eq_zero_of_view_return hview
    change ExecutionCost.ofWork 0 + trace.cost + ExecutionCost.ofWork 0 +
      ExecutionCost.observe 0 0 ≤ 0
    rw [hcost]
    rfl
  · intro input
    simp [returnRanked, zeroBound]

/-- Executable identity code with indices fixed for input precomposition. -/
def unitInputCode : zeroBackend.Realizer unitBoundary.input unitBoundary.input id :=
  PUnit.unit

/-- Precomposition is immediately usable and adds only the backend's certified zero overhead. -/
example :
    (returnRealization.precomp unitInputCode).RunsWithinUnder (fun _ _ ↦ True)
      (fun input ↦
        ExecutionCost.ofWork
            (zeroBackend.cost unitInputCode input +
              zeroBackend.composeOverhead unitInputCode returnRealization.initCode input) +
          zeroBound input) :=
  returnRunsWithin.precomp unitInputCode

/-- Executable identity code with indices fixed for result postcomposition. -/
def unitResultCode : zeroBackend.Realizer unitBoundary.out unitBoundary.out id :=
  PUnit.unit

/-- Zero-overhead result mapping certificate for the cost-free fixture. -/
def returnMapCost : MapResultCostCertificate returnRealization unitResultCode
    (fun _ _ ↦ True) where
  overhead _ := 0
  cost_le := by
    intro input finish trace htrace
    have hview : (returnRealization.mapResult unitResultCode).machine.view
        ((returnRealization.mapResult unitResultCode).machine.init input) = Sum.inl input := by
      rfl
    obtain ⟨hfinish, hcost⟩ := trace.finish_eq_and_cost_eq_zero_of_view_return hview
    have hsourceView : returnRealization.machine.view
        (returnRealization.machine.init input) = Sum.inl input := by
      rfl
    obtain ⟨_, hsourceCost⟩ :=
      QuantitativeRealization.ExecutionTrace.finish_eq_and_cost_eq_zero_of_view_return
        (trace.ofMapResult returnRealization unitResultCode) hsourceView
    change ExecutionCost.ofWork 0 + trace.cost + ExecutionCost.ofWork 0 +
        ExecutionCost.observe 0 0 ≤
      ExecutionCost.ofWork 0 + (trace.ofMapResult returnRealization unitResultCode).cost +
          ExecutionCost.ofWork 0 + ExecutionCost.observe 0 0 + 0
    rw [hcost, hsourceCost]
    rfl

/-- Result postcomposition reuses source termination/progress and the explicit cost certificate. -/
example :
    (returnRealization.mapResult unitResultCode).RunsWithinUnder (fun _ _ ↦ True)
      (fun input ↦ zeroBound input + returnMapCost.overhead input) :=
  returnRunsWithin.mapResult unitResultCode returnMapCost

#check RankedRunCertificate.resolvesInUnder
#check RankedRunCertificate.runsWithinUnder
#check QuantitativeRealization.ExecutionTrace.toPrecomp
#check QuantitativeRealization.ExecutionTrace.ofPrecomp
#check QuantitativeRealization.ExecutionTrace.toMapResult
#check QuantitativeRealization.ExecutionTrace.ofMapResult
#check QuantitativeRealization.RunsWithinUnder.precomp
#check QuantitativeRealization.RunsWithinUnder.mapResult

end PFunctor.QuantitativeBoundedClosureTest
