/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Instances
public import PolyFun.Realizability.Quantitative

/-!
# Quantitative-realizability regression checks

The empty-response fixture checks that a pending query cannot satisfy even a one-query resource
bound merely because universal branchwise resolution is vacuous over its response type.
-/

public section

namespace PFunctor.QuantitativeTest

open DynSystem.DynComputation

/-- A deliberately cost-free backend used only to isolate structural query accounting. -/
@[expose]
def zeroBackend : QuantitativeStepClass StepClass.unconstrained where
  Realizer _ _ _ := PUnit
  size _ _ := 0
  cost _ _ := 0
  admissible _ := True.intro

/-- Exact categorical wiring data for the cost-free backend. -/
def zeroExactCategory : zeroBackend.ExactCategory where
  identity _ := PUnit.unit
  compose _ _ := PUnit.unit
  composeOverhead _ _ _ := 0
  cost_compose_eq _ _ _ := rfl

instance : zeroBackend.HasCategory := zeroExactCategory.toHasCategory

instance : zeroBackend.HasExactCategory := zeroExactCategory.toHasExactCategory

/-- An interface exposing one query with no possible typed response. -/
abbrev emptyResponse : PFunctor := PFunctor.mk PUnit fun _ ↦ PEmpty

/-- The permanently pending one-query program over `emptyResponse`. -/
def stuckProgram : PUnit → FreeM emptyResponse PUnit := fun _ ↦
  FreeM.liftBind PUnit.unit PEmpty.elim

/-- Quantitative realization of `stuckProgram` under the cost-free test backend. -/
def stuckRealization : QuantitativeRealization zeroBackend
    (Boundary.unconstrained emptyResponse PUnit PUnit) where
  machine := ofFreeM stuckProgram
  state := PUnit.unit
  initCode := PUnit.unit
  headCode := PUnit.unit
  updateCode := PUnit.unit

/-- A resource bound large enough to count the pending query itself. -/
def oneQueryBound : ExecutionCost := ⟨0, 1, 0, 0, 0⟩

/-- A pending empty-response query violates syntactic progress even with one query available. -/
theorem stuckRealization_not_runsWithin_oneQuery :
    ¬stuckRealization.RunsWithin (fun _ ↦ oneQueryBound) := by
  intro h
  have hview :
      (ofFreeM stuckProgram).view ((ofFreeM stuckProgram).init PUnit.unit) =
        Sum.inr ⟨PUnit.unit, PEmpty.elim⟩ := by
    rfl
  have hresponse : Nonempty PEmpty :=
    h.response_nonempty PUnit.unit (.nil _) hview
  obtain ⟨response⟩ := hresponse
  exact response.elim

/-- Disallowing every answer does not make the empty-response query satisfy a restricted bound:
relation-restricted progress rejects the same vacuity. -/
theorem stuckRealization_not_runsWithinUnder_none :
    ¬stuckRealization.RunsWithinUnder (fun _ _ ↦ False) (fun _ ↦ oneQueryBound) := by
  intro h
  have hview :
      (ofFreeM stuckProgram).view ((ofFreeM stuckProgram).init PUnit.unit) =
        Sum.inr ⟨PUnit.unit, PEmpty.elim⟩ := by
    rfl
  have hresponse : ∃ response, False :=
    h.response_exists PUnit.unit (.nil _) (by trivial) hview
  obtain ⟨_, hfalse⟩ := hresponse
  exact hfalse

#check QuantitativeRealization.ExecutionTrace.Conforms
#check ResolvesInUnder
#check QuantitativeRealization.TraceProgressUnder
#check QuantitativeRealization.RunsWithinUnder
#check IsQuantitativelyRealizableWithinUnder

end PFunctor.QuantitativeTest
