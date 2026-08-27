/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Instances
public import PolyFun.Realizability.Quantitative.Closure

/-!
# Quantitative-realizability closure checks

Compile-time checks for executable structural mixins and the unbounded quantitative realization
constructors. The fixture charges zero backend work so that these tests exercise only the typing
and semantic wiring of the generic layer.
-/

public section

namespace PFunctor.QuantitativeClosureTest

open DynSystem.DynComputation

/-- A cost-free backend used only as a structural compile-time fixture. -/
@[expose]
def zeroBackend : QuantitativeStepClass StepClass.unconstrained where
  Realizer _ _ _ := PUnit
  size _ _ := 0
  cost _ _ := 0
  admissible _ := True.intro

instance : zeroBackend.HasCategory where
  identity _ := PUnit.unit
  compose _ _ := PUnit.unit
  composeOverhead _ _ _ := 0
  cost_compose_le _ _ _ := le_rfl

instance : zeroBackend.HasExactCategory where
  cost_compose_eq _ _ _ := rfl

instance : zeroBackend.HasProd where
  fst _ _ := PUnit.unit
  snd _ _ := PUnit.unit
  pair _ _ := PUnit.unit

instance : zeroBackend.HasSum where
  inl _ _ := PUnit.unit
  inr _ _ := PUnit.unit
  elim _ _ := PUnit.unit

instance : zeroBackend.HasOption where
  map _ := PUnit.unit
  none _ _ := PUnit.unit
  bindContext _ := PUnit.unit

instance : zeroBackend.IsDistributive where
  distribute _ _ _ := PUnit.unit

/-- A query interface with one position and no possible response. -/
abbrev emptyResponse : PFunctor := PFunctor.mk PUnit fun _ ↦ PEmpty

/-- The unconstrained boundary used by the immediate and sequential-return checks. -/
abbrev unitBoundary : Boundary StepClass.unconstrained emptyResponse PUnit PUnit :=
  Boundary.unconstrained emptyResponse PUnit PUnit

/-- Executable quantitative realization of the identity return program. -/
theorem identityReturn : IsQuantitativelyRealizableBy zeroBackend unitBoundary
    (fun input ↦ FreeM.pure input) :=
  isQuantitativelyRealizableBy_ofFn PUnit.unit

example : IsQuantitativelyRealizableBy zeroBackend
    (unitBoundary.withInput PUnit.unit) ((fun input ↦ FreeM.pure input) ∘ id) :=
  identityReturn.precomp PUnit.unit

example : IsQuantitativelyRealizableBy zeroBackend
    (unitBoundary.withOut PUnit.unit)
    (fun input ↦ FreeM.map id (FreeM.pure input)) :=
  identityReturn.mapResult PUnit.unit

example : IsQuantitativelyRealizableBy zeroBackend
    (unitBoundary.withOut PUnit.unit)
    (fun input ↦ FreeM.bind (FreeM.pure input) (fun value ↦ FreeM.pure value)) := by
  have second : IsQuantitativelyRealizableBy zeroBackend
      (unitBoundary.mid PUnit.unit) (fun value ↦ FreeM.pure value) :=
    isQuantitativelyRealizableBy_ofFn PUnit.unit
  exact identityReturn.seqComp second

/-! The lens regression uses a genuinely nonidentity position map. Besides checking that the
executable evidence packages, the two reductions below pin the security-relevant tag check in
`pullHeadIdx`: a matching answer is pulled back and a mismatched exposed position is rejected. -/

/-- Two-position source interface for the lens canary. -/
abbrev sourceInterface : PFunctor := PFunctor.mk Bool fun _ ↦ Bool

/-- Natural-number-position target interface for the lens canary. -/
abbrev targetInterface : PFunctor := PFunctor.mk Nat fun _ ↦ Bool

/-- Relabel the two source positions as `0` and `1`. -/
def relabelLens : Lens sourceInterface targetInterface where
  toFunA value := if value then 1 else 0
  toFunB _ direction := direction

/-- Boundary for the nonidentity interface-transport canary. -/
abbrev sourceBoundary : Boundary StepClass.unconstrained sourceInterface PUnit PUnit :=
  Boundary.unconstrained sourceInterface PUnit PUnit

/-- The cost-free backend carries executable evidence for both lens maps. -/
def relabelLensAdmissible :
    relabelLens.QuantitativelyAdmissible zeroBackend sourceBoundary PUnit.unit PUnit.unit where
  onPos := PUnit.unit
  onPull := PUnit.unit

example : relabelLens.pullHeadIdx PUnit
    (Sum.inr true, ⟨1, true⟩) = some ⟨true, true⟩ := by
  rfl

example : relabelLens.pullHeadIdx PUnit
    (Sum.inr true, ⟨0, true⟩) = none := by
  rfl

/-- Immediate return over the source interface, used to execute `wrap`. -/
def sourceReturn : QuantitativeRealization zeroBackend sourceBoundary :=
  QuantitativeRealization.ofFn (f := id) PUnit.unit

/-- The executable transport is accepted with the nonidentity lens evidence. -/
def wrappedReturn : QuantitativeRealization zeroBackend
    (sourceBoundary.withInterface (q := targetInterface) PUnit.unit PUnit.unit) :=
  sourceReturn.wrap PUnit.unit PUnit.unit relabelLensAdmissible

example : zeroBackend.cost wrappedReturn.initCode PUnit.unit = 0 := rfl

example : zeroBackend.cost wrappedReturn.headCode PUnit.unit = 0 := rfl

#check QuantitativeStepClass.HasProd.pairRight
#check QuantitativeStepClass.HasSum.map
#check QuantitativeStepClass.IsDistributive.elimContext
#check Lens.QuantitativelyAdmissible
#check Lens.QuantitativelyAdmissible.toIsAdmissible
#check QuantitativeRealization.seqComp
#check QuantitativeRealization.wrap
#check QuantitativeRealization.ExecutionTrace.queryCount_le_length
#check QuantitativeRealization.ExecutionTrace.interfaceTraffic_le_traffic_cost
#check QuantitativeRealization.RunsWithin.queryCount_le
#check QuantitativeRealization.RunsWithin.interfaceTraffic_le
#check QuantitativeRealization.RunsWithin.traceProgress
#check QuantitativeRealization.RunsWithin.response_nonempty

end PFunctor.QuantitativeClosureTest
