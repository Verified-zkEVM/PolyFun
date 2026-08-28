/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Resource
public import PolyFun.PFunctor.Dynamical.DynComputation.Termination
public import PolyFunTest.Realizability.QuantitativeBoundedClosure
public import PolyFunTest.Realizability.QuantitativePolynomial

/-!
# Quantitative resource-contract checks

The componentwise arithmetic canary uses nonzero, distinct values so swapping or dropping a cost
field fails elaboration. The cost-free executable fixture separately checks that response contracts
do not get conflated with semantic implementation witnesses for immediately returning programs.
-/

@[expose] public section

namespace PFunctor.QuantitativeResourceTest

open Complexity
open DynSystem.DynComputation
open QuantitativePolynomialTest

/-! ## Genuinely dependent response sizes -/

/-- A representation is its concrete encoded-size function. -/
def measuredClass : StepClass.{0, 0} where
  Str α := α → ℕ
  Hom _ _ _ := True
  id_mem _ := trivial
  comp_mem _ _ := trivial

/-- A cost-free backend which reads the nonconstant sizes pinned by `measuredClass`. -/
def measuredBackend : QuantitativeStepClass.{0, 0, 0} measuredClass where
  Realizer _ _ _ := PUnit
  size representation value := representation value
  cost _ _ := 0
  admissible _ := trivial

/-- Two positions with genuinely different dependent answer types. -/
def dependentResponse : PFunctor.{0, 0} where
  A := Bool
  B
    | false => Bool
    | true => Fin 3

/-- Nonconstant position encoding used as the modulus argument. -/
def dependentPositionSize : Bool → ℕ
  | false => 2
  | true => 5

/-- Nonconstant dependent response encoding, including the position tag. -/
def dependentIndexSize : dependentResponse.Idx → ℕ
  | ⟨false, false⟩ => 4
  | ⟨false, true⟩ => 7
  | ⟨true, answer⟩ => 10 + answer.val

/-- Pinned interface representations for the dependent response model. -/
def dependentInterface : InterfaceBoundary measuredClass dependentResponse :=
  ⟨dependentPositionSize, dependentIndexSize⟩

/-- Distinct monotone envelopes for the two positions. -/
def dependentModel :
    ResponseResourceModel measuredBackend dependentInterface id where
  allows _ _ := True
  responseSize
    | false => fun size ↦ size + 5
    | true => fun size ↦ 2 * size + 3
  responseSize_monotone
    | false => fun _ _ hle ↦ Nat.add_le_add_right hle 5
    | true => fun _ _ hle ↦ Nat.add_le_add_right (Nat.mul_le_mul_left 2 hle) 3
  responseSize_le
    | false, false, _ => by change 4 ≤ 7; omega
    | false, true, _ => by change 7 ≤ 7; omega
    | true, answer, _ => by
        change 10 + answer.val ≤ 13
        omega

/-- The two dependent answers at the first position have distinguishable encodings. -/
example : measuredBackend.size dependentInterface.idx ⟨false, false⟩ = 4 := rfl
example : measuredBackend.size dependentInterface.idx ⟨false, true⟩ = 7 := rfl

/-- The second position uses a different answer type and a nonconstant three-point encoding. -/
example : measuredBackend.size dependentInterface.idx
    ⟨true, (⟨2, by omega⟩ : Fin 3)⟩ = 12 := rfl

/-- `responseSize_le` is exercised directly at both dependent fibers. -/
example : measuredBackend.size dependentInterface.idx ⟨false, true⟩ ≤
    dependentModel.responseSize false
      (measuredBackend.size dependentInterface.pos false) :=
  dependentModel.responseSize_le false true trivial

example : measuredBackend.size dependentInterface.idx ⟨true, (⟨2, by omega⟩ : Fin 3)⟩ ≤
    dependentModel.responseSize true
      (measuredBackend.size dependentInterface.pos true) :=
  dependentModel.responseSize_le true ⟨2, by omega⟩ trivial

/-- A concrete response-size environment for the empty-response test interface. -/
def emptyModel :
    ResponseResourceModel zeroBackend unitBoundary.interface (fun _ ↦ true) where
  allows _ answer := nomatch answer
  responseSize _ size := size + 1
  responseSize_monotone _ _ _ hle := Nat.add_le_add_right hle 1
  responseSize_le _ answer := nomatch answer

/-- A nonempty contract which accepts every model with the pinned singleton label. -/
def emptyContract : ResponseResourceContract zeroBackend unitBoundary.interface Bool where
  labelOf _ := true
  admissible _ := True
  model_nonempty := ⟨emptyModel, True.intro⟩

/-- The dependent response model is exposed as the intended second-order modulus. -/
example : emptyModel.modulus (.responseSize true) 4 = 5 := by
  simp [emptyModel]

/-- A component-distinguishing polynomial used to guard evaluation and composition. -/
def samplePolynomial : ExecutionCostPolynomial (ResponseModulus Bool) where
  work := .oracle (.responseSize true) (.add .input (.const 1))
  queries := .oracle (.responseSize false) .input
  traffic := .mul .input (.const 3)
  peakStateSize := .const 5
  peakHeadSize := .const 7

/-- A nontrivial monotone length environment for the arithmetic canary. -/
def doubleModulus : ResponseModulus Bool → ℕ → ℕ
  | .responseSize _ => fun size ↦ 2 * size

/-- Evaluation preserves all five fields and applies the response modulus at the nested argument. -/
example : samplePolynomial.eval doubleModulus 3 =
    { work := 8, queries := 6, traffic := 9, peakStateSize := 5, peakHeadSize := 7 } :=
  by
    ext <;> simp [samplePolynomial, doubleModulus]

/-- Input composition changes the argument seen by both ordinary and response-length terms. -/
example : (samplePolynomial.comp (.add .input (.const 2))).eval doubleModulus 3 =
    { work := 12, queries := 10, traffic := 15, peakStateSize := 5, peakHeadSize := 7 } :=
  by
    rw [ExecutionCostPolynomial.eval_comp]
    ext <;> simp [samplePolynomial, doubleModulus]

/-- Substitution replaces the response-length symbol while leaving the other components intact. -/
example :
    (samplePolynomial.subst (target := PEmpty)
      (fun _ ↦ .mul .input (.const 3))).eval PEmpty.elim 2 =
      { work := 9, queries := 6, traffic := 6, peakStateSize := 5, peakHeadSize := 7 } :=
  by
    rw [ExecutionCostPolynomial.eval_subst]
    ext <;> simp [samplePolynomial]

/-- Swap the two response labels rather than merely changing their result type. -/
def swapResponseLabel : ResponseModulus Bool → ResponseModulus Bool
  | .responseSize label => .responseSize (!label)

/-- A modulus which makes the two labels observably different. -/
def splitModulus : ResponseModulus Bool → ℕ → ℕ
  | .responseSize false => fun size ↦ size + 10
  | .responseSize true => fun size ↦ 3 * size

/-- Reindexing swaps both distinct symbols: work moves to `false`, queries move to `true`. -/
example : (samplePolynomial.reindex swapResponseLabel).eval splitModulus 3 =
    { work := 14, queries := 9, traffic := 9, peakStateSize := 5, peakHeadSize := 7 } := by
  rw [ExecutionCostPolynomial.eval_reindex]
  ext <;> simp [samplePolynomial, swapResponseLabel, splitModulus]

/-- Conservative polynomial addition dominates `ExecutionCost`'s additive and peak combination. -/
example : samplePolynomial.eval doubleModulus 3 + samplePolynomial.eval doubleModulus 4 ≤
    (samplePolynomial + samplePolynomial).eval doubleModulus 4 := by
  have hmono : samplePolynomial.eval doubleModulus 3 ≤
      samplePolynomial.eval doubleModulus 4 :=
    ExecutionCostPolynomial.eval_mono_input _ (by
        intro symbol
        cases symbol
        intro left right hle
        exact Nat.mul_le_mul_left 2 hle) (by omega)
  exact (ExecutionCost.add_le_add hmono le_rfl).trans
    (ExecutionCostPolynomial.add_eval_le_eval_add samplePolynomial samplePolynomial
      doubleModulus 4)

/-- Executable data for the pure identity program. -/
def pureCertificate : PureResourceCertificate zeroBackend unitBoundary id :=
  PureResourceCertificate.ofPolyRealizer zeroModel
    (zeroPolyRealizer unitBoundary.input unitBoundary.out id)

/-- Pure executable data yields a syntax-independent run bound under the response contract. -/
example : PolynomialRunBound pureCertificate.realization emptyContract :=
  pureCertificate.runBound emptyContract

/-- Adding semantic implementation produces the corresponding `FreeM.pure` program witness. -/
def pureWitness : PolynomialProgramWitness zeroBackend unitBoundary emptyContract
    (fun input ↦ FreeM.pure (P := emptyResponse) input) :=
  pureCertificate.programWitness emptyContract

/-- The program witness projects to ordinary quantitative realizability. -/
example :=
  pureWitness.isQuantitativelyRealizableBy

/-- Every admitted response model receives the exact input-indexed bound from the same witness. -/
example (model : emptyContract.Model) :=
  pureWitness.isQuantitativelyRealizableWithinUnder model

/-! ## Query-bearing ranked and bind certificates -/

private abbrev queryBackend := QuantitativeBoundedClosureTest.unitCostBackend
private abbrev queryBoundary := QuantitativeBoundedClosureTest.firstQueryBoundary
private abbrev queryFinalRep := QuantitativeBoundedClosureTest.natOutputRep
private abbrev queryFirst := QuantitativeBoundedClosureTest.firstQueryRealization
private abbrev querySecond := QuantitativeBoundedClosureTest.secondQueryRealization

/-- The single concrete response model used by the query-bearing certificate canary. -/
private def queryResponseModel :
    ResponseResourceModel queryBackend queryBoundary.interface (fun _ ↦ false) where
  allows := QuantitativeBoundedClosureTest.allowsBool
  responseSize _ _ := 1
  responseSize_monotone _ _ _ _ := le_rfl
  responseSize_le _ _ _ := le_rfl

/-- Pin the query fixture to one response policy, preventing model variation from hiding a cast. -/
private abbrev queryContract :
    ResponseResourceContract queryBackend queryBoundary.interface Bool where
  labelOf _ := false
  admissible model := model = queryResponseModel
  model_nonempty := ⟨queryResponseModel, rfl⟩

private abbrev queryModel : queryContract.Model := ⟨queryResponseModel, rfl⟩

/-- The existing all-response bound gives ordinary well-founded termination of phase one. -/
private theorem firstTerminates (input : PUnit) :
    queryFirst.machine.TerminatesFrom (queryFirst.machine.init input) := by
  have hAll := QuantitativeBoundedClosureTest.firstQueryRunsWithin.resolvesIn input
  change queryFirst.machine.ResolvesInUnder (fun _ _ ↦ True) 1
    (queryFirst.machine.init input) at hAll
  exact DynSystem.DynComputation.ResolvesIn.terminatesFrom <|
    (queryFirst.machine.resolvesInUnder_all_iff 1 _).mp hAll

/-- The existing all-response bound gives ordinary well-founded termination of phase two. -/
private theorem secondTerminates (input : Bool) :
    querySecond.machine.TerminatesFrom (querySecond.machine.init input) := by
  have hAll := QuantitativeBoundedClosureTest.secondQueryRunsWithin.resolvesIn input
  change querySecond.machine.ResolvesInUnder (fun _ _ ↦ True) 1
    (querySecond.machine.init input) at hAll
  exact DynSystem.DynComputation.ResolvesIn.terminatesFrom <|
    (querySecond.machine.resolvesInUnder_all_iff 1 _).mp hAll

/-- The extracted first-phase program retains the concrete query-bearing machine semantics. -/
private noncomputable def firstProgram :
    PUnit → FreeM QuantitativeBoundedClosureTest.boolResponse Bool :=
  queryFirst.machine.toFreeM firstTerminates

/-- The extracted second-phase program retains the answer-dependent concrete machine semantics. -/
private noncomputable def secondProgram :
    Bool → FreeM QuantitativeBoundedClosureTest.boolResponse Nat :=
  querySecond.machine.toFreeM secondTerminates

private theorem firstImplements : queryFirst.machine.Implements firstProgram :=
  queryFirst.machine.implements_toFreeM firstTerminates

private theorem secondImplements : querySecond.machine.Implements secondProgram :=
  querySecond.machine.implements_toFreeM secondTerminates

/-- Rank one before the query and rank zero after receiving its typed answer. -/
private noncomputable def firstRanked :
    RankedRunCertificate queryFirst QuantitativeBoundedClosureTest.allowsBool where
  rank
    | none => 1
    | some _ => 0
  returns_of_rank_zero
    | none, h => by simp at h
    | some answer, _ => ⟨answer, rfl⟩
  decreases := by
    intro state position next view_eq direction _
    cases state with
    | none =>
        cases position
        cases view_eq
        change 0 < 1
        omega
    | some answer =>
        change Sum.inl answer = Sum.inr _ at view_eq
        contradiction
  progress := by
    intro state position next view_eq
    exact ⟨false, trivial⟩

/-- Remaining positive cost after initialization, separated before and after the query. -/
private def firstPotential : Option Bool → ExecutionCost
  | none => ⟨3, 1, 2, 1, 1⟩
  | some _ => ⟨1, 0, 0, 1, 1⟩

/-- The final readout charges one work unit but no update or query. -/
private example : RankedResource.terminalCost queryFirst (some true) =
    ⟨1, 0, 0, 1, 1⟩ := rfl

/-- A pending transition charges both readout and update work plus typed boundary traffic. -/
private example : RankedResource.queryStepCost queryFirst none PUnit.unit true =
    ⟨2, 1, 2, 1, 1⟩ := rfl

/-- A genuinely query-bearing ranked local-potential producer. -/
private noncomputable def firstPotentialCertificate :
    RankedResource.PotentialCertificate queryFirst
      QuantitativeBoundedClosureTest.allowsBool
      (fun _ ↦ QuantitativeBoundedClosureTest.oneQueryBound) where
  toRankedRunCertificate := firstRanked
  potential := firstPotential
  terminal_le := by
    intro state
    cases state <;>
      simp [RankedResource.terminalCost, firstPotential, queryFirst,
        QuantitativeBoundedClosureTest.firstQueryRealization,
        QuantitativeBoundedClosureTest.unitCostBackend, ExecutionCost.le_iff,
        ExecutionCost.ofWork]
  query_le := by
    intro state position next view_eq direction _
    cases state with
    | none =>
        cases position
        cases view_eq
        change (⟨2, 1, 2, 1, 1⟩ : ExecutionCost) + ⟨1, 0, 0, 1, 1⟩ ≤
          ⟨3, 1, 2, 1, 1⟩
        rw [ExecutionCost.le_iff]
        decide
    | some answer =>
        change Sum.inl answer = Sum.inr _ at view_eq
        contradiction
  init_le := by
    intro input
    cases input
    change ExecutionCost.ofWork 1 + ⟨3, 1, 2, 1, 1⟩ ≤
      QuantitativeBoundedClosureTest.oneQueryBound
    rw [ExecutionCost.le_iff]
    decide
  rank_init_le := by
    intro input
    cases input
    change 1 ≤ QuantitativeBoundedClosureTest.oneQueryBound.queries
    decide

/-- Consuming the local potential yields the same pathwise one-query run bound. -/
private example := firstPotentialCertificate.runsWithinUnder

/-- The ranked producer pins the exact one-query and terminal zero-query boundaries. -/
private example : firstPotentialCertificate.toRankedRunCertificate.rank none = 1 := rfl
private example : firstPotentialCertificate.toRankedRunCertificate.rank (some true) = 0 := rfl

private def firstOutputRecovery : queryBackend.PolyOutputSizeRecovery queryBoundary where
  polynomial := .const 7
  output_le _ := by
    change 1 ≤ 7
    omega

private def oneQueryPolynomial : ExecutionCostPolynomial (ResponseModulus Bool) :=
  .const QuantitativeBoundedClosureTest.oneQueryBound

/-- Ranked evidence packages directly into the standard split program-witness surface. -/
private noncomputable def firstRankedCertificate :
    RankedResourceCertificate queryBackend queryBoundary queryContract firstProgram where
  realization := queryFirst
  implements := firstImplements
  outputRecovery := firstOutputRecovery
  polynomial := oneQueryPolynomial
  resourcePotential := by
    intro model
    rcases model with ⟨model, hmodel⟩
    change model = queryResponseModel at hmodel
    subst model
    simpa [oneQueryPolynomial, queryResponseModel] using firstPotentialCertificate

/-- Forgetting ranked evidence yields a usable semantic witness, not only a run-only package. -/
private example :=
  firstRankedCertificate.programWitness.isQuantitativelyRealizableWithinUnder queryModel

private noncomputable def firstWitness :
    PolynomialProgramWitness queryBackend queryBoundary queryContract firstProgram where
  realization := queryFirst
  implements := firstImplements
  outputRecovery := firstOutputRecovery
  runBound := firstRankedCertificate.runBound

/-- The public bound equation exposes exactly the polynomial evaluation expected downstream. -/
private example (input : PUnit) :
    firstWitness.runBound.bound queryModel input =
      firstWitness.runBound.polynomial.eval queryModel.modulus
        (queryBackend.size queryBoundary.input input) := by
  simp

private def secondRunBound : PolynomialRunBound querySecond queryContract where
  polynomial := oneQueryPolynomial
  runsWithin := by
    intro model
    rcases model with ⟨model, hmodel⟩
    change model = queryResponseModel at hmodel
    subst model
    simpa [oneQueryPolynomial, queryResponseModel] using
      QuantitativeBoundedClosureTest.secondQueryRunsWithin

private theorem secondRunBound_bound (model : queryContract.Model) (input : Bool) :
    secondRunBound.bound model input = QuantitativeBoundedClosureTest.oneQueryBound := by
  rw [PolynomialRunBound.bound_apply]
  simp only [secondRunBound, oneQueryPolynomial, ExecutionCostPolynomial.eval_const]

private def secondOutputRecovery :
    queryBackend.PolyOutputSizeRecovery (queryBoundary.mid queryFinalRep) where
  polynomial := FirstOrderPolynomial.input
  output_le _ := le_rfl

private noncomputable def secondWitness :
    PolynomialProgramWitness queryBackend (queryBoundary.mid queryFinalRep)
      queryContract secondProgram where
  realization := querySecond
  implements := secondImplements
  outputRecovery := secondOutputRecovery
  runBound := secondRunBound

/-- A strict handoff envelope, larger than either concrete one-query second-phase run. -/
private def handoffBound : ExecutionCost := QuantitativeBoundedClosureTest.twoQueryBound

/-- A still larger polynomial envelope, making `bound_le` orientation observable too. -/
private def handoffPolynomialBound : ExecutionCost := ⟨8, 3, 6, 1, 1⟩

private def handoffForModel (model : queryContract.Model) :
    SeqCompHandoffBound queryFirst model.resourceModel.allows
      (secondRunBound.bound model) := by
  exact
    { bound := fun _ ↦ handoffBound
      returned_le := by
        intro input finish trace htrace value view_eq
        rw [secondRunBound_bound]
        rw [ExecutionCost.le_iff]
        decide }

private theorem handoffForModel_bound (model : queryContract.Model) (input : PUnit) :
    (handoffForModel model).bound input = handoffBound := by
  rcases model with ⟨model, hmodel⟩
  change model = queryResponseModel at hmodel
  subst model
  rfl

/-- The handoff envelope is oriented from reached first-phase answers to second-phase bounds. -/
private def polynomialHandoff :
    PolynomialSeqCompHandoffBound queryFirst querySecond queryContract secondRunBound where
  polynomial := .const handoffPolynomialBound
  certificate := handoffForModel
  bound_le := by
    intro model input
    rw [handoffForModel_bound]
    simp only [ExecutionCostPolynomial.eval_const]
    rw [ExecutionCost.le_iff]
    decide

private theorem polynomialHandoff_certificate_bound
    (model : queryContract.Model) (input : PUnit) :
    (polynomialHandoff.certificate model).bound input = handoffBound := by
  change (handoffForModel model).bound input = handoffBound
  exact handoffForModel_bound model input

private theorem polynomialHandoff_eval (model : queryContract.Model) (input : PUnit) :
    polynomialHandoff.polynomial.eval model.modulus
      (queryBackend.size queryBoundary.input input) = handoffPolynomialBound := by
  simp only [polynomialHandoff, ExecutionCostPolynomial.eval_const]

private def seqCompCostForModel (model : queryContract.Model) :
    SeqCompCostCertificate queryFirst querySecond model.resourceModel.allows := by
  rcases model with ⟨model, hmodel⟩
  change model = queryResponseModel at hmodel
  subst model
  exact QuantitativeBoundedClosureTest.querySeqCompCost

private theorem seqCompCostForModel_overhead (model : queryContract.Model) (input : PUnit) :
    (seqCompCostForModel model).overhead input = 0 := by
  rcases model with ⟨model, hmodel⟩
  change model = queryResponseModel at hmodel
  subst model
  rfl

/-- The existing exact source-decomposition certificate supplies zero structural overhead. -/
private def polynomialSeqCompCost :
    PolynomialSeqCompCostCertificate queryFirst querySecond queryContract where
  polynomial := .const 0
  certificate := seqCompCostForModel
  overhead_le := by
    intro model input
    rw [seqCompCostForModel_overhead]
    simp only [ExecutionCostPolynomial.eval_const]
    exact le_rfl

/-- The reached Boolean is fed to the second phase, not bounded in the reverse direction. -/
private example : secondRunBound.bound queryModel true ≤
    (polynomialHandoff.certificate queryModel).bound PUnit.unit := by
  exact (polynomialHandoff.certificate queryModel).returned_le PUnit.unit
    (QuantitativeBoundedClosureTest.firstQueryTrace true)
    (QuantitativeBoundedClosureTest.firstQueryTrace true).conforms_all rfl

/-- Reversing the reached-value handoff inequality is false on the concrete asymmetric bounds. -/
private example : ¬ (polynomialHandoff.certificate queryModel).bound PUnit.unit ≤
    secondRunBound.bound queryModel true := by
  rw [polynomialHandoff_certificate_bound, secondRunBound_bound]
  rw [ExecutionCost.le_iff]
  decide

/-- Reversing the polynomial-envelope inequality is independently false. -/
private example : ¬ polynomialHandoff.polynomial.eval queryModel.modulus
      (queryBackend.size queryBoundary.input PUnit.unit) ≤
    (polynomialHandoff.certificate queryModel).bound PUnit.unit := by
  rw [polynomialHandoff_eval, polynomialHandoff_certificate_bound]
  rw [ExecutionCost.le_iff]
  decide

/-- Two one-query witnesses compose through the program-level `bind` constructor. -/
private noncomputable def compositeWitness :=
  firstWitness.bind secondWitness polynomialHandoff polynomialSeqCompCost

/-- Composition selects the second phase's recovery polynomial, not the distinguishable first. -/
private example : firstWitness.outputRecovery.polynomial.eval 2 = 7 := rfl
private example : secondWitness.outputRecovery.polynomial.eval 2 = 2 := rfl
private example : compositeWitness.outputRecovery.polynomial.eval 2 = 2 := rfl

/-- The composite returned-size theorem charges the final right-phase readout. -/
private example : queryBackend.size (queryBoundary.withOut queryFinalRep).out 4 ≤
    compositeWitness.outputSizePolynomial.eval queryModel.modulus
      (queryBackend.size queryBoundary.input PUnit.unit) := by
  exact compositeWitness.returnedSize_le queryModel PUnit.unit
    (QuantitativeBoundedClosureTest.queryCrossingTrace true false)
    (QuantitativeBoundedClosureTest.queryCrossingTrace true false).conforms_all 4 rfl

/-- The all-response model exposes the `FreeM.bind` syntax through `isTotalRollBound`. -/
private example :=
  compositeWitness.isTotalRollBound queryModel (fun _ _ ↦ trivial) PUnit.unit

end PFunctor.QuantitativeResourceTest
