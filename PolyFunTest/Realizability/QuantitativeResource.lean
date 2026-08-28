/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Resource
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
  queries := .input
  traffic := .mul .input (.const 3)
  peakStateSize := .const 5
  peakHeadSize := .const 7

/-- A nontrivial monotone length environment for the arithmetic canary. -/
def doubleModulus : ResponseModulus Bool → ℕ → ℕ
  | .responseSize _ => fun size ↦ 2 * size

/-- Evaluation preserves all five fields and applies the response modulus at the nested argument. -/
example : samplePolynomial.eval doubleModulus 3 =
    { work := 8, queries := 3, traffic := 9, peakStateSize := 5, peakHeadSize := 7 } :=
  by
    ext <;> simp [samplePolynomial, doubleModulus]

/-- Input composition changes the argument seen by both ordinary and response-length terms. -/
example : (samplePolynomial.comp (.add .input (.const 2))).eval doubleModulus 3 =
    { work := 12, queries := 5, traffic := 15, peakStateSize := 5, peakHeadSize := 7 } :=
  by
    rw [ExecutionCostPolynomial.eval_comp]
    ext <;> simp [samplePolynomial, doubleModulus]

/-- Substitution replaces the response-length symbol while leaving the other components intact. -/
example :
    (samplePolynomial.subst (target := PEmpty)
      (fun _ ↦ .mul .input (.const 3))).eval PEmpty.elim 2 =
      { work := 9, queries := 2, traffic := 6, peakStateSize := 5, peakHeadSize := 7 } :=
  by
    rw [ExecutionCostPolynomial.eval_subst]
    ext <;> simp [samplePolynomial]

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

end PFunctor.QuantitativeResourceTest
