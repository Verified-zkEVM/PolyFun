/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Instances
public import PolyFun.Realizability.Quantitative.Polynomial

/-!
# Polynomial quantitative-realizability checks

The cost-free fixture builds the complete explicit polynomial model and checks that identity and
composition retain executable code, work bounds, and output-size bounds. Its zero size function
also makes every bidirectional structural encoding-size certificate immediate.
-/

public section

namespace PFunctor.QuantitativePolynomialTest

open Complexity

/-- A cost-free backend used to exercise polynomial certificate composition. -/
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

/-- Every function has a zero-cost, zero-growth certificate in the cost-free fixture. -/
def zeroPolyRealizer {A B : Type} (a : StepClass.unconstrained.Str A)
    (b : StepClass.unconstrained.Str B) (f : A → B) : zeroBackend.PolyRealizer a b f where
  code := PUnit.unit
  work := FirstOrderPolynomial.const 0
  outputSize := FirstOrderPolynomial.const 0
  work_le _ := le_rfl
  outputSize_le _ := le_rfl

/-- Polynomial category certificate for the cost-free fixture. -/
def zeroPolynomialCategory : zeroBackend.PolynomialCategory where
  identityWork _ := FirstOrderPolynomial.const 0
  cost_identity_le _ _ := le_rfl
  composeOverhead _ _ := FirstOrderPolynomial.const 0
  composeOverhead_le _ _ _ := le_rfl

/-- Explicit structural choices for the cost-free fixture. -/
def zeroKernel : zeroBackend.StructuralKernel where
  cProd := inferInstance
  cSum := inferInstance
  cOption := inferInstance
  cDistributive := inferInstance
  qProd := inferInstance
  qSum := inferInstance
  qOption := inferInstance
  qDistributive := inferInstance

/-- Polynomial structural operations and bidirectional size laws for the fixture. -/
def zeroStructural : zeroBackend.PolynomialStructuralClosure zeroKernel where
  fst _ _ := zeroPolyRealizer _ _ Prod.fst
  snd _ _ := zeroPolyRealizer _ _ Prod.snd
  pair _ _ := zeroPolyRealizer _ _ _
  inl _ _ := zeroPolyRealizer _ _ Sum.inl
  inr _ _ := zeroPolyRealizer _ _ Sum.inr
  elim _ _ := zeroPolyRealizer _ _ _
  optionMap _ := zeroPolyRealizer _ _ _
  optionNone _ _ := zeroPolyRealizer _ _ fun _ ↦ none
  optionBindContext _ := zeroPolyRealizer _ _ _
  distribute _ _ _ := zeroPolyRealizer _ _ _
  prodSize _ _ := FirstOrderPolynomial.const 0
  size_prod_le _ _ _ := le_rfl
  prodLeftSize _ _ := FirstOrderPolynomial.const 0
  size_prod_fst_le _ _ _ := le_rfl
  prodRightSize _ _ := FirstOrderPolynomial.const 0
  size_prod_snd_le _ _ _ := le_rfl
  sumLeftSize _ _ := FirstOrderPolynomial.const 0
  size_sum_inl_le _ _ _ := le_rfl
  sumRightSize _ _ := FirstOrderPolynomial.const 0
  size_sum_inr_le _ _ _ := le_rfl
  sumPayloadSize _ _ := FirstOrderPolynomial.const 0
  size_sum_getLeft_le _ _ _ := le_rfl
  size_sum_getRight_le _ _ _ := le_rfl
  optionSomeSize _ := FirstOrderPolynomial.const 0
  size_option_some_le _ _ := le_rfl
  optionPayloadSize _ := FirstOrderPolynomial.const 0
  size_option_get_le _ _ := le_rfl

/-- Complete explicit polynomial model for the cost-free fixture. -/
def zeroModel : zeroBackend.PolynomialModel where
  category := inferInstance
  kernel := zeroKernel
  polynomialCategory := zeroPolynomialCategory
  structural := zeroStructural

/-- The pinned unit representation used by the identity/composition checks. -/
def unitRep : StepClass.unconstrained.Str PUnit := PUnit.unit

/-- Identity is obtained from the explicit model rather than a global polynomial instance. -/
def identityCode : zeroBackend.PolyRealizer unitRep unitRep id :=
  zeroModel.identity unitRep

/-- Composition charges the explicit category model and retains both certificates. -/
def composedIdentity : zeroBackend.PolyRealizer unitRep unitRep (id ∘ id) :=
  zeroModel.comp identityCode identityCode

example (input : PUnit.{1}) :
    zeroBackend.cost composedIdentity.code input ≤
      composedIdentity.work.eval (zeroBackend.size unitRep input) :=
  composedIdentity.work_le input

example (input : PUnit.{1}) :
    zeroBackend.size unitRep ((id ∘ id) input) ≤
      composedIdentity.outputSize.eval (zeroBackend.size unitRep input) :=
  composedIdentity.outputSize_le input

example (polynomial : Polynomial ℕ) (inputSize : ℕ) :
    (FirstOrderPolynomial.ofNatPolynomial polynomial).eval inputSize =
      polynomial.eval inputSize :=
  FirstOrderPolynomial.eval_ofNatPolynomial polynomial inputSize

#check QuantitativeStepClass.PolyRealizer
#check QuantitativeStepClass.PolynomialCategory
#check QuantitativeStepClass.StructuralKernel
#check QuantitativeStepClass.PolynomialStructuralClosure
#check QuantitativeStepClass.PolynomialModel
#check FirstOrderPolynomial.pow
#check FirstOrderPolynomial.ofNatPolynomial
#check FirstOrderPolynomial.eval_ofNatPolynomial

end PFunctor.QuantitativePolynomialTest
