/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Instances
public import PolyFun.Realizability.Quantitative.Closure
public import PolyFun.Realizability.Quantitative.Simulation

/-!
# Reference models for resource accounting

These arithmetic models isolate the generic certificate laws. They impose no computability
restriction and therefore do not establish standard polynomial-time realizability. `metered`
records arbitrary local charges; `zero` forgets both cost and size.
-/

public section

universe u v w

namespace PFunctor.QuantitativeStepClass.Reference

/-- Representations explicitly select a natural-number size function. -/
@[expose] def sizes : StepClass.{u, u} where
  Str A := A → ℕ
  Hom _ _ _ := True
  id_mem _ := trivial
  comp_mem _ _ := trivial

/-- Unrestricted functions with an arbitrary charge function as code. -/
@[expose] def metered : QuantitativeStepClass.{u, u, u} sizes where
  Realizer {A} {_B} _ _ _ := A → ℕ
  size rep value := rep value
  cost code value := code value
  admissible _ := trivial

/-- Unrestricted functions with zero sizes and zero work charges. -/
@[expose] def zero : QuantitativeStepClass.{u, v, w} StepClass.unconstrained where
  Realizer _ _ _ := PUnit
  size _ _ := 0
  cost _ _ := 0
  admissible _ := trivial

instance : zero.HasComposition where
  identity _ := PUnit.unit
  compose _ _ := PUnit.unit
  composeOverhead _ _ _ := 0
  cost_compose_le _ _ _ := le_rfl

instance : zero.HasExactComposition where
  cost_compose_eq _ _ _ := rfl

instance : zero.HasProd where
  fst _ _ := PUnit.unit
  snd _ _ := PUnit.unit
  pair _ _ := PUnit.unit

instance : zero.HasSum where
  inl _ _ := PUnit.unit
  inr _ _ := PUnit.unit
  elim _ _ := PUnit.unit

instance : zero.HasOption where
  map _ := PUnit.unit
  none _ _ := PUnit.unit
  bindContext _ := PUnit.unit
  some _ := PUnit.unit

instance : zero.IsDistributive where
  distribute _ _ _ := PUnit.unit

/-- Every backend maps to the arithmetic model while preserving its sizes and local charges. -/
noncomputable def toMetered {C : StepClass.{u, v}} (Q : QuantitativeStepClass.{u, v, w} C) :
    Q.Simulates metered (fun a ↦ Q.size a) where
  code r := Q.cost r
  sizeBound := Polynomial.X
  size_le _ _ := by simp [metered]
  sizeLower := Polynomial.X
  size_ge _ _ := by simp [metered]
  costBound _ := Polynomial.X
  cost_le _ _ := by simp [metered]

end PFunctor.QuantitativeStepClass.Reference
