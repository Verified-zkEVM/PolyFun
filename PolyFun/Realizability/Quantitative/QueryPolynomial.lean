/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Resource
public import PolyFun.Complexity.SecondOrderPolynomial.NatPolynomial

/-!
# Ordinary polynomial bounds on conforming executions

Polynomial response moduli turn second-order run certificates into ordinary bounds on visible
queries and backend work. The resulting bounds apply to every conforming finite prefix.
-/

public section

universe u v w x

namespace PFunctor.DynSystem.DynComputation.PolynomialRunBound

open PFunctor Complexity

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq p.A] {Q : QuantitativeStepClass.{u, v, w} C} {label : Type x}
  {input output : Type u} {bd : Boundary C p input output}
  {R : QuantitativeRealization Q bd} {contract : ResponseResourceContract Q bd.interface label}

/-- **Query polynomial.** Against a model with polynomially bounded response moduli, the number of
visible queries is bounded by an ordinary polynomial in the encoded input size. -/
theorem exists_natPolynomial_queries (certificate : PolynomialRunBound R contract)
    (model : contract.Model) (bounds : ResponseModulus label → Polynomial ℕ)
    (hbounds : ∀ i m, model.modulus i m ≤ (bounds i).eval m) :
    ∃ q : Polynomial ℕ, ∀ value,
      (certificate.bound model value).queries ≤ q.eval (Q.size bd.input value) :=
  ⟨certificate.polynomial.queries.toNatPolynomial bounds, fun value ↦ by
    rw [PolynomialRunBound.bound_apply, ExecutionCostPolynomial.eval_queries]
    exact SecondOrderPolynomial.eval_le_toNatPolynomial bounds model.modulus hbounds _ _⟩

/-- The same for backend work. -/
theorem exists_natPolynomial_work (certificate : PolynomialRunBound R contract)
    (model : contract.Model) (bounds : ResponseModulus label → Polynomial ℕ)
    (hbounds : ∀ i m, model.modulus i m ≤ (bounds i).eval m) :
    ∃ q : Polynomial ℕ, ∀ value,
      (certificate.bound model value).work ≤ q.eval (Q.size bd.input value) :=
  ⟨certificate.polynomial.work.toNatPolynomial bounds, fun value ↦ by
    rw [PolynomialRunBound.bound_apply, ExecutionCostPolynomial.eval_work]
    exact SecondOrderPolynomial.eval_le_toNatPolynomial bounds model.modulus hbounds _ _⟩

/-- One ordinary polynomial bounds the length of every conforming execution prefix. -/
theorem exists_natPolynomial_traceLength (certificate : PolynomialRunBound R contract)
    (model : contract.Model) (bounds : ResponseModulus label → Polynomial ℕ)
    (hbounds : ∀ i m, model.modulus i m ≤ (bounds i).eval m) :
    ∃ q : Polynomial ℕ, ∀ value {finish : R.machine.State}
      (trace : R.ExecutionTrace (R.machine.init value) finish),
      trace.Conforms model.resourceModel.allows →
        trace.length ≤ q.eval (Q.size bd.input value) := by
  obtain ⟨q, hq⟩ := certificate.exists_natPolynomial_queries model bounds hbounds
  exact ⟨q, fun value _ trace htrace ↦
    ((certificate.runsWithin_bound model).traceLength_le value trace htrace).trans (hq value)⟩

/-- One ordinary polynomial bounds the work of every conforming execution prefix. -/
theorem exists_natPolynomial_executionWork (certificate : PolynomialRunBound R contract)
    (model : contract.Model) (bounds : ResponseModulus label → Polynomial ℕ)
    (hbounds : ∀ i m, model.modulus i m ≤ (bounds i).eval m) :
    ∃ q : Polynomial ℕ, ∀ value {finish : R.machine.State}
      (trace : R.ExecutionTrace (R.machine.init value) finish),
      trace.Conforms model.resourceModel.allows →
        (R.executionCost value trace).work ≤ q.eval (Q.size bd.input value) := by
  obtain ⟨q, hq⟩ := certificate.exists_natPolynomial_work model bounds hbounds
  exact ⟨q, fun value _ trace htrace ↦
    ((certificate.runsWithin_bound model).cost_le value trace htrace).1.trans (hq value)⟩

end PFunctor.DynSystem.DynComputation.PolynomialRunBound
