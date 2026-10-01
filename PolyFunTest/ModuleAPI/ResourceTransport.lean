/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.QueryPolynomial
public import PolyFun.Realizability.Quantitative.Erasure
public import PolyFun.Realizability.Quantitative.FamilySimulation
public import PolyFun.Realizability.Quantitative.Reference

/-!
# Resource transport through ordinary imports

Nested response lengths, independent universes, and restoration of recosted traces exercise the
public equations. Size collapse is rejected by the lower comparison required for simulation.
-/

public section

open PFunctor PFunctor.DynSystem.DynComputation Complexity

universe u v w x

namespace PolyFunTest.ModuleAPI.ResourceTransport

/-- An adaptive second query uses the length of the first response. -/
example (k : ℕ) :
    ((SecondOrderPolynomial.oracle () (.oracle () .input)).toNatPolynomial
      (fun _ ↦ Polynomial.X + 1)).eval k = k + 2 := by
  simp

/-- The source modulus can be nonmonotone; only its polynomial upper bound is used. -/
example (q : SecondOrderPolynomial Unit) (k : ℕ) :
    q.eval (fun _ n ↦ if n = 0 then 2 else 0) k ≤
      (q.toNatPolynomial (fun _ ↦ Polynomial.C 2)).eval k := by
  apply SecondOrderPolynomial.eval_le_toNatPolynomial
  intro i n
  split <;> simp

variable {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{u, v, w} C} {p : PFunctor.{u, u}} [DecidableEq p.A]
  {α β : Type u} {bd : Boundary C p α β} (R : QuantitativeRealization Q bd)
  (cost' : ∀ (A B : Type u) (a : C.Str A) (b : C.Str B) (f : A → B),
    Q.Realizer a b f → A → ℕ)

example {start finish : R.machine.State} (t : (R.recost cost').ExecutionTrace start finish) :
    (t.restore (R := R)).recost (cost' := cost') = t :=
  QuantitativeRealization.ExecutionTrace.recost_restore t

example {allows : ∀ a, p.B a → Prop} {bound : α → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) :
    (R.recost (fun _ _ _ _ _ _ _ ↦ 0)).RunsWithinUnder allows bound :=
  R.runsWithinUnder_recost h (fun _ _ _ _ _ _ _ ↦ Nat.zero_le _)

example {label : Type x} {contract : ResponseResourceContract Q bd.interface label}
    (h : PolynomialRunBound R contract) (model : contract.Model)
    (bounds : ResponseModulus label → Polynomial ℕ)
    (hb : ∀ i n, model.modulus i n ≤ (bounds i).eval n) :
    ∃ q : Polynomial ℕ, ∀ value {finish : R.machine.State}
      (t : R.ExecutionTrace (R.machine.init value) finish),
      t.Conforms model.resourceModel.allows → t.length ≤ q.eval (Q.size bd.input value) :=
  h.exists_natPolynomial_traceLength model bounds hb

/-- Erasing arbitrary input sizes cannot satisfy the simulation's lower size comparison. -/
example (q : Polynomial ℕ) : ¬∀ n : ℕ, n ≤ q.eval 0 := by
  intro h
  have := h (q.eval 0 + 1)
  omega

/-- The arithmetic reference model preserves a polynomial certificate across universes. -/
noncomputable example {C : StepClass.{u, v}} (Q : QuantitativeStepClass.{u, v, w} C)
    {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B} (r : Q.PolyRealizer a b f) :
    QuantitativeStepClass.Reference.metered.PolyRealizer (Q.size a) (Q.size b) f :=
  (QuantitativeStepClass.Reference.toMetered Q).polyRealizer r

end PolyFunTest.ModuleAPI.ResourceTransport
