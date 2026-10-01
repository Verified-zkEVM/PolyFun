/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.FamilySimulation
public import PolyFun.Realizability.Quantitative.Reference

/-!
# Resource transport through ordinary imports

Independent universes exercise the public simulation equations. Size collapse is rejected by the
lower comparison required for simulation.
-/

public section

open PFunctor

universe u v w

namespace PolyFunTest.ModuleAPI.ResourceTransport

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
