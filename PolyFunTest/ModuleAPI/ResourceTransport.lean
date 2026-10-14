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

open QuantitativeStepClass in
/-- The size-free reference model cannot simulate the metered model: the lower size comparison
would bound every metered size by one constant, `sizeLower.eval 0`. -/
theorem not_simulatedBy_zero {str} :
    IsEmpty (Reference.metered.{u}.SimulatedBy Reference.zero.{u, v, w} str) := by
  refine ⟨fun S ↦ ?_⟩
  have h := S.size_ge (A := ULift.{u} ℕ) (fun x ↦ x.down) ⟨S.sizeLower.eval 0 + 1⟩
  change S.sizeLower.eval 0 + 1 ≤ S.sizeLower.eval 0 at h
  omega

/-- The arithmetic reference model preserves a polynomial certificate across universes. -/
noncomputable example {C : StepClass.{u, v}} (Q : QuantitativeStepClass.{u, v, w} C)
    {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B} (r : Q.PolyRealizer a b f) :
    QuantitativeStepClass.Reference.metered.PolyRealizer (Q.size a) (Q.size b) f :=
  (QuantitativeStepClass.Reference.toMetered Q).polyRealizer r

/-- Simulations compose through ordinary imports, including with the identity simulation. -/
noncomputable example {C : StepClass.{u, v}} (Q : QuantitativeStepClass.{u, v, w} C) :
    Q.SimulatedBy QuantitativeStepClass.Reference.metered (fun a ↦ Q.size a) :=
  (QuantitativeStepClass.SimulatedBy.id Q).comp (QuantitativeStepClass.Reference.toMetered Q)

end PolyFunTest.ModuleAPI.ResourceTransport
