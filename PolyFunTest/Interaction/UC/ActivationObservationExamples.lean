/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ActivationObservation

/-!
# Activation-observation examples

Regression checks that `Observation.activation` gives the concrete process
model the full `Emulates` composition suite with no assumed instances: the
factorization laws are supplied by the named activation-equivalence theorems
rather than by a hypothesis.

Everything here is structural: emulation at the activation observation says
every closing context sees the same coarse activation structure, and makes no
claim about packets, actions, or sampler effects.
-/

@[expose] public section

universe u v w w'

namespace Interaction.UC.ActivationObservationExamples

variable {Party : Type u} {m : Type w → Type w'}
  {schedulerSampler : m (ULift.{w, 0} Bool)}

/-- The factorization suite is available by instance synthesis alone. -/
example :
    (Observation.activation.{u, v, w, w'}
      Party m schedulerSampler).RespectsFactorization :=
  inferInstance

/-- Parallel composition of activation-level emulations over the concrete
process model, with no assumed observation laws. -/
example {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ₁}
    {real₂ ideal₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ₂}
    (h₁ : Emulates real₁ ideal₁ (Observation.activation Party m schedulerSampler))
    (h₂ : Emulates real₂ ideal₂ (Observation.activation Party m schedulerSampler)) :
    Emulates ((openTheory Party m schedulerSampler).par real₁ real₂)
      ((openTheory Party m schedulerSampler).par ideal₁ ideal₂)
      (Observation.activation Party m schedulerSampler) :=
  Emulates.par_compose h₁ h₂

/-- Wired composition of activation-level emulations. -/
example {Δ₁ Γ Δ₂ : PortBoundary}
    {real₁ ideal₁ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj
      (PortBoundary.tensor Δ₁ Γ)}
    {real₂ ideal₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₁ : Emulates real₁ ideal₁ (Observation.activation Party m schedulerSampler))
    (h₂ : Emulates real₂ ideal₂ (Observation.activation Party m schedulerSampler)) :
    Emulates ((openTheory Party m schedulerSampler).wire real₁ real₂)
      ((openTheory Party m schedulerSampler).wire ideal₁ ideal₂)
      (Observation.activation Party m schedulerSampler) :=
  Emulates.wire_compose h₁ h₂

/-- Closing activation-level emulations against activation-level emulating
environments. -/
example {Δ : PortBoundary}
    {real ideal : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ}
    {K_real K_ideal : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj
      (PortBoundary.swap Δ)}
    (hProt : Emulates real ideal (Observation.activation Party m schedulerSampler))
    (hEnv : Emulates K_real K_ideal (Observation.activation Party m schedulerSampler)) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).close real K_real)
      ((openTheory Party m schedulerSampler).close ideal K_ideal) :=
  (Observation.activation_rel Party m schedulerSampler).mp
    (Emulates.plug_compose hProt hEnv)

/-- The observation's relation is exactly activation equivalence. -/
example
    {c₁ c₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Closed}
    (h : OpenProcessActivationEquiv c₁ c₂) :
    (Observation.activation Party m schedulerSampler).rel c₁ c₂ :=
  (Observation.activation_rel Party m schedulerSampler).mpr h

end Interaction.UC.ActivationObservationExamples
