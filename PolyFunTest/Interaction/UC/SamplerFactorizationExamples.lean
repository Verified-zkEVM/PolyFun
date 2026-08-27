/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.SamplerObservation

/-!
# Sampler-factorization examples

Regression checks for the sampler-aware coherence laws and their observation
bridge.  At `MonadRelFamily.top` every scheduler-transport hypothesis is
trivial, so the packet-aware observation `Observation.sampler` obtains the
full factorization suite — and hence the whole `Emulates` composition suite —
unconditionally.
-/

@[expose] public section

universe u v w w'

namespace Interaction.UC.SamplerFactorizationExamples

open OpenProcessFactorization

variable {Party : Type u} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
  {schedulerSampler : m (ULift.{w, 0} Bool)}

/-- At the forgetful relation family the transport facts are trivial and the
sampler observation respects factorization outright. -/
example :
    (Observation.sampler.{u, v, w, w'} Party m schedulerSampler
      (MonadRelFamily.top m)).RespectsFactorization :=
  Observation.respectsFactorization_sampler Party m schedulerSampler
    (MonadRelFamily.top m) (MonadRelFamily.top_rel _ _)
    (MonadRelFamily.top_rel _ _) (MonadRelFamily.top_rel _ _)

/-- With the factorization laws in hand, the composition suite applies to the
packet-aware observation over the concrete process model. -/
example {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ₁}
    {real₂ ideal₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ₂}
    (h₁ : Emulates real₁ ideal₁
      (Observation.sampler Party m schedulerSampler (MonadRelFamily.top m)))
    (h₂ : Emulates real₂ ideal₂
      (Observation.sampler Party m schedulerSampler (MonadRelFamily.top m))) :
    Emulates ((openTheory Party m schedulerSampler).par real₁ real₂)
      ((openTheory Party m schedulerSampler).par ideal₁ ideal₂)
      (Observation.sampler Party m schedulerSampler (MonadRelFamily.top m)) :=
  letI := Observation.respectsFactorization_sampler Party m schedulerSampler
    (MonadRelFamily.top m) (MonadRelFamily.top_rel _ _)
    (MonadRelFamily.top_rel _ _) (MonadRelFamily.top_rel _ _)
  Emulates.par_compose h₁ h₂

/-- The five sampler-aware coherence laws are pinned at their statements. -/
example {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w, w'} m Party Δ)
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ)) :
    OpenProcessSamplerEquiv (MonadRelFamily.top m)
      ((openTheory Party m schedulerSampler).plug W K)
      ((openTheory Party m schedulerSampler).plug K W) :=
  openTheory_plug_comm_sampler_equiv Party m schedulerSampler
    (MonadRelFamily.top m) (MonadRelFamily.top_rel _ _) W K

/-- Sampler-aware factorization forgets onto the activation-level law. -/
example {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (K : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).par W₁ W₂) K)
      ((openTheory Party m schedulerSampler).plug W₁
        (OpenProcess.mapBoundary
          (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁)).toHom
          ((openTheory Party m schedulerSampler).wire
            (Γ := PortBoundary.swap Δ₂)
            (Δ₂ := PortBoundary.empty)
            K
            (OpenProcess.mapBoundary
              (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm.toHom W₂)))) :=
  (openTheory_plug_par_left_sampler_equiv Party m schedulerSampler
    (MonadRelFamily.top m) (MonadRelFamily.top_rel _ _) W₁ W₂ K).toActivationEquiv

end Interaction.UC.SamplerFactorizationExamples
