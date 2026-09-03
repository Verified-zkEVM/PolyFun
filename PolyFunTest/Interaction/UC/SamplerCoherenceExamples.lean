/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ScheduledSamplerFactorization

/-!
# Sampler-coherence examples

Regression checks for the sampler-level coherence shapes and their two
instances: the shared-sampler theory `openTheory`, whose laws are conditional
on scheduler-transport facts, and the mass-aware theory `scheduledOpenTheory`,
whose laws follow from `BinaryScheduler.IsCoherent` alone. At
`MonadRelFamily.top` every hypothesis is trivial, so both sampler observations
respect factorization outright and the whole `Emulates` composition suite
applies. Sampler equivalence is also a congruence for the theory once the
relation family is bind-congruent, which the exact and forgetful families are.
-/

@[expose] public section

universe u v w w'

namespace Interaction.UC.SamplerCoherenceExamples

open OpenProcessFactorization

variable {Party : Type u} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
  {schedulerSampler : m (ULift.{w, 0} Bool)} {scheduler : BinaryScheduler m}

/-- The exact and forgetful relation families are bind-congruent. -/
example : (MonadRelFamily.eq m).IsBindCongr := inferInstance
example : (MonadRelFamily.top m).IsBindCongr := inferInstance

omit [LawfulMonad m] in
/-- Every scheduler is coherent for the forgetful relation family. -/
theorem isCoherent_top : scheduler.IsCoherent (MonadRelFamily.top m) where
  swap _ _ := MonadRelFamily.top_rel _ _
  left _ _ _ := MonadRelFamily.top_rel _ _
  right _ _ _ := MonadRelFamily.top_rel _ _

/-- The mass-aware sampler observation respects factorization at the forgetful
relation family, with no transport hypothesis. -/
example :
    (Observation.scheduledSampler.{u, v, w, w'} Party m scheduler
      (MonadRelFamily.top m)).RespectsFactorization :=
  Observation.respectsFactorization_scheduledSampler Party m scheduler
    (MonadRelFamily.top m) isCoherent_top

/-- The composition suite applies to the mass-aware theory: it is lawful, and
its sampler observation respects factorization under a coherent scheduler. -/
example {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : (scheduledOpenTheory.{u, v, w, w'} Party m scheduler).Obj Δ₁}
    {real₂ ideal₂ : (scheduledOpenTheory.{u, v, w, w'} Party m scheduler).Obj Δ₂}
    (h₁ : Emulates real₁ ideal₁
      (Observation.scheduledSampler Party m scheduler (MonadRelFamily.top m)))
    (h₂ : Emulates real₂ ideal₂
      (Observation.scheduledSampler Party m scheduler (MonadRelFamily.top m))) :
    Emulates ((scheduledOpenTheory Party m scheduler).par real₁ real₂)
      ((scheduledOpenTheory Party m scheduler).par ideal₁ ideal₂)
      (Observation.scheduledSampler Party m scheduler (MonadRelFamily.top m)) :=
  letI := Observation.respectsFactorization_scheduledSampler Party m scheduler
    (MonadRelFamily.top m) isCoherent_top
  Emulates.par_compose h₁ h₂

/-- Sampler equivalence of a component lifts through any closing context: the
congruence laws chain along the structure of the composite. -/
example (R : MonadRelFamily m) [R.IsBindCongr] {Δ₁ Δ₂ : PortBoundary}
    {real ideal : OpenProcess.{u, v, w, w'} m Party Δ₁}
    (W : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)))
    (h : OpenProcessSamplerEquiv R real ideal) :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).par real W) K)
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).par ideal W) K) :=
  openTheory_plug_congr_left_sampler_equiv Party m schedulerSampler R K
    (openTheory_par_congr_left_sampler_equiv Party m schedulerSampler R W h)

/-- At the forgetful relation family the monoidal laws of the shared-sampler
theory hold up to sampler equivalence outright: fairness, the transport fact,
and bind-congruence are all trivial. -/
example {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (W₃ : OpenProcess.{u, v, w, w'} m Party Δ₃) :
    OpenProcessSamplerEquiv (MonadRelFamily.top m)
      (OpenProcess.mapBoundary (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom
        ((openTheory Party m schedulerSampler).par
          ((openTheory Party m schedulerSampler).par W₁ W₂) W₃))
      ((openTheory Party m schedulerSampler).par W₁
        ((openTheory Party m schedulerSampler).par W₂ W₃)) :=
  openTheory_par_assoc_sampler_equiv Party m schedulerSampler (MonadRelFamily.top m)
    (MonadRelFamily.top_rel _ _) (MonadRelFamily.top_rel _ _) W₁ W₂ W₃

example {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂) :
    OpenProcessSamplerEquiv (MonadRelFamily.top m)
      (OpenProcess.mapBoundary (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom
        ((openTheory Party m schedulerSampler).par W₁ W₂))
      ((openTheory Party m schedulerSampler).par W₂ W₁) :=
  openTheory_par_comm_sampler_equiv Party m schedulerSampler (MonadRelFamily.top m)
    (MonadRelFamily.top_rel _ _) W₁ W₂

/-- The shared-sampler plug factorization is the mass-aware one at constant
mass: the hierarchical draws coincide, so the transport facts do. -/
example (σ : m (ULift.{w, 0} Bool)) :
    BinaryScheduler.sourceDraw (fun _ _ => σ) 1 1 1 = sourceDraw σ :=
  BinaryScheduler.sourceDraw_eq_nestedDrawLeft (fun _ _ => σ) 1 1 1

end Interaction.UC.SamplerCoherenceExamples
