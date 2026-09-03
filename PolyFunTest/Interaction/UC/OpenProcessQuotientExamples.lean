/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.OpenProcessQuotient

/-!
# Process-model quotient examples

Regression checks for the quotients of the process models. The activation
quotient of `openTheory` is a strict compact-closed theory with plug-wire
factorization, so the composition suite runs on it at plain equality and
transfers back to activation equivalence on the model; the sampler quotients
satisfy plug factorization under the transport facts, trivially at the
forgetful relation family.
-/

@[expose] public section

universe u v w w'

namespace Interaction.UC.OpenProcessQuotientExamples

open OpenTheory

variable {Party : Type u} {m : Type w → Type w'} {schedulerSampler : m (ULift.{w, 0} Bool)}

/-- The activation quotient is strictly compact closed with plug-wire
factorization, hence has plug factorization and every observation on it
respects factorization. -/
example :
    HasPlugWireFactor
      ((openTheory.{u, v, w, w'} Party m schedulerSampler).quotient
        (openTheory.activationCongruence Party m schedulerSampler)) :=
  inferInstance

example :
    HasPlugFactorization
      ((openTheory.{u, v, w, w'} Party m schedulerSampler).quotient
        (openTheory.activationCongruence Party m schedulerSampler)) :=
  inferInstance

/-- Plug composition on the activation quotient at plain equality recovers the
activation-level composition on the model: emulation of classes is emulation
of representatives at the activation observation. -/
example {Δ : PortBoundary}
    {real ideal : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ}
    {K_real K_ideal : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj
      (PortBoundary.swap Δ)}
    (hProt : Emulates real ideal (Observation.activation Party m schedulerSampler))
    (hEnv : Emulates K_real K_ideal (Observation.activation Party m schedulerSampler)) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).close real K_real)
      ((openTheory Party m schedulerSampler).close ideal K_ideal) := by
  let E := openTheory.activationCongruence Party m schedulerSampler
  have toQuot : ∀ {Δ : PortBoundary}
      {W W' : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ},
      Emulates W W' (Observation.activation Party m schedulerSampler) →
        Emulates (E.cls W) (E.cls W') (Observation.eq _) := fun h =>
    (Emulates.quotient_iff E).mpr ⟨fun K =>
      (Observation.activation_rel_iff_comap Party m schedulerSampler).mp (h.compare K)⟩
  have hQuot := Emulates.plug_compose (toQuot hProt) (toQuot hEnv)
  exact (E.cls_eq_cls (W := (openTheory Party m schedulerSampler).close real K_real)
    (W' := (openTheory Party m schedulerSampler).close ideal K_ideal)).mp
    (Observation.eq_rel.mp hQuot)

/-- At the forgetful relation family the sampler quotient of the process model
has plug factorization with no transport hypothesis. -/
example [Monad m] [LawfulMonad m] :
    HasPlugFactorization
      ((openTheory.{u, v, w, w'} Party m schedulerSampler).quotient
        (openTheory.samplerCongruence Party m schedulerSampler (MonadRelFamily.top m))) :=
  openTheory.hasPlugFactorization_quotient_samplerCongruence Party m schedulerSampler
    (MonadRelFamily.top m) (MonadRelFamily.top_rel _ _) (MonadRelFamily.top_rel _ _)
    (MonadRelFamily.top_rel _ _)

/-- The sampler observation respects factorization, derived through the
quotient rather than field by field. -/
example [Monad m] [LawfulMonad m] :
    (Observation.sampler.{u, v, w, w'} Party m schedulerSampler
      (MonadRelFamily.top m)).RespectsFactorization :=
  Observation.respectsFactorization_sampler_of_quotient Party m schedulerSampler
    (MonadRelFamily.top m) (MonadRelFamily.top_rel _ _) (MonadRelFamily.top_rel _ _)
    (MonadRelFamily.top_rel _ _)

/-- The mass-aware sampler quotient has plug factorization under any coherent
scheduler, in particular every scheduler at the forgetful family. -/
example [Monad m] [LawfulMonad m] (scheduler : BinaryScheduler m) :
    HasPlugFactorization
      ((scheduledOpenTheory.{u, v, w, w'} Party m scheduler).quotient
        (scheduledOpenTheory.samplerCongruence Party m scheduler (MonadRelFamily.top m))) :=
  scheduledOpenTheory.hasPlugFactorization_quotient_samplerCongruence Party m scheduler
    (MonadRelFamily.top m)
    ⟨fun _ _ => MonadRelFamily.top_rel _ _, fun _ _ _ => MonadRelFamily.top_rel _ _,
      fun _ _ _ => MonadRelFamily.top_rel _ _⟩

/-- Two scheduled processes are congruent only when their masses agree: the
congruence records both. -/
example [Monad m] [LawfulMonad m] (scheduler : BinaryScheduler m) {Δ : PortBoundary}
    (W W' : ScheduledOpenProcess.{u, v, w, w'} m Party Δ) :
    (scheduledOpenTheory.samplerCongruence Party m scheduler (MonadRelFamily.top m)).rel W W' ↔
      W.mass = W'.mass ∧ OpenProcessSamplerEquiv (MonadRelFamily.top m) W.process W'.process :=
  scheduledOpenTheory.samplerCongruence_rel Party m scheduler (MonadRelFamily.top m)

end Interaction.UC.OpenProcessQuotientExamples
