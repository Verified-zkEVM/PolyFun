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
trivial, so the sampler-blind strong observation `Observation.sampler` obtains the
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
strong path observation over the concrete process model. -/
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

/-- Exact computation equality cannot make both reassociations invisible even
for a deterministic identity-monad scheduler. The transport facts are genuine
semantic obligations, not routine congruence lemmas. -/
example (σ : ULift.{w, 0} Bool) :
    ¬ ((MonadRelFamily.eq Id).rel
        (sourceDraw (m := Id) σ) (leftDraw (m := Id) σ) ∧
      (MonadRelFamily.eq Id).rel
        (sourceDraw (m := Id) σ) (rightDraw (m := Id) σ)) := by
  obtain ⟨b⟩ := σ
  cases b
  · simp only [MonadRelFamily.eq_rel, sourceDraw_id_up_false,
      leftDraw_id_up_false, rightDraw_id_up_false]
    intro h
    have : Leaf.context = Leaf.second := congrArg ULift.down h.1
    contradiction
  · simp only [MonadRelFamily.eq_rel, sourceDraw_id_up_true,
      leftDraw_id_up_true, rightDraw_id_up_true, true_and]
    intro h
    have : Leaf.first = Leaf.second := congrArg ULift.down h
    contradiction

end Interaction.UC.SamplerFactorizationExamples
