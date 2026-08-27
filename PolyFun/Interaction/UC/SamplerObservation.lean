/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.OpenProcessSamplerFactorization

/-!
# Sampler-invariant observations respect factorization

The bridge from the sampler-aware coherence laws to the UC composition
theorems: any observation on closed open processes that cannot distinguish
sampler-equivalent systems satisfies `Observation.RespectsPlugComm` and
`Observation.RespectsFactorization`, given the three scheduler-transport
facts for its relation family.

This discharges the structural half of the instantiation gates in
`docs/wiki/uc.md` once and for all: a downstream distributional observation
supplies (a) its relation family `R` on `m`-computations — typically equality
of denotations — with the `MonadRelFamily` laws, (b) the three transport
facts about reassociated scheduler draws, and (c) the invariance of its
observation under `OpenProcessSamplerEquiv` — the downstream adequacy
theorem.  Everything else is supplied here.

`Observation.sampler` packages sampler equivalence itself as the canonical
such observation; it retains packet identity and sampler effects up to `R`,
and is still not a *security* observation — it compares single steps, not
distributions over executions.
-/

public section

universe u v w w'

namespace Interaction
namespace UC

open OpenProcessFactorization

variable (Party : Type u) (m : Type w → Type w')
  (schedulerSampler : m (ULift.{w, 0} Bool))

/-- Any observation invariant under sampler equivalence at `R` respects plug
commutation and plug/wire factorization, given the scheduler-transport facts
for `R`.  The five fields are exactly the five sampler-aware coherence
theorems composed with the invariance. -/
theorem Observation.respectsFactorization_of_samplerInvariant
    [Monad m] [LawfulMonad m] (R : MonadRelFamily m)
    {Obs : Observation (openTheory.{u, v, w, w'} Party m schedulerSampler)}
    (hfair : R.rel schedulerSampler (schedulerFlip <$> schedulerSampler))
    (hleft : R.rel (sourceDraw schedulerSampler) (leftDraw schedulerSampler))
    (hright : R.rel (sourceDraw schedulerSampler)
      (rightDraw schedulerSampler))
    (hInv : ∀ {c₁ c₂ : (openTheory.{u, v, w, w'} Party m
        schedulerSampler).Closed},
      OpenProcessSamplerEquiv R c₁ c₂ → Obs.rel c₁ c₂) :
    Obs.RespectsFactorization where
  plug_comm W K := hInv
    (openTheory_plug_comm_sampler_equiv Party m schedulerSampler R hfair W K)
  close_par_left W₁ W₂ K := hInv
    (openTheory_plug_par_left_sampler_equiv Party m schedulerSampler R hleft
      W₁ W₂ K)
  close_par_right W₁ W₂ K := hInv
    (openTheory_plug_par_right_sampler_equiv Party m schedulerSampler R hright
      W₁ W₂ K)
  close_wire_left W₁ W₂ K := hInv
    (openTheory_plug_wire_left_sampler_equiv Party m schedulerSampler R hleft
      W₁ W₂ K)
  close_wire_right W₁ W₂ K := hInv
    (openTheory_plug_wire_right_sampler_equiv Party m schedulerSampler R
      hright W₁ W₂ K)

/-- Sampler equivalence as an observation on the concrete open-process
theory: the canonical packet- and sampler-aware structural observation. -/
def Observation.sampler [Monad m] [LawfulMonad m] (R : MonadRelFamily m) :
    Observation (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  rel := OpenProcessSamplerEquiv R
  equiv :=
    ⟨fun p => OpenProcessSamplerEquiv.refl p,
      OpenProcessSamplerEquiv.symm,
      OpenProcessSamplerEquiv.trans⟩

@[simp]
theorem Observation.sampler_rel [Monad m] [LawfulMonad m]
    (R : MonadRelFamily m)
    {c₁ c₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Closed} :
    (Observation.sampler Party m schedulerSampler R).rel c₁ c₂ ↔
      OpenProcessSamplerEquiv R c₁ c₂ :=
  Iff.rfl

/-- The sampler observation respects plug commutation and factorization,
given the scheduler-transport facts for its relation family.  A theorem
rather than an instance: the transport facts are genuine hypotheses. -/
theorem Observation.respectsFactorization_sampler
    [Monad m] [LawfulMonad m] (R : MonadRelFamily m)
    (hfair : R.rel schedulerSampler (schedulerFlip <$> schedulerSampler))
    (hleft : R.rel (sourceDraw schedulerSampler) (leftDraw schedulerSampler))
    (hright : R.rel (sourceDraw schedulerSampler)
      (rightDraw schedulerSampler)) :
    (Observation.sampler.{u, v, w, w'}
      Party m schedulerSampler R).RespectsFactorization :=
  Observation.respectsFactorization_of_samplerInvariant Party m
    schedulerSampler R hfair hleft hright fun h => h

end UC
end Interaction
