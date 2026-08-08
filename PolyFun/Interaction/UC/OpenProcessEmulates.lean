/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.OpenProcess
import all PolyFun.Interaction.UC.OpenTheory
import all PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.OpenProcessFactorization

/-!
# Observations on the process model that ignore scheduling

`Emulates`' composition theorems take their structural input from the
observation, through `Observation.RespectsPlugComm` and
`Observation.RespectsFactorization`. This file supplies both for the
process-backed `openTheory`, which cannot supply the strict
`OpenTheory.HasPlugWireFactor` structure: every binary composition prepends a
scheduler node, so regrouping one is a delay bisimulation rather than an
identity.

## The shape of the bridge

`OpenProcessActivationEquiv` is *not* promoted to an observation here, and
must not be. It labels a step only by whether some party was activated,
discarding packet identity and `stepSampler` effects, so a security statement
made against it would say almost nothing. Its role is the opposite one: it is
an upper bound on how fine a scheduling-insensitive observation may be.

`Observation.IsSchedulingInsensitive` records that bound — an observation
satisfies it when activation-equivalent closed systems are already related.
A concrete security observation (packet-aware, sampler-aware, supplied
downstream where probability lives) is expected to satisfy it because the
scheduler nodes introduced by composition are internal, hence never activated,
and so should be invisible to any reasonable notion of what a network does.

Given that bound, the four factorization laws proved in
`OpenProcessFactorization.lean` transport onto `Obs`, and the process model
earns the whole UC composition suite: `Emulates.par_compose`,
`wire_compose`, `plug_compose`, and their one-sided variants.

## Main definitions

* `Observation.IsSchedulingInsensitive Obs`: activation-equivalent closed
  processes are `Obs`-related.
* `respectsPlugComm_of_isSchedulingInsensitive` and
  `respectsFactorization_of_isSchedulingInsensitive`: the resulting instances.
-/

public section

universe u v w w'

namespace Interaction
namespace UC

variable {Party : Type u} {m : Type w → Type w'} {schedulerSampler : m (ULift.{w, 0} Bool)}

/--
`Obs.IsSchedulingInsensitive` states that the observation `Obs` cannot
distinguish closed processes that differ only in activation-preserving
scheduling structure.

This is a *bound* on an observation, never a definition of one:
`OpenProcessActivationEquiv` retains no packet or action identity and ignores
`stepSampler`, so it is far too coarse to serve as a security observation on
its own. What the class says is that whatever `Obs` does measure, it does not
measure the internal scheduler nodes that `par`, `wire`, and `plug` introduce
— which is exactly the licence needed to transport the model's coherence laws
from activation equivalence to `Obs`.
-/
class Observation.IsSchedulingInsensitive
    (Obs : Observation (openTheory.{u, v, w, w'} Party m schedulerSampler)) : Prop where
  /-- Activation-equivalent closed processes are related by `Obs`. -/
  rel_of_activationEquiv :
    ∀ {p q : (openTheory.{u, v, w, w'} Party m schedulerSampler).Closed},
      OpenProcessActivationEquiv p q → Obs.rel p q

/--
A scheduling-insensitive observation on the process model respects plug
commutation, because `openTheory_plug_comm_activation_equiv` already provides
the law up to activation equivalence.

This is what makes `Emulates.plug_right` and `Emulates.plug_compose`
applicable to `openTheory`.
-/
instance respectsPlugComm_of_isSchedulingInsensitive
    (Obs : Observation (openTheory.{u, v, w, w'} Party m schedulerSampler))
    [Observation.IsSchedulingInsensitive Obs] : Obs.RespectsPlugComm where
  plug_comm W K :=
    Observation.IsSchedulingInsensitive.rel_of_activationEquiv
      (openTheory_plug_comm_activation_equiv Party m schedulerSampler W K)

/--
A scheduling-insensitive observation on the process model respects the whole
plug/wire factorization, transporting the four laws of
`OpenProcessFactorization.lean` along the bound.

With this instance the process model satisfies the same interface as the free
syntax models, so `Emulates.par_compose`, `Emulates.wire_compose`, and their
one-sided variants apply to it — despite `openTheory` having no
`OpenTheory.HasPlugWireFactor` instance, and indeed no `HasUnit` or
`HasIdWire` instance either.
-/
instance respectsFactorization_of_isSchedulingInsensitive
    (Obs : Observation (openTheory.{u, v, w, w'} Party m schedulerSampler))
    [Observation.IsSchedulingInsensitive Obs] : Obs.RespectsFactorization where
  __ := respectsPlugComm_of_isSchedulingInsensitive Obs
  close_par_left W₁ W₂ K :=
    Observation.IsSchedulingInsensitive.rel_of_activationEquiv
      (openTheory_plug_par_left_activation_equiv Party m schedulerSampler W₁ W₂ K)
  close_par_right W₁ W₂ K :=
    Observation.IsSchedulingInsensitive.rel_of_activationEquiv
      (openTheory_plug_par_right_activation_equiv Party m schedulerSampler W₁ W₂ K)
  close_wire_left W₁ W₂ K :=
    Observation.IsSchedulingInsensitive.rel_of_activationEquiv
      (openTheory_plug_wire_left_activation_equiv Party m schedulerSampler W₁ W₂ K)
  close_wire_right W₁ W₂ K :=
    Observation.IsSchedulingInsensitive.rel_of_activationEquiv
      (openTheory_plug_wire_right_activation_equiv Party m schedulerSampler W₁ W₂ K)

end UC
end Interaction
