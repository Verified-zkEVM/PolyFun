/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.OpenProcessModel

/-!
# Observations on the process model that ignore scheduling

`Emulates`' composition theorems take their structural input from the
observation, through `Observation.RespectsPlugComm` and
`Observation.RespectsFactorization`. This file supplies the plug-commutation
instance for the process-backed `openTheory`, which cannot supply the strict
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
This is an explicit semantic hypothesis, not a consequence of the structural
activation equivalence. In particular, packet-aware or sampler-aware
observations need not satisfy it: activation equivalence erases packet identity
and `stepSampler` before comparing systems.

## Main definitions

* `Observation.IsSchedulingInsensitive Obs`: activation-equivalent closed
  processes are `Obs`-related.
* `respectsPlugComm_of_isSchedulingInsensitive`: such an observation respects
  plug commutation, so `Emulates.plug_right` and `Emulates.plug_compose` apply
  to `openTheory`.

## What is still missing

`OpenProcessFactorization.lean` proves the four `par` and `wire`
reassociations only for `OpenProcessActivationEquiv`. Promoting them to a
packet-, probability-, or sampler-aware observation still requires a
downstream theorem that transports the nested scheduler samplers through the
reassociation and proves that the concrete observation is invariant under
that transport. This module therefore does not install a
`RespectsFactorization` instance from activation equivalence alone.
-/

public section

universe u v w w'

namespace Interaction
namespace UC

variable {Party : Type u} {m : Type w → Type w'} {schedulerSampler : m (ULift.{w, 0} Bool)}

/--
`Obs.IsSchedulingInsensitive` states that the observation `Obs` cannot
distinguish any closed processes identified by the coarse activation semantics.

This is a *bound* on an observation, never a definition of one:
`OpenProcessActivationEquiv` retains no packet or action identity and ignores
`stepSampler`, so it is far too coarse to serve as a security observation on
its own. The class says substantially more than invisibility of the internal
scheduler nodes: it requires `Obs` to identify every pair that this coarse
activation semantics identifies. A packet- or sampler-aware observation
therefore needs a separate semantic transport theorem and will generally not
provide this instance directly.
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

end UC
end Interaction
