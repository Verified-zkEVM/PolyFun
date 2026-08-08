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
`Observation.RespectsFactorization`. This file supplies those instances for
the process-backed `openTheory`, which cannot supply the strict
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

## Main definitions

* `Observation.IsSchedulingInsensitive Obs`: activation-equivalent closed
  processes are `Obs`-related.
* `respectsPlugComm_of_isSchedulingInsensitive`: such an observation respects
  plug commutation, so `Emulates.plug_right` and `Emulates.plug_compose` apply
  to `openTheory`.

## What is still missing

`Observation.RespectsFactorization` needs the `par` and `wire` factorization
laws, and those have no activation-equivalence counterpart yet: of the three
`OpenTheory.HasPlugWireFactor` fields only `plug_eq_wire` is covered, by
`openTheory_plug_eq_wire_activation_equiv`, while `plug_par_left` and
`plug_wire_left` are unproved for this model (as are all three `IsTraced`
laws, which would be the categorical route to them). Until they exist the
process model supports the `plug` half of the composition suite but not the
`par` and `wire` half.
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

end UC
end Interaction
