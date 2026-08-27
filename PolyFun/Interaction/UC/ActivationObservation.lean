/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.OpenProcessFactorization

/-!
# The activation observation on open processes

`Observation.activation` packages `OpenProcessActivationEquiv` as an
`Observation` over the concrete open-process theory `openTheory`, and proves
that it respects plug commutation and plug/wire factorization from the named
activation-equivalence theorems of `OpenProcessModel` and
`OpenProcessFactorization`.

This observation judges *coarse activation structure only*: silent scheduler
steps may be absorbed, and packet identity, action identity, and `stepSampler`
effects are invisible to it.  `Emulates real ideal (Observation.activation …)`
therefore asserts that every closing context sees the same activation
structure on both sides — a structural coherence statement, **not** a
cryptographic security statement.  The three-relation separation recorded in
`docs/wiki/uc.md` continues to apply; a packet- and sampler-aware observation
is a separate, stronger construction.

Since `Observation.RespectsFactorization` holds, the entire `Emulates` /
`EmulatesWithin` composition suite is available over `openTheory` at the
activation level.
-/

public section

universe u v w w'

namespace Interaction
namespace UC

variable (Party : Type u) (m : Type w → Type w')
  (schedulerSampler : m (ULift.{w, 0} Bool))

/-- Coarse activation structure as an observation on the concrete open-process
theory: two closed processes are related when their activation-labelled
transition systems are delay-bisimulation equivalent.

This is a structural observation, not a security observation; see the module
docstring. -/
def Observation.activation :
    Observation (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  rel := OpenProcessActivationEquiv
  equiv :=
    ⟨fun p => OpenProcessActivationEquiv.refl p,
      OpenProcessActivationEquiv.symm,
      OpenProcessActivationEquiv.trans⟩

@[simp]
theorem Observation.activation_rel
    {c₁ c₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Closed} :
    (Observation.activation Party m schedulerSampler).rel c₁ c₂ ↔
      OpenProcessActivationEquiv c₁ c₂ :=
  Iff.rfl

/-- The activation observation respects plug commutation and plug/wire
factorization: each field is one of the named activation-equivalence theorems.
This makes the full `Emulates` composition suite available over `openTheory`
at the activation level. -/
instance Observation.respectsFactorization_activation :
    (Observation.activation.{u, v, w, w'} Party m schedulerSampler).RespectsFactorization where
  plug_comm W K :=
    openTheory_plug_comm_activation_equiv Party m schedulerSampler W K
  close_par_left W₁ W₂ K :=
    openTheory_plug_par_left_activation_equiv Party m schedulerSampler W₁ W₂ K
  close_par_right W₁ W₂ K :=
    openTheory_plug_par_right_activation_equiv Party m schedulerSampler W₁ W₂ K
  close_wire_left W₁ W₂ K :=
    openTheory_plug_wire_left_activation_equiv Party m schedulerSampler W₁ W₂ K
  close_wire_right W₁ W₂ K :=
    openTheory_plug_wire_right_activation_equiv Party m schedulerSampler W₁ W₂ K

end UC
end Interaction
