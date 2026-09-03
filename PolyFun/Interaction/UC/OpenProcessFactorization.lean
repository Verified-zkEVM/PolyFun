/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.OpenProcessModel
public import PolyFun.Interaction.UC.OpenProcessSamplerCoherence

/-!
# Plug factorization for the process model, up to activation equivalence

`OpenTheory.HasPlugFactorization` asks that closing a `par` or `wire` composite
against a context factor through one component, with the other absorbed into
the context. The process-backed `openTheory` satisfies none of those as
equalities: each binary composition prepends its own scheduler node, so the
two sides of a factorization do not even give their step trees the same shape.

They do agree up to `OpenProcessActivationEquiv`. The regrouping only moves
`.internal` scheduler nodes, and `activationLTS` labels those silent, so the
delay bisimulation absorbs them. This is a structural result only:
`OpenProcessActivationEquiv` erases packet/action identity and `stepSampler`,
and these proofs do not transport the nested scheduler samplers. A downstream
packet-, probability-, or sampler-aware observation needs an additional
scheduler-transport theorem and an observation-invariance proof before these
laws imply its factorization laws.

## Main results

* `openTheory_plug_par_left_activation_equiv` and
  `openTheory_plug_par_right_activation_equiv`
* `openTheory_plug_wire_left_activation_equiv` and
  `openTheory_plug_wire_right_activation_equiv`

Each is a chain of the coherence shapes in `OpenProcessCoherence`: after the
normalization equalities push every `mapBoundary` into the injections, the
source `plug (compose W₁ W₂) K` is reassociated to nest the absorbed component
with the context, and the inner pair is commuted under
`OpenProcess.interleave_congr_right`. The `_right` variants first commute the
composite under `OpenProcess.interleave_congr_left`.

`OpenProcessFactorization.sourceSchedule`, `leftSchedule`, and `rightSchedule`
record the scheduler truth tables of the two sides, indexed by the leaf type
`OpenProcessFactorization.Leaf` of `OpenProcessSamplerCoherence`; the
sampler-aware laws consume them.
-/

public section

universe u v w w'

namespace Interaction

namespace UC

open OpenNodeContext (preservesActivation_map preservesActivation_inlTensor
  preservesActivation_inrTensor preservesActivation_wireLeft preservesActivation_wireRight
  preservesActivation_close)

variable (Party : Type u)
variable (m : Type w → Type w')
variable (schedulerSampler : m (ULift.{w, 0} Bool))

namespace OpenProcessFactorization

/-- Scheduler choices on the source shape `plug (compose W₁ W₂) K`.
The outer choice is listed first; the inner choice is present only when the
composite is selected. -/
def sourceSchedule : Leaf → List Bool
  | .first => [true, true]
  | .second => [true, false]
  | .context => [false]

/-- Scheduler choices after factoring through the first component. -/
def leftSchedule : Leaf → List Bool
  | .first => [true]
  | .second => [false, false]
  | .context => [false, true]

/-- Scheduler choices after factoring through the second component. -/
def rightSchedule : Leaf → List Bool
  | .first => [false, false]
  | .second => [true]
  | .context => [false, true]

end OpenProcessFactorization

/-- Closing a parallel composition factors through its left component, up to
activation equivalence: absorbing `W₂` into the context regroups the internal
scheduler nesting without changing which steps activate a party.

This is `OpenTheory.HasPlugFactorization.close_par_left` for the process
model. The strict equality fails — the two sides nest their scheduler nodes
differently, so the step trees do not even share a shape — but the regrouping
only moves `.internal` nodes, which `activationLTS` labels silent. -/
theorem openTheory_plug_par_left_activation_equiv
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
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
              (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm.toHom W₂)))) := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave, OpenProcess.mapBoundary_eq_mapHom,
    OpenProcess.interleave_mapHom_right]
  have hK : OpenNodeContext.PreservesActivation
      ((OpenNodeContext.map.{u, w} Party
        (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁)).toHom).comp
        (OpenNodeContext.wireLeft Party (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)
          PortBoundary.empty)) :=
    (preservesActivation_map _).comp (preservesActivation_wireLeft _ _ _)
  have hW₂ : OpenNodeContext.PreservesActivation
      (((OpenNodeContext.map.{u, w} Party
        (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁)).toHom).comp
        (OpenNodeContext.wireRight Party (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)
          PortBoundary.empty)).comp
        (OpenNodeContext.map.{u, w} Party
          (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm.toHom)) :=
    ((preservesActivation_map _).comp (preservesActivation_wireRight _ _ _)).comp
      (preservesActivation_map _)
  exact (interleave_assoc_activationEquiv W₁ W₂ K schedulerSampler schedulerSampler
    schedulerSampler schedulerSampler
    (preservesActivation_inlTensor Δ₁ Δ₂) (preservesActivation_inrTensor Δ₁ Δ₂)
    (preservesActivation_close _) (preservesActivation_close _) hW₂ hK
    (preservesActivation_close Δ₁) (preservesActivation_close _)
    (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _)
    (map_schedulerNode_isActivated Party
      (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁)).toHom)
      (schedulerNode_isActivated Party _)).trans
    (OpenProcess.interleave_congr_right W₁ _ (preservesActivation_close Δ₁)
      (preservesActivation_close _) (schedulerNode_isActivated Party _) schedulerSampler
      (interleave_comm_activationEquiv W₂ K schedulerSampler schedulerSampler hW₂ hK hK hW₂
        (map_schedulerNode_isActivated Party _) (map_schedulerNode_isActivated Party _))
      schedulerSampler)

/-- Closing a wired composition factors through its left factor, up to
activation equivalence: absorbing `W₂` into the context regroups the internal
scheduler nesting without changing which steps activate a party.

This is `OpenTheory.HasPlugFactorization.close_wire_left` for the process
model. The argument is the same regrouping as
`openTheory_plug_par_left_activation_equiv`, with the `wireLeft` / `wireRight`
boundary embeddings in place of the tensor injections; the right-hand side
carries one fewer `mapBoundary` because `swap` distributes over `tensor`
definitionally, so no outer reshape is needed. -/
theorem openTheory_plug_wire_left_activation_equiv
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    (W₂ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).wire W₁ W₂) K)
      ((openTheory Party m schedulerSampler).plug W₁
        ((openTheory Party m schedulerSampler).wire
          (Δ₁ := PortBoundary.swap Δ₁)
          (Γ := PortBoundary.swap Δ₂)
          (Δ₂ := PortBoundary.swap Γ)
          K
          (OpenProcess.mapBoundary
            (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom W₂))) := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_eq_mapHom, OpenProcess.interleave_mapHom_right]
  have hK : OpenNodeContext.PreservesActivation
      (OpenNodeContext.wireLeft.{u, w} Party (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)
        (PortBoundary.swap Γ)) :=
    preservesActivation_wireLeft _ _ _
  have hW₂ : OpenNodeContext.PreservesActivation
      ((OpenNodeContext.wireRight.{u, w} Party (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)
        (PortBoundary.swap Γ)).comp
        (OpenNodeContext.map.{u, w} Party
          (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom)) :=
    (preservesActivation_wireRight _ _ _).comp (preservesActivation_map _)
  exact (interleave_assoc_activationEquiv W₁ W₂ K schedulerSampler schedulerSampler
    schedulerSampler schedulerSampler
    (preservesActivation_wireLeft Δ₁ Γ Δ₂) (preservesActivation_wireRight Δ₁ Γ Δ₂)
    (preservesActivation_close _) (preservesActivation_close _) hW₂ hK
    (preservesActivation_close _) (preservesActivation_close _)
    (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _)
    (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _)).trans
    (OpenProcess.interleave_congr_right W₁ _ (preservesActivation_close _)
      (preservesActivation_close _) (schedulerNode_isActivated Party _) schedulerSampler
      (interleave_comm_activationEquiv W₂ K schedulerSampler schedulerSampler hW₂ hK hK hW₂
        (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _))
      schedulerSampler)

/-- Closing a parallel composition factors through its right component, up to
activation equivalence. The mirror of
`openTheory_plug_par_left_activation_equiv`, absorbing `W₁` into the context
instead of `W₂`; the context additionally commutes its two halves, which is the
extra `tensorComm` reshape on `K`. -/
theorem openTheory_plug_par_right_activation_equiv
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).par W₁ W₂) K)
      ((openTheory Party m schedulerSampler).plug W₂
        (OpenProcess.mapBoundary
          (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₂)).toHom
          ((openTheory Party m schedulerSampler).wire
            (Γ := PortBoundary.swap Δ₁)
            (Δ₂ := PortBoundary.empty)
            (OpenProcess.mapBoundary
              (PortBoundary.Equiv.tensorComm
                (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)).toHom K)
            (OpenProcess.mapBoundary
              (PortBoundary.Equiv.tensorEmptyRight Δ₁).symm.toHom W₁)))) := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave]
  simp only [OpenProcess.mapBoundary_eq_mapHom]
  rw [OpenProcess.interleave_mapHom_left, OpenProcess.interleave_mapHom_right]
  have hK : OpenNodeContext.PreservesActivation
      (((OpenNodeContext.map.{u, w} Party
        (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₂)).toHom).comp
        (OpenNodeContext.wireLeft Party (PortBoundary.swap Δ₂) (PortBoundary.swap Δ₁)
          PortBoundary.empty)).comp
        (OpenNodeContext.map.{u, w} Party
          (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)).toHom)) :=
    ((preservesActivation_map _).comp (preservesActivation_wireLeft _ _ _)).comp
      (preservesActivation_map _)
  have hW₁ : OpenNodeContext.PreservesActivation
      (((OpenNodeContext.map.{u, w} Party
        (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₂)).toHom).comp
        (OpenNodeContext.wireRight Party (PortBoundary.swap Δ₂) (PortBoundary.swap Δ₁)
          PortBoundary.empty)).comp
        (OpenNodeContext.map.{u, w} Party
          (PortBoundary.Equiv.tensorEmptyRight Δ₁).symm.toHom)) :=
    ((preservesActivation_map _).comp (preservesActivation_wireRight _ _ _)).comp
      (preservesActivation_map _)
  exact ((OpenProcess.interleave_congr_left _ K (preservesActivation_close _)
    (preservesActivation_close _) (schedulerNode_isActivated Party _) schedulerSampler
    (interleave_comm_activationEquiv W₁ W₂ schedulerSampler schedulerSampler
      (preservesActivation_inlTensor Δ₁ Δ₂) (preservesActivation_inrTensor Δ₁ Δ₂)
      (preservesActivation_inrTensor Δ₁ Δ₂) (preservesActivation_inlTensor Δ₁ Δ₂)
      (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _))
    schedulerSampler).trans
    (interleave_assoc_activationEquiv W₂ W₁ K schedulerSampler schedulerSampler
      schedulerSampler schedulerSampler
      (preservesActivation_inrTensor Δ₁ Δ₂) (preservesActivation_inlTensor Δ₁ Δ₂)
      (preservesActivation_close _) (preservesActivation_close _) hW₁ hK
      (preservesActivation_close Δ₂) (preservesActivation_close _)
      (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _)
      (map_schedulerNode_isActivated Party
      (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₂)).toHom)
      (schedulerNode_isActivated Party _))).trans
    (OpenProcess.interleave_congr_right W₂ _ (preservesActivation_close Δ₂)
      (preservesActivation_close _) (schedulerNode_isActivated Party _) schedulerSampler
      (interleave_comm_activationEquiv W₁ K schedulerSampler schedulerSampler hW₁ hK hK hW₁
        (map_schedulerNode_isActivated Party _) (map_schedulerNode_isActivated Party _))
      schedulerSampler)

/-- Closing a wired composition factors through its right factor, up to
activation equivalence. The mirror of
`openTheory_plug_wire_left_activation_equiv`. -/
theorem openTheory_plug_wire_right_activation_equiv
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    (W₂ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).wire W₁ W₂) K)
      ((openTheory Party m schedulerSampler).plug W₂
        (OpenProcess.mapBoundary
          (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₂) Γ).toHom
          ((openTheory Party m schedulerSampler).wire
            (Δ₁ := PortBoundary.swap Δ₂)
            (Γ := PortBoundary.swap Δ₁)
            (Δ₂ := Γ)
            (OpenProcess.mapBoundary
              (PortBoundary.Equiv.tensorComm
                (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)).toHom K)
            W₁))) := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave, OpenProcess.mapBoundary_eq_mapHom,
    OpenProcess.interleave_mapHom_left]
  have hK : OpenNodeContext.PreservesActivation
      (((OpenNodeContext.map.{u, w} Party
        (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₂) Γ).toHom).comp
        (OpenNodeContext.wireLeft Party (PortBoundary.swap Δ₂) (PortBoundary.swap Δ₁) Γ)).comp
        (OpenNodeContext.map.{u, w} Party
          (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)).toHom)) :=
    ((preservesActivation_map _).comp (preservesActivation_wireLeft _ _ _)).comp
      (preservesActivation_map _)
  have hW₁ : OpenNodeContext.PreservesActivation
      ((OpenNodeContext.map.{u, w} Party
        (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₂) Γ).toHom).comp
        (OpenNodeContext.wireRight Party (PortBoundary.swap Δ₂) (PortBoundary.swap Δ₁) Γ)) :=
    (preservesActivation_map _).comp (preservesActivation_wireRight _ _ _)
  exact ((OpenProcess.interleave_congr_left _ K (preservesActivation_close _)
    (preservesActivation_close _) (schedulerNode_isActivated Party _) schedulerSampler
    (interleave_comm_activationEquiv W₁ W₂ schedulerSampler schedulerSampler
      (preservesActivation_wireLeft Δ₁ Γ Δ₂) (preservesActivation_wireRight Δ₁ Γ Δ₂)
      (preservesActivation_wireRight Δ₁ Γ Δ₂) (preservesActivation_wireLeft Δ₁ Γ Δ₂)
      (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _))
    schedulerSampler).trans
    (interleave_assoc_activationEquiv W₂ W₁ K schedulerSampler schedulerSampler
      schedulerSampler schedulerSampler
      (preservesActivation_wireRight Δ₁ Γ Δ₂) (preservesActivation_wireLeft Δ₁ Γ Δ₂)
      (preservesActivation_close _) (preservesActivation_close _) hW₁ hK
      (preservesActivation_close _) (preservesActivation_close _)
      (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _)
      (map_schedulerNode_isActivated Party
      (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₂) Γ).toHom)
      (schedulerNode_isActivated Party _))).trans
    (OpenProcess.interleave_congr_right W₂ _ (preservesActivation_close _)
      (preservesActivation_close _) (schedulerNode_isActivated Party _) schedulerSampler
      (interleave_comm_activationEquiv W₁ K schedulerSampler schedulerSampler hW₁ hK hK hW₁
        (map_schedulerNode_isActivated Party _) (map_schedulerNode_isActivated Party _))
      schedulerSampler)

end UC
end Interaction
