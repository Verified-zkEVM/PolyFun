/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.OpenProcess
import all PolyFun.Interaction.UC.OpenProcessModel
public import PolyFun.Interaction.UC.OpenProcessCoherence
public import PolyFun.Interaction.UC.OpenProcessModel
public import PolyFun.Interaction.UC.OpenProcessFactorization

/-!
# The generic coherence theorems recover the process-model laws

Each law of `openTheory` up to activation equivalence is a nesting of
`interleave`s with identical leaves. These checks re-derive four of the
library's laws from the generic shapes in `OpenProcessCoherence`: after the
normalization equalities push `mapBoundary` into the injections, each law is
one shape theorem, possibly chained through a congruence. The factorization
law `plug_par_left` is the model case: reassociation, then commutation of the
inner pair under the congruence.
-/

universe u v w w'

namespace Interaction.UC.OpenProcessCoherenceExamples

variable {m : Type w → Type w'} {Party : Type u} (schedulerSampler : m (ULift.{w, 0} Bool))

open OpenProcess OpenNodeContext

/-! The silence facts unfold non-exposed reducers, so they stay outside the
public section. -/

/-- Every scheduler node is silent, also after boundary adaptation. -/
theorem schedulerNode_silent (Δ : PortBoundary) :
    (schedulerNode Party Δ).boundary.isActivated = false := rfl

theorem map_schedulerNode_silent {Δ Δ' : PortBoundary} (φ : PortBoundary.Hom Δ Δ') :
    (OpenNodeContext.map.{u, w} Party φ _ (schedulerNode Party Δ)).boundary.isActivated = false :=
  rfl

/-- The unit's steps are all silent. -/
theorem openTheoryUnit_silent (s : (openTheoryUnit Party m).Proc)
    (tr : ((openTheoryUnit Party m).step s).tree.Path) :
    IsSilentStep (openTheoryUnit.{u, v, w, w'} Party m) s tr :=
  trivial

public section

/-- `par_assoc`, as reassociation of the normalized nestings. -/
theorem par_assoc' {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (W₃ : OpenProcess.{u, v, w, w'} m Party Δ₃) :
    OpenProcessActivationEquiv
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom
        ((openTheory Party m schedulerSampler).par
          ((openTheory Party m schedulerSampler).par W₁ W₂) W₃))
      ((openTheory Party m schedulerSampler).par W₁
        ((openTheory Party m schedulerSampler).par W₂ W₃)) := by
  simp only [openTheory]
  rw [mapBoundary_interleave]
  exact interleave_assoc_activationEquiv W₁ W₂ W₃ _ _ _ _
    (preservesActivation_inlTensor Δ₁ Δ₂) (preservesActivation_inrTensor Δ₁ Δ₂)
    ((preservesActivation_map _).comp (preservesActivation_inlTensor _ Δ₃))
    ((preservesActivation_map _).comp (preservesActivation_inrTensor _ Δ₃))
    (preservesActivation_inlTensor Δ₂ Δ₃) (preservesActivation_inrTensor Δ₂ Δ₃)
    (preservesActivation_inlTensor Δ₁ _) (preservesActivation_inrTensor Δ₁ _)
    (schedulerNode_silent _) (map_schedulerNode_silent _) (schedulerNode_silent _)
    (schedulerNode_silent _)

/-- `par_comm`, as commutation of the normalized nesting. -/
theorem par_comm' {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂) :
    OpenProcessActivationEquiv
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom
        ((openTheory Party m schedulerSampler).par W₁ W₂))
      ((openTheory Party m schedulerSampler).par W₂ W₁) := by
  simp only [openTheory]
  rw [mapBoundary_interleave]
  exact interleave_comm_activationEquiv W₁ W₂ _ _
    ((preservesActivation_map _).comp (preservesActivation_inlTensor Δ₁ Δ₂))
    ((preservesActivation_map _).comp (preservesActivation_inrTensor Δ₁ Δ₂))
    (preservesActivation_inlTensor Δ₂ Δ₁) (preservesActivation_inrTensor Δ₂ Δ₁)
    (map_schedulerNode_silent _) (schedulerNode_silent _)

/-- `par_leftUnit`, as left absorption of the silent unit. -/
theorem par_left_unit' {Δ : PortBoundary} (W : OpenProcess.{u, v, w, w'} m Party Δ) :
    OpenProcessActivationEquiv
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom
        ((openTheory Party m schedulerSampler).par
          (openTheoryUnit Party m) W))
      W := by
  simp only [openTheory]
  rw [mapBoundary_interleave]
  have : Inhabited (openTheoryUnit.{u, v, w, w'} Party m).Proc := ⟨PUnit.unit⟩
  exact interleave_unit_left_activationEquiv (openTheoryUnit Party m) W openTheoryUnit_silent
    ((preservesActivation_map _).comp (preservesActivation_inlTensor _ Δ))
    ((preservesActivation_map _).comp (preservesActivation_inrTensor _ Δ))
    (map_schedulerNode_silent _) _

/-- `plug_par_left`: reassociate, then commute the inner pair under the
congruence. -/
theorem plug_par_left' {Δ₁ Δ₂ : PortBoundary}
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
  rw [mapBoundary_interleave, mapBoundary_eq_mapHom, interleave_mapHom_right]
  have hF : PreservesActivation
      ((OpenNodeContext.map.{u, w} Party
        (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁)).toHom).comp
        (wireLeft Party (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂) PortBoundary.empty)) :=
    (preservesActivation_map _).comp (preservesActivation_wireLeft _ _ _)
  have hG : PreservesActivation
      (((OpenNodeContext.map.{u, w} Party
        (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁)).toHom).comp
        (wireRight Party (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂) PortBoundary.empty)).comp
        (OpenNodeContext.map.{u, w} Party
          (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm.toHom)) :=
    ((preservesActivation_map _).comp (preservesActivation_wireRight _ _ _)).comp
      (preservesActivation_map _)
  exact (interleave_assoc_activationEquiv W₁ W₂ K schedulerSampler schedulerSampler
    schedulerSampler schedulerSampler
    (preservesActivation_inlTensor Δ₁ Δ₂) (preservesActivation_inrTensor Δ₁ Δ₂)
    (preservesActivation_close _) (preservesActivation_close _) hG hF
    (preservesActivation_close Δ₁) (preservesActivation_close _)
    (schedulerNode_silent _) (schedulerNode_silent _)
    (map_schedulerNode_silent (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁)).toHom)
    (schedulerNode_silent _)).trans
    (interleave_congr_right W₁ _ (preservesActivation_close Δ₁)
      (preservesActivation_close _) (schedulerNode_silent _) schedulerSampler
      (interleave_comm_activationEquiv W₂ K schedulerSampler schedulerSampler hG hF hF hG
        (map_schedulerNode_silent _) (map_schedulerNode_silent _)) schedulerSampler)

end

end Interaction.UC.OpenProcessCoherenceExamples
