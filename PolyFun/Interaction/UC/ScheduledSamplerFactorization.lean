/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

import all PolyFun.Interaction.UC.Emulates
import all PolyFun.Interaction.UC.OpenProcessSamplerEquiv
import all PolyFun.Interaction.UC.ScheduledOpenProcessModel
public import PolyFun.Interaction.UC.OpenProcessSamplerFactorization
public import PolyFun.Interaction.UC.SamplerObservation
public import PolyFun.Interaction.UC.Scheduler
public import PolyFun.Interaction.UC.ScheduledOpenProcessModel

/-!
# Path-sampler factorization for mass-aware scheduling

The structural UC factorization maps already identify the leaves of the
source and reassociated binary process trees. This module proves the sampler
statements for the mass-aware scheduler: whenever the binary scheduler
satisfies `BinaryScheduler.IsCoherent`, the hierarchical draws of both sides of
a regrouping are related, so the generic shapes of `OpenProcessSamplerCoherence`
apply.

Concretely, `BinaryScheduler.sourceDraw`, `leftDraw`, and `rightDraw` are the
nested draws `nestedDrawLeft`, `nestedDrawFactorLeft`, and
`nestedDrawFactorRight` at the scheduler calls a composition makes, so
`IsCoherent` supplies exactly the transport facts the shapes ask for. The
theory `scheduledOpenTheory` then satisfies plug commutation and the four plug
factorizations up to `OpenProcessSamplerEquiv R` on the underlying processes,
and `Observation.scheduledSampler` packages that as an observation respecting
factorization. Everything remains independent of probability; downstream
models only need to prove the scheduler coherence law for their observation
relation.
-/

public section

universe u v w w'

namespace Interaction
namespace UC

open Concurrent OpenProcessFactorization

namespace BinaryScheduler

variable {m : Type w → Type w'} [Monad m]

/-- The source-shaped mass-aware draw is the source nesting's draw at the two
scheduler calls of `plug (compose W₁ W₂) K`. -/
theorem sourceDraw_eq_nestedDrawLeft (scheduler : BinaryScheduler m)
    (first second context : ℕ+) :
    sourceDraw scheduler first second context =
      nestedDrawLeft (scheduler (first + second) context) (scheduler first second) := by
  unfold sourceDraw nestedDrawLeft
  refine congrArg (_ >>= ·) (funext fun outer => ?_)
  obtain ⟨b⟩ := outer
  cases b
  · rfl
  · refine congrArg (_ >>= ·) (funext fun inner => ?_)
    obtain ⟨b'⟩ := inner
    cases b' <;> rfl

/-- The left-factored mass-aware draw is the left-factored nesting's draw at
the two scheduler calls of `plug W₁ (wire K W₂)`. -/
theorem leftDraw_eq_nestedDrawFactorLeft (scheduler : BinaryScheduler m)
    (first second context : ℕ+) :
    leftDraw scheduler first second context =
      nestedDrawFactorLeft (scheduler first (context + second)) (scheduler context second) := by
  unfold leftDraw nestedDrawFactorLeft
  refine congrArg (_ >>= ·) (funext fun outer => ?_)
  obtain ⟨b⟩ := outer
  cases b
  · refine congrArg (_ >>= ·) (funext fun inner => ?_)
    obtain ⟨b'⟩ := inner
    cases b' <;> rfl
  · rfl

/-- The right-factored mass-aware draw is the right-factored nesting's draw at
the two scheduler calls of `plug W₂ (wire K W₁)`. -/
theorem rightDraw_eq_nestedDrawFactorRight (scheduler : BinaryScheduler m)
    (first second context : ℕ+) :
    rightDraw scheduler first second context =
      nestedDrawFactorRight (scheduler second (context + first)) (scheduler context first) := by
  unfold rightDraw nestedDrawFactorRight
  refine congrArg (_ >>= ·) (funext fun outer => ?_)
  obtain ⟨b⟩ := outer
  cases b
  · refine congrArg (_ >>= ·) (funext fun inner => ?_)
    obtain ⟨b'⟩ := inner
    cases b' <;> rfl
  · rfl

/-- Binding the source-shaped mass-aware draw against a continuation exposes
the two scheduler calls used by the nested process sampler. -/
theorem sourceDraw_bind [LawfulMonad m]
    (scheduler : BinaryScheduler m) (first second context : ℕ+)
    {α : Type w} (h : ULift.{w, 0} Leaf → m α) :
    sourceDraw scheduler first second context >>= h =
      scheduler (first + second) context >>= fun outer =>
        if outer.down then
          scheduler first second >>= fun inner =>
            if inner.down then h ⟨.first⟩ else h ⟨.second⟩
        else
          h ⟨.context⟩ := by
  simp only [sourceDraw, bind_assoc]
  refine bind_congr fun outer => ?_
  obtain ⟨choice⟩ := outer
  cases choice
  · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  · simp only [↓reduceIte, bind_assoc]
    refine bind_congr fun inner => ?_
    obtain ⟨choice⟩ := inner
    cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]

/-- Binding the left-factored mass-aware draw exposes the scheduler calls used
by the left-reassociated process sampler. -/
theorem leftDraw_bind [LawfulMonad m]
    (scheduler : BinaryScheduler m) (first second context : ℕ+)
    {α : Type w} (h : ULift.{w, 0} Leaf → m α) :
    leftDraw scheduler first second context >>= h =
      scheduler first (context + second) >>= fun outer =>
        if outer.down then
          h ⟨.first⟩
        else
          scheduler context second >>= fun inner =>
            if inner.down then h ⟨.context⟩ else h ⟨.second⟩ := by
  simp only [leftDraw, bind_assoc]
  refine bind_congr fun outer => ?_
  obtain ⟨choice⟩ := outer
  cases choice
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
    refine bind_congr fun inner => ?_
    obtain ⟨choice⟩ := inner
    cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  · simp only [↓reduceIte, pure_bind]

/-- Binding the right-factored mass-aware draw exposes the scheduler calls
used by the right-reassociated process sampler. -/
theorem rightDraw_bind [LawfulMonad m]
    (scheduler : BinaryScheduler m) (first second context : ℕ+)
    {α : Type w} (h : ULift.{w, 0} Leaf → m α) :
    rightDraw scheduler first second context >>= h =
      scheduler second (context + first) >>= fun outer =>
        if outer.down then
          h ⟨.second⟩
        else
          scheduler context first >>= fun inner =>
            if inner.down then h ⟨.context⟩ else h ⟨.first⟩ := by
  simp only [rightDraw, bind_assoc]
  refine bind_congr fun outer => ?_
  obtain ⟨choice⟩ := outer
  cases choice
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
    refine bind_congr fun inner => ?_
    obtain ⟨choice⟩ := inner
    cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  · simp only [↓reduceIte, pure_bind]

/-! ### Coherence in the form the shapes consume -/

variable {R : MonadRelFamily m} {scheduler : BinaryScheduler m}

/-- The flipped draw for two masses is related to the draw for the swapped
masses. -/
theorem IsCoherent.flip_rel (h : IsCoherent R scheduler) (left right : ℕ+) :
    R.rel (schedulerFlip <$> scheduler left right) (scheduler right left) :=
  R.symm (h.swap right left)

/-- The source nesting's draw is related to the left-factored nesting's draw
at the scheduler calls of a left plug factorization. -/
theorem IsCoherent.nestedDrawLeft_rel_factorLeft (h : IsCoherent R scheduler)
    (first second context : ℕ+) :
    R.rel (nestedDrawLeft (scheduler (first + second) context) (scheduler first second))
      (nestedDrawFactorLeft (scheduler first (context + second))
        (scheduler context second)) := by
  rw [← sourceDraw_eq_nestedDrawLeft, ← leftDraw_eq_nestedDrawFactorLeft]
  exact h.left first second context

/-- The source nesting's draw is related to the right-factored nesting's draw
at the scheduler calls of a right plug factorization. -/
theorem IsCoherent.nestedDrawLeft_rel_factorRight (h : IsCoherent R scheduler)
    (first second context : ℕ+) :
    R.rel (nestedDrawLeft (scheduler (first + second) context) (scheduler first second))
      (nestedDrawFactorRight (scheduler second (context + first))
        (scheduler context first)) := by
  rw [← sourceDraw_eq_nestedDrawLeft, ← rightDraw_eq_nestedDrawFactorRight]
  exact h.right first second context

end BinaryScheduler

/-! ## Reassociated path samplers -/

/-- The source-shaped and left-factored nested path samplers are related after
applying the structural left-reassociation path equivalence. -/
theorem samplePath_interleave_assoc_left {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] (R : MonadRelFamily m)
    (scheduler : BinaryScheduler m) (coherent : scheduler.IsCoherent R)
    (firstMass secondMass contextMass : ℕ+)
    (firstTree secondTree contextTree : TypeTree.{w})
    (firstSampler : TypeTree.Sampler m firstTree)
    (secondSampler : TypeTree.Sampler m secondTree)
    (contextSampler : TypeTree.Sampler m contextTree) :
    R.rel
      ((fun path => parLeftPathEquiv firstTree secondTree contextTree path) <$>
        TypeTree.samplePath _
          (TypeTree.Sampler.interleave
            (scheduler (firstMass + secondMass) contextMass)
            (TypeTree.Sampler.interleave (scheduler firstMass secondMass)
              firstSampler secondSampler)
            contextSampler))
      (TypeTree.samplePath _
        (TypeTree.Sampler.interleave
          (scheduler firstMass (contextMass + secondMass)) firstSampler
          (TypeTree.Sampler.interleave (scheduler contextMass secondMass)
            contextSampler secondSampler))) :=
  samplePath_factorLeft_rel firstSampler secondSampler contextSampler R
    (coherent.nestedDrawLeft_rel_factorLeft firstMass secondMass contextMass)

/-- The source-shaped and right-factored nested path samplers are related after
applying the structural right-reassociation path equivalence. -/
theorem samplePath_interleave_assoc_right {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] (R : MonadRelFamily m)
    (scheduler : BinaryScheduler m) (coherent : scheduler.IsCoherent R)
    (firstMass secondMass contextMass : ℕ+)
    (firstTree secondTree contextTree : TypeTree.{w})
    (firstSampler : TypeTree.Sampler m firstTree)
    (secondSampler : TypeTree.Sampler m secondTree)
    (contextSampler : TypeTree.Sampler m contextTree) :
    R.rel
      ((fun path => parRightPathEquiv firstTree secondTree contextTree path) <$>
        TypeTree.samplePath _
          (TypeTree.Sampler.interleave
            (scheduler (firstMass + secondMass) contextMass)
            (TypeTree.Sampler.interleave (scheduler firstMass secondMass)
              firstSampler secondSampler)
            contextSampler))
      (TypeTree.samplePath _
        (TypeTree.Sampler.interleave
          (scheduler secondMass (contextMass + firstMass)) secondSampler
          (TypeTree.Sampler.interleave (scheduler contextMass firstMass)
            contextSampler firstSampler))) :=
  samplePath_factorRight_rel firstSampler secondSampler contextSampler R
    (coherent.nestedDrawLeft_rel_factorRight firstMass secondMass contextMass)

/-! ## Sampler-aware laws of the mass-aware theory -/

section ScheduledLaws

variable (Party : Type u) (m : Type w → Type w') [Monad m] [LawfulMonad m]
  (scheduler : BinaryScheduler m) (R : MonadRelFamily m)

/-- `plug` is commutative in the mass-aware theory up to sampler equivalence
of the underlying processes, under a coherent scheduler. -/
theorem scheduledOpenTheory_plug_comm_sampler_equiv (coherent : scheduler.IsCoherent R)
    {Δ : PortBoundary}
    (W : ScheduledOpenProcess.{u, v, w, w'} m Party Δ)
    (K : ScheduledOpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ)) :
    OpenProcessSamplerEquiv R
      ((scheduledOpenTheory Party m scheduler).plug W K).process
      ((scheduledOpenTheory Party m scheduler).plug K W).process := by
  simp only [scheduledOpenTheory, ScheduledOpenProcess.process_interleave]
  exact interleave_comm_samplerEquiv R W.process K.process _ _
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _)
    (coherent.flip_rel _ _)

/-- Closing a parallel composition factors through its left component in the
mass-aware theory, up to sampler equivalence of the underlying processes,
under a coherent scheduler. -/
theorem scheduledOpenTheory_plug_par_left_sampler_equiv (coherent : scheduler.IsCoherent R)
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₂)
    (K : ScheduledOpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessSamplerEquiv R
      ((scheduledOpenTheory Party m scheduler).plug
        ((scheduledOpenTheory Party m scheduler).par W₁ W₂) K).process
      ((scheduledOpenTheory Party m scheduler).plug W₁
        ((scheduledOpenTheory Party m scheduler).map
          (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁)).toHom
          ((scheduledOpenTheory Party m scheduler).wire
            (Γ := PortBoundary.swap Δ₂)
            (Δ₂ := PortBoundary.empty)
            K
            ((scheduledOpenTheory Party m scheduler).map
              (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm.toHom W₂)))).process := by
  simp only [scheduledOpenTheory, ScheduledOpenProcess.process_interleave,
    ScheduledOpenProcess.process_mapBoundary, ScheduledOpenProcess.mass_interleave,
    ScheduledOpenProcess.mass_mapBoundary]
  rw [OpenProcess.mapBoundary_interleave, OpenProcess.mapBoundary_eq_mapHom,
    OpenProcess.interleave_mapHom_right]
  exact interleave_factorLeft_samplerEquiv R W₁.process W₂.process K.process _ _ _ _
    (close_comp_inlTensor Party Δ₁ Δ₂)
    ((close_comp_inrTensor Party Δ₁ Δ₂).trans
      (close_comp_map_comp_wireRight_comp_map Party (Δ₁ := PortBoundary.swap Δ₁)
        (Γ := PortBoundary.swap Δ₂) (Δ₂ := PortBoundary.empty) _ _).symm)
    (close_comp_map_comp_wireLeft Party (Δ₁ := PortBoundary.swap Δ₁) (Γ := PortBoundary.swap Δ₂)
      (Δ₂ := PortBoundary.empty) _).symm
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _).close
    (isInternalNode_schedulerNode Party _)
    ((isInternalNode_schedulerNode Party _).map _).close
    (coherent.nestedDrawLeft_rel_factorLeft _ _ _)

/-- Closing a wired composition factors through its left factor in the
mass-aware theory, up to sampler equivalence of the underlying processes,
under a coherent scheduler. -/
theorem scheduledOpenTheory_plug_wire_left_sampler_equiv (coherent : scheduler.IsCoherent R)
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : ScheduledOpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    (W₂ : ScheduledOpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : ScheduledOpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessSamplerEquiv R
      ((scheduledOpenTheory Party m scheduler).plug
        ((scheduledOpenTheory Party m scheduler).wire W₁ W₂) K).process
      ((scheduledOpenTheory Party m scheduler).plug W₁
        ((scheduledOpenTheory Party m scheduler).wire
          (Δ₁ := PortBoundary.swap Δ₁)
          (Γ := PortBoundary.swap Δ₂)
          (Δ₂ := PortBoundary.swap Γ)
          K
          ((scheduledOpenTheory Party m scheduler).map
            (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom W₂))).process := by
  simp only [scheduledOpenTheory, ScheduledOpenProcess.process_interleave,
    ScheduledOpenProcess.process_mapBoundary, ScheduledOpenProcess.mass_interleave,
    ScheduledOpenProcess.mass_mapBoundary]
  rw [OpenProcess.mapBoundary_eq_mapHom, OpenProcess.interleave_mapHom_right]
  exact interleave_factorLeft_samplerEquiv R W₁.process W₂.process K.process _ _ _ _
    (close_comp_wireLeft Party Δ₁ Γ Δ₂)
    ((close_comp_wireRight Party Δ₁ Γ Δ₂).trans
      (close_comp_wireRight_comp_map Party (Δ₁ := PortBoundary.swap Δ₁)
        (Γ := PortBoundary.swap Δ₂) (Δ₂ := PortBoundary.swap Γ) _).symm)
    (close_comp_wireLeft Party (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)
      (PortBoundary.swap Γ)).symm
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _).close
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _).close
    (coherent.nestedDrawLeft_rel_factorLeft _ _ _)

/-- Closing a parallel composition factors through its right component in the
mass-aware theory, up to sampler equivalence of the underlying processes,
under a coherent scheduler. -/
theorem scheduledOpenTheory_plug_par_right_sampler_equiv (coherent : scheduler.IsCoherent R)
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₂)
    (K : ScheduledOpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessSamplerEquiv R
      ((scheduledOpenTheory Party m scheduler).plug
        ((scheduledOpenTheory Party m scheduler).par W₁ W₂) K).process
      ((scheduledOpenTheory Party m scheduler).plug W₂
        ((scheduledOpenTheory Party m scheduler).map
          (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₂)).toHom
          ((scheduledOpenTheory Party m scheduler).wire
            (Γ := PortBoundary.swap Δ₁)
            (Δ₂ := PortBoundary.empty)
            ((scheduledOpenTheory Party m scheduler).map
              (PortBoundary.Equiv.tensorComm
                (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)).toHom K)
            ((scheduledOpenTheory Party m scheduler).map
              (PortBoundary.Equiv.tensorEmptyRight Δ₁).symm.toHom W₁)))).process := by
  simp only [scheduledOpenTheory, ScheduledOpenProcess.process_interleave,
    ScheduledOpenProcess.process_mapBoundary, ScheduledOpenProcess.mass_interleave,
    ScheduledOpenProcess.mass_mapBoundary]
  rw [OpenProcess.mapBoundary_interleave]
  simp only [OpenProcess.mapBoundary_eq_mapHom]
  rw [OpenProcess.interleave_mapHom_left, OpenProcess.interleave_mapHom_right]
  exact interleave_factorRight_samplerEquiv R W₁.process W₂.process K.process _ _ _ _
    ((close_comp_inlTensor Party Δ₁ Δ₂).trans
      (close_comp_map_comp_wireRight_comp_map Party (Δ₁ := PortBoundary.swap Δ₂)
        (Γ := PortBoundary.swap Δ₁) (Δ₂ := PortBoundary.empty) _ _).symm)
    (close_comp_inrTensor Party Δ₁ Δ₂)
    (close_comp_map_comp_wireLeft_comp_map Party (Δ₁ := PortBoundary.swap Δ₂)
      (Γ := PortBoundary.swap Δ₁) (Δ₂ := PortBoundary.empty)
      (Δ' := PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) _ _).symm
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _).close
    (isInternalNode_schedulerNode Party _)
    ((isInternalNode_schedulerNode Party _).map _).close
    (coherent.nestedDrawLeft_rel_factorRight _ _ _)

/-- Closing a wired composition factors through its right factor in the
mass-aware theory, up to sampler equivalence of the underlying processes,
under a coherent scheduler. -/
theorem scheduledOpenTheory_plug_wire_right_sampler_equiv (coherent : scheduler.IsCoherent R)
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : ScheduledOpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    (W₂ : ScheduledOpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : ScheduledOpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessSamplerEquiv R
      ((scheduledOpenTheory Party m scheduler).plug
        ((scheduledOpenTheory Party m scheduler).wire W₁ W₂) K).process
      ((scheduledOpenTheory Party m scheduler).plug W₂
        ((scheduledOpenTheory Party m scheduler).map
          (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₂) Γ).toHom
          ((scheduledOpenTheory Party m scheduler).wire
            (Δ₁ := PortBoundary.swap Δ₂)
            (Γ := PortBoundary.swap Δ₁)
            (Δ₂ := Γ)
            ((scheduledOpenTheory Party m scheduler).map
              (PortBoundary.Equiv.tensorComm
                (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)).toHom K)
            W₁))).process := by
  simp only [scheduledOpenTheory, ScheduledOpenProcess.process_interleave,
    ScheduledOpenProcess.process_mapBoundary, ScheduledOpenProcess.mass_interleave,
    ScheduledOpenProcess.mass_mapBoundary]
  rw [OpenProcess.mapBoundary_interleave, OpenProcess.mapBoundary_eq_mapHom,
    OpenProcess.interleave_mapHom_left]
  exact interleave_factorRight_samplerEquiv R W₁.process W₂.process K.process _ _ _ _
    ((close_comp_wireLeft Party Δ₁ Γ Δ₂).trans
      (close_comp_map_comp_wireRight Party (Δ₁ := PortBoundary.swap Δ₂)
        (Γ := PortBoundary.swap Δ₁) (Δ₂ := Γ) _).symm)
    (close_comp_wireRight Party Δ₁ Γ Δ₂)
    (close_comp_map_comp_wireLeft_comp_map Party (Δ₁ := PortBoundary.swap Δ₂)
      (Γ := PortBoundary.swap Δ₁) (Δ₂ := Γ)
      (Δ' := PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) _ _).symm
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _).close
    (isInternalNode_schedulerNode Party _)
    ((isInternalNode_schedulerNode Party _).map _).close
    (coherent.nestedDrawLeft_rel_factorRight _ _ _)

/-! ### The scheduled sampler observation -/

/-- Sampler equivalence of the underlying processes, as an observation on the
mass-aware theory. -/
def Observation.scheduledSampler :
    Observation (scheduledOpenTheory.{u, v, w, w'} Party m scheduler) where
  rel c₁ c₂ := OpenProcessSamplerEquiv R c₁.process c₂.process
  equiv :=
    ⟨fun c => OpenProcessSamplerEquiv.refl c.process,
      OpenProcessSamplerEquiv.symm,
      OpenProcessSamplerEquiv.trans⟩

@[simp]
theorem Observation.scheduledSampler_rel
    {c₁ c₂ : (scheduledOpenTheory.{u, v, w, w'} Party m scheduler).Closed} :
    (Observation.scheduledSampler Party m scheduler R).rel c₁ c₂ ↔
      OpenProcessSamplerEquiv R c₁.process c₂.process :=
  Iff.rfl

/-- Under a coherent scheduler, any observation on the mass-aware theory that
cannot distinguish sampler-equivalent underlying processes respects plug
commutation and factorization. -/
theorem Observation.respectsFactorization_of_scheduledSamplerInvariant
    (coherent : scheduler.IsCoherent R)
    {Obs : Observation (scheduledOpenTheory.{u, v, w, w'} Party m scheduler)}
    (hInv : ∀ {c₁ c₂ : (scheduledOpenTheory.{u, v, w, w'} Party m scheduler).Closed},
      OpenProcessSamplerEquiv R c₁.process c₂.process → Obs.rel c₁ c₂) :
    Obs.RespectsFactorization where
  plug_comm W K := hInv
    (scheduledOpenTheory_plug_comm_sampler_equiv Party m scheduler R coherent W K)
  close_par_left W₁ W₂ K := hInv
    (scheduledOpenTheory_plug_par_left_sampler_equiv Party m scheduler R coherent W₁ W₂ K)
  close_par_right W₁ W₂ K := hInv
    (scheduledOpenTheory_plug_par_right_sampler_equiv Party m scheduler R coherent W₁ W₂ K)
  close_wire_left W₁ W₂ K := hInv
    (scheduledOpenTheory_plug_wire_left_sampler_equiv Party m scheduler R coherent W₁ W₂ K)
  close_wire_right W₁ W₂ K := hInv
    (scheduledOpenTheory_plug_wire_right_sampler_equiv Party m scheduler R coherent W₁ W₂ K)

/-- The scheduled sampler observation respects plug commutation and
factorization under a coherent scheduler. Unlike the shared-sampler theory, no
further transport hypothesis is needed: coherence of the scheduler is the
whole obligation. -/
theorem Observation.respectsFactorization_scheduledSampler (coherent : scheduler.IsCoherent R) :
    (Observation.scheduledSampler.{u, v, w, w'} Party m scheduler R).RespectsFactorization :=
  Observation.respectsFactorization_of_scheduledSamplerInvariant Party m scheduler R coherent
    fun h => h

end ScheduledLaws

end UC
end Interaction
