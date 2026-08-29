/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.Basic.Sampler
import all PolyFun.Interaction.UC.OpenProcessModel
import all PolyFun.Interaction.UC.OpenProcessSamplerEquiv
public import PolyFun.Interaction.UC.OpenProcessFactorization
public import PolyFun.Interaction.UC.OpenProcessModel
public import PolyFun.Interaction.UC.OpenProcessSamplerEquiv

/-!
# Sampler-aware coherence of the open-process theory

The structural coherence laws of `openTheory` hold up to
`OpenProcessActivationEquiv`, which erases sampler effects and uses delay
matching. This module strengthens them to `OpenProcessSamplerEquiv`, which
retains sampled-path effects, **conditionally on named scheduler-transport hypotheses**: a
single shared `schedulerSampler` does not preserve per-step scheduling
distributions across reassociation, so each law takes exactly the
`MonadRelFamily` fact about reassociated scheduler draws that it needs.
`MonadRelFamily.top` discharges every such hypothesis trivially, recovering
sampler-blind strong path equivalences unconditionally.

The activation-equivalence laws in `OpenProcessModel` and
`OpenProcessFactorization` keep their direct proofs rather than becoming
corollaries: they hold for an arbitrary `m` with no `Monad` instance, while
sampled paths — and hence this module — require `[Monad m] [LawfulMonad m]`.

`plug` commutation needs the scheduler to be `R`-fair: flipping the scheduler
coin must be invisible to the relation family
(`R.rel schedulerSampler (schedulerFlip <$> schedulerSampler)`).
-/

public section

universe u v w w'

namespace Interaction
namespace UC

open Concurrent

/-! ## Scheduler re-encodings -/

/-- Negate a lifted scheduler coin: the path re-encoding of `plug`
commutation. -/
@[expose]
def schedulerFlip : ULift.{w, 0} Bool → ULift.{w, 0} Bool :=
  fun b => ULift.up !b.down

@[simp] theorem schedulerFlip_up_true :
    schedulerFlip.{w} (ULift.up true) = ULift.up false := rfl

@[simp] theorem schedulerFlip_up_false :
    schedulerFlip.{w} (ULift.up false) = ULift.up true := rfl

/-! ## The empty boundary carries no traffic -/

/-- Any two traces over the empty interface are equal: the interface has no
positions, so no packet exists and both traces are the empty word. -/
theorem traceList_interface_empty_eq
    (x y : PFunctor.TraceList Interface.empty) : x = y :=
  match x, y with
  | [], [] => rfl
  | ⟨a, _⟩ :: _, _ => a.elim
  | [], ⟨a, _⟩ :: _ => a.elim

/-! ## Path re-encoding and sampling laws for the scheduler node -/

/-- Flip the scheduler coin at the root of a binary-choice interleaving tree,
exchanging the two branches. -/
def flipInterleavePathEquiv (t₁ t₂ : TypeTree.{w}) :
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₁
      | ⟨false⟩ => t₂) ≃
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₂
      | ⟨false⟩ => t₁) where
  toFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨false⟩, tr⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨true⟩, tr⟩
  invFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨false⟩, tr⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨true⟩, tr⟩
  left_inv := by rintro ⟨⟨b⟩, tr⟩; cases b <;> rfl
  right_inv := by rintro ⟨⟨b⟩, tr⟩; cases b <;> rfl

/-- Flipping the scheduler coin of an interleaved sample is sampling the
branch-swapped interleave under the flipped scheduler draw. -/
theorem samplePath_interleave_flip {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] {spec₁ spec₂ : TypeTree.{w}}
    (σ : m (ULift.{w, 0} Bool))
    (samp₁ : TypeTree.Sampler m spec₁) (samp₂ : TypeTree.Sampler m spec₂) :
    (fun tr => flipInterleavePathEquiv spec₁ spec₂ tr) <$>
        TypeTree.samplePath _ (TypeTree.Sampler.interleave σ samp₁ samp₂) =
      TypeTree.samplePath _
        (TypeTree.Sampler.interleave (schedulerFlip <$> σ) samp₂ samp₁) := by
  simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind,
    bind_map_left]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb <;> simp only [map_pure] <;> rfl

/-- Interleaved samples with the same branch samplers and `R`-related
scheduler draws are `R`-related. -/
theorem samplePath_interleave_congr_scheduler {m : Type w → Type w'}
    [Monad m] (R : MonadRelFamily m)
    {spec₁ spec₂ : TypeTree.{w}} {σ σ' : m (ULift.{w, 0} Bool)}
    (h : R.rel σ' σ)
    (samp₁ : TypeTree.Sampler m spec₁) (samp₂ : TypeTree.Sampler m spec₂) :
    R.rel
      (TypeTree.samplePath _ (TypeTree.Sampler.interleave σ' samp₁ samp₂))
      (TypeTree.samplePath _ (TypeTree.Sampler.interleave σ samp₁ samp₂)) := by
  simp only [TypeTree.Sampler.interleave, TypeTree.samplePath]
  exact R.bind_congr _ h

/-! ## Scheduler draws for the factorization reassociations -/

namespace OpenProcessFactorization

/-- Draw a `Leaf` with the source-shaped coin encoding
(`sourceSchedule`): the composite is selected first, then its component. -/
@[expose]
def sourceDraw {m : Type w → Type w'} [Monad m]
    (σ : m (ULift.{w, 0} Bool)) : m (ULift.{w, 0} Leaf) :=
  σ >>= fun b =>
    match b with
    | ⟨true⟩ => σ >>= fun b' =>
        match b' with
        | ⟨true⟩ => pure ⟨.first⟩
        | ⟨false⟩ => pure ⟨.second⟩
    | ⟨false⟩ => pure ⟨.context⟩

/-- Draw a `Leaf` with the left-factored coin encoding (`leftSchedule`). -/
@[expose]
def leftDraw {m : Type w → Type w'} [Monad m]
    (σ : m (ULift.{w, 0} Bool)) : m (ULift.{w, 0} Leaf) :=
  σ >>= fun b =>
    match b with
    | ⟨true⟩ => pure ⟨.first⟩
    | ⟨false⟩ => σ >>= fun b' =>
        match b' with
        | ⟨true⟩ => pure ⟨.context⟩
        | ⟨false⟩ => pure ⟨.second⟩

/-- Draw a `Leaf` with the right-factored coin encoding (`rightSchedule`). -/
@[expose]
def rightDraw {m : Type w → Type w'} [Monad m]
    (σ : m (ULift.{w, 0} Bool)) : m (ULift.{w, 0} Leaf) :=
  σ >>= fun b =>
    match b with
    | ⟨true⟩ => pure ⟨.second⟩
    | ⟨false⟩ => σ >>= fun b' =>
        match b' with
        | ⟨true⟩ => pure ⟨.context⟩
        | ⟨false⟩ => pure ⟨.first⟩

/-- Binding a source draw against a per-leaf continuation is the flattened
two-coin computation. -/
theorem sourceDraw_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (σ : m (ULift.{w, 0} Bool)) {α : Type w}
    (h : ULift.{w, 0} Leaf → m α) :
    sourceDraw σ >>= h =
      σ >>= fun b =>
        match b with
        | ⟨true⟩ => σ >>= fun b' =>
            match b' with
            | ⟨true⟩ => h ⟨.first⟩
            | ⟨false⟩ => h ⟨.second⟩
        | ⟨false⟩ => h ⟨.context⟩ := by
  simp only [sourceDraw, bind_assoc]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb
  · simp only [pure_bind]
  · simp only [bind_assoc]
    refine bind_congr fun b' => ?_
    obtain ⟨bb'⟩ := b'
    cases bb' <;> simp only [pure_bind]

/-- Binding a left-factored draw against a per-leaf continuation is the
flattened two-coin computation. -/
theorem leftDraw_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (σ : m (ULift.{w, 0} Bool)) {α : Type w}
    (h : ULift.{w, 0} Leaf → m α) :
    leftDraw σ >>= h =
      σ >>= fun b =>
        match b with
        | ⟨true⟩ => h ⟨.first⟩
        | ⟨false⟩ => σ >>= fun b' =>
            match b' with
            | ⟨true⟩ => h ⟨.context⟩
            | ⟨false⟩ => h ⟨.second⟩ := by
  simp only [leftDraw, bind_assoc]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb
  · simp only [bind_assoc]
    refine bind_congr fun b' => ?_
    obtain ⟨bb'⟩ := b'
    cases bb' <;> simp only [pure_bind]
  · simp only [pure_bind]

/-- Binding a right-factored draw against a per-leaf continuation is the
flattened two-coin computation. -/
theorem rightDraw_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (σ : m (ULift.{w, 0} Bool)) {α : Type w}
    (h : ULift.{w, 0} Leaf → m α) :
    rightDraw σ >>= h =
      σ >>= fun b =>
        match b with
        | ⟨true⟩ => h ⟨.second⟩
        | ⟨false⟩ => σ >>= fun b' =>
            match b' with
            | ⟨true⟩ => h ⟨.context⟩
            | ⟨false⟩ => h ⟨.first⟩ := by
  simp only [rightDraw, bind_assoc]
  refine bind_congr fun b => ?_
  obtain ⟨bb⟩ := b
  cases bb
  · simp only [bind_assoc]
    refine bind_congr fun b' => ?_
    obtain ⟨bb'⟩ := b'
    cases bb' <;> simp only [pure_bind]
  · simp only [pure_bind]

/-! The deterministic identity-monad cases make the reassociation obstruction
directly executable for downstream users. -/

@[simp] theorem sourceDraw_id_up_true :
    sourceDraw (m := Id) (ULift.up true : ULift.{w, 0} Bool) =
      ULift.up Leaf.first := rfl

@[simp] theorem sourceDraw_id_up_false :
    sourceDraw (m := Id) (ULift.up false : ULift.{w, 0} Bool) =
      ULift.up Leaf.context := rfl

@[simp] theorem leftDraw_id_up_true :
    leftDraw (m := Id) (ULift.up true : ULift.{w, 0} Bool) =
      ULift.up Leaf.first := rfl

@[simp] theorem leftDraw_id_up_false :
    leftDraw (m := Id) (ULift.up false : ULift.{w, 0} Bool) =
      ULift.up Leaf.second := rfl

@[simp] theorem rightDraw_id_up_true :
    rightDraw (m := Id) (ULift.up true : ULift.{w, 0} Bool) =
      ULift.up Leaf.second := rfl

@[simp] theorem rightDraw_id_up_false :
    rightDraw (m := Id) (ULift.up false : ULift.{w, 0} Bool) =
      ULift.up Leaf.first := rfl

end OpenProcessFactorization

/-! ## Path re-encoding for the left par/wire factorizations -/

/-- Regroup the nested scheduler coins of `plug (par/wire ⋯) K` onto the
left-factored shape: the first component keeps a single `true` coin, the
second component moves under two `false` coins, and the context moves under
`false, true`. -/
def parLeftPathEquiv (t₁ t₂ tk : TypeTree.{w}) :
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
        | ⟨true⟩ => t₁
        | ⟨false⟩ => t₂
      | ⟨false⟩ => tk) ≃
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₁
      | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
        | ⟨true⟩ => tk
        | ⟨false⟩ => t₂) where
  toFun := fun
    | ⟨⟨true⟩, ⟨⟨true⟩, tr⟩⟩ => ⟨⟨true⟩, tr⟩
    | ⟨⟨true⟩, ⟨⟨false⟩, tr⟩⟩ => ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩
  invFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨true⟩, ⟨⟨true⟩, tr⟩⟩
    | ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩ => ⟨⟨false⟩, tr⟩
    | ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩ => ⟨⟨true⟩, ⟨⟨false⟩, tr⟩⟩
  left_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · rfl
    · obtain ⟨⟨b'⟩, tr'⟩ := tr
      cases b' <;> rfl
  right_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · obtain ⟨⟨b'⟩, tr'⟩ := tr
      cases b' <;> rfl
    · rfl

variable (Party : Type u) (m : Type w → Type w')
  (schedulerSampler : m (ULift.{w, 0} Bool))

/-! ## Sampler-aware plug commutation -/

/-- `plug` is commutative up to sampler equivalence, provided the scheduler is
`R`-fair: closing a protocol against an environment and closing the
environment against the protocol have the same silence and boundary-trace
structure and `R`-related sampled paths, with the scheduler coin flipped.

At `R := MonadRelFamily.top` the fairness hypothesis is trivial and the
statement is the strong path-matching refinement of
`openTheory_plug_comm_activation_equiv`. -/
theorem openTheory_plug_comm_sampler_equiv [Monad m] [LawfulMonad m]
    (R : MonadRelFamily m)
    (hfair : R.rel schedulerSampler (schedulerFlip <$> schedulerSampler))
    {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w, w'} m Party Δ)
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ)) :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).plug W K)
      ((openTheory Party m schedulerSampler).plug K W) := by
  refine ⟨fun (⟨s₁, s₂⟩ : W.Proc × K.Proc) (⟨s₂', s₁'⟩ : K.Proc × W.Proc) =>
      s₁ = s₁' ∧ s₂ = s₂',
    ⟨?_⟩,
    fun ⟨s₁, s₂⟩ => ⟨⟨s₂, s₁⟩, rfl, rfl⟩,
    fun ⟨s₂, s₁⟩ => ⟨⟨s₁, s₂⟩, rfl, rfl⟩⟩
  rintro ⟨s₁, s₂⟩ ⟨s₂', s₁'⟩ ⟨h1, h2⟩
  subst h1
  subst h2
  refine ⟨flipInterleavePathEquiv (W.step s₁).tree (K.step s₂).tree,
    ?_, ?_, ?_, ?_⟩
  · -- Silence is preserved: the scheduler node is never activated and the
    -- branch decorations differ only by activation-preserving close maps.
    rintro ⟨⟨b⟩, tr⟩
    cases b <;>
      exact and_congr Iff.rfl
        (((isSilentDecoration_iff_map _ (fun X ons => by
            simp [OpenNodeContext.close, BoundaryAction.closed]) _ _).trans
          (isSilentDecoration_iff_map _ (fun X ons => by
            simp [OpenNodeContext.close, BoundaryAction.closed]) _ _).symm))
  · -- Both boundary traces live over the empty boundary.
    intro tr
    exact traceList_interface_empty_eq _ _
  · -- Successors are componentwise equal after the swap.
    rintro ⟨⟨b⟩, tr⟩
    cases b <;> exact ⟨rfl, rfl⟩
  · -- The sampled paths are related by scheduler fairness.
    change R.rel
      ((fun tr => flipInterleavePathEquiv (W.step s₁).tree (K.step s₂).tree tr)
        <$> TypeTree.samplePath _
          (TypeTree.Sampler.interleave schedulerSampler
            (W.stepSampler s₁) (K.stepSampler s₂)))
      (TypeTree.samplePath _
        (TypeTree.Sampler.interleave schedulerSampler
          (K.stepSampler s₂) (W.stepSampler s₁)))
    rw [samplePath_interleave_flip]
    exact samplePath_interleave_congr_scheduler R (R.symm hfair) _ _

/-! ## Sampler-aware left par factorization -/

open OpenProcessFactorization in
/-- Closing a parallel composition factors through its left component, up to
sampler equivalence, conditionally on the scheduler-transport fact
`R.rel (sourceDraw schedulerSampler) (leftDraw schedulerSampler)`: the source
and left-factored coin encodings of the three-way choice must be invisible to
the relation family.

This is the sampler-aware strengthening of
`openTheory_plug_par_left_activation_equiv`; at `R := MonadRelFamily.top` the
transport fact is trivial. -/
theorem openTheory_plug_par_left_sampler_equiv [Monad m] [LawfulMonad m]
    (R : MonadRelFamily m)
    (hσ : R.rel (sourceDraw schedulerSampler) (leftDraw schedulerSampler))
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (K : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessSamplerEquiv R
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
  refine ⟨fun (⟨⟨s₁, s₂⟩, k⟩ : (W₁.Proc × W₂.Proc) × K.Proc)
      (⟨s₁', k', s₂'⟩ : W₁.Proc × K.Proc × W₂.Proc) =>
      s₁ = s₁' ∧ s₂ = s₂' ∧ k = k',
    ⟨?_⟩,
    fun ⟨⟨s₁, s₂⟩, k⟩ => ⟨⟨s₁, k, s₂⟩, rfl, rfl, rfl⟩,
    fun ⟨s₁, k, s₂⟩ => ⟨⟨⟨s₁, s₂⟩, k⟩, rfl, rfl, rfl⟩⟩
  rintro ⟨⟨s₁, s₂⟩, k⟩ ⟨s₁', k', s₂'⟩ ⟨h1, h2, h3⟩
  subst h1
  subst h2
  subst h3
  refine ⟨parLeftPathEquiv (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree,
    ?_, ?_, ?_, ?_⟩
  · -- Silence is preserved through the regrouping.
    rintro ⟨⟨b⟩, rest⟩
    simp only [IsSilentStep, PFunctor.FreeM.Displayed.Decoration.map,
      OpenProcess.mapBoundary, StepOver.mapContext]
    cases b
    · -- Context path: `⟨F, tr⟩ ↦ ⟨F, ⟨T, tr⟩⟩`.
      constructor
      · intro h
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2)))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
            BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      · intro h
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
            BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    · -- Composite paths: case on the inner coin.
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b'
      · -- Second component: `⟨T, ⟨F, tr⟩⟩ ↦ ⟨F, ⟨F, tr⟩⟩`.
        constructor
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp
                    ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp
                    ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
      · -- First component: `⟨T, ⟨T, tr⟩⟩ ↦ ⟨T, tr⟩`.
        constructor
        · intro h
          refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
  · -- Both boundary traces live over the empty boundary.
    intro tr
    exact traceList_interface_empty_eq _ _
  · -- Successors are componentwise equal after the regrouping.
    rintro ⟨⟨b⟩, rest⟩
    cases b
    · exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b' <;> exact ⟨rfl, rfl, rfl⟩
  · -- The sampled paths are related by the scheduler-transport fact.
    change R.rel
      ((fun tr => parLeftPathEquiv
          (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree tr) <$>
        TypeTree.samplePath
          (TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (W₁.step s₁).tree
              | ⟨false⟩ => (W₂.step s₂).tree
            | ⟨false⟩ => (K.step k).tree)
          (TypeTree.Sampler.interleave schedulerSampler
            (TypeTree.Sampler.interleave schedulerSampler
              (W₁.stepSampler s₁) (W₂.stepSampler s₂))
            (K.stepSampler k)))
      (TypeTree.samplePath
        (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₁.step s₁).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₂.step s₂).tree)
        (TypeTree.Sampler.interleave schedulerSampler
          (W₁.stepSampler s₁)
          (TypeTree.Sampler.interleave schedulerSampler
            (K.stepSampler k) (W₂.stepSampler s₂))))
    set e := parLeftPathEquiv
      (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree with he
    let h : ULift.{w, 0} Leaf →
        m (TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₁.step s₁).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₂.step s₂).tree)) := fun leaf =>
      match leaf with
      | ⟨.first⟩ => TypeTree.samplePath _ (W₁.stepSampler s₁) >>= fun tr =>
          pure ⟨⟨true⟩, tr⟩
      | ⟨.second⟩ => TypeTree.samplePath _ (W₂.stepSampler s₂) >>= fun tr =>
          pure ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩
      | ⟨.context⟩ => TypeTree.samplePath _ (K.stepSampler k) >>= fun tr =>
          pure ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩
    have hR : TypeTree.samplePath
        (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₁.step s₁).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₂.step s₂).tree)
        (TypeTree.Sampler.interleave schedulerSampler
          (W₁.stepSampler s₁)
          (TypeTree.Sampler.interleave schedulerSampler
            (K.stepSampler k) (W₂.stepSampler s₂))) =
        leftDraw schedulerSampler >>= h := by
      rw [leftDraw_bind]
      simp only [TypeTree.Sampler.interleave, TypeTree.samplePath]
      refine bind_congr fun b => ?_
      obtain ⟨bb⟩ := b
      cases bb
      · simp only [TypeTree.samplePath, bind_assoc, pure_bind]
        refine bind_congr fun b' => ?_
        obtain ⟨bb'⟩ := b'
        cases bb' <;> rfl
      · rfl
    have hL : (fun tr => e tr) <$>
        TypeTree.samplePath
          (TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (W₁.step s₁).tree
              | ⟨false⟩ => (W₂.step s₂).tree
            | ⟨false⟩ => (K.step k).tree)
          (TypeTree.Sampler.interleave schedulerSampler
            (TypeTree.Sampler.interleave schedulerSampler
              (W₁.stepSampler s₁) (W₂.stepSampler s₂))
            (K.stepSampler k)) =
        sourceDraw schedulerSampler >>= h := by
      rw [sourceDraw_bind]
      simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind]
      refine bind_congr fun b => ?_
      obtain ⟨bb⟩ := b
      cases bb
      · simp only [map_pure]
        rfl
      · simp only [TypeTree.samplePath, bind_assoc, map_pure, pure_bind]
        refine bind_congr fun b' => ?_
        obtain ⟨bb'⟩ := b'
        cases bb' <;> rfl
    rw [hL, hR]
    exact R.bind_congr h hσ

/-! ## Sampler-aware left wire factorization -/

open OpenProcessFactorization in
/-- Closing a wired composition factors through its left factor, up to sampler
equivalence, conditionally on the source/left scheduler-transport fact.  The
sampler-aware strengthening of
`openTheory_plug_wire_left_activation_equiv`. -/
theorem openTheory_plug_wire_left_sampler_equiv [Monad m] [LawfulMonad m]
    (R : MonadRelFamily m)
    (hσ : R.rel (sourceDraw schedulerSampler) (leftDraw schedulerSampler))
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    (W₂ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).wire W₁ W₂) K)
      ((openTheory Party m schedulerSampler).plug W₁
        ((openTheory Party m schedulerSampler).wire
          (Δ₁ := PortBoundary.swap Δ₁)
          (Γ := PortBoundary.swap Δ₂)
          (Δ₂ := PortBoundary.swap Γ)
          K
          (OpenProcess.mapBoundary
            (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom
            W₂))) := by
  refine ⟨fun (⟨⟨s₁, s₂⟩, k⟩ : (W₁.Proc × W₂.Proc) × K.Proc)
      (⟨s₁', k', s₂'⟩ : W₁.Proc × K.Proc × W₂.Proc) =>
      s₁ = s₁' ∧ s₂ = s₂' ∧ k = k',
    ⟨?_⟩,
    fun ⟨⟨s₁, s₂⟩, k⟩ => ⟨⟨s₁, k, s₂⟩, rfl, rfl, rfl⟩,
    fun ⟨s₁, k, s₂⟩ => ⟨⟨⟨s₁, s₂⟩, k⟩, rfl, rfl, rfl⟩⟩
  rintro ⟨⟨s₁, s₂⟩, k⟩ ⟨s₁', k', s₂'⟩ ⟨h1, h2, h3⟩
  subst h1
  subst h2
  subst h3
  refine ⟨parLeftPathEquiv (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree,
    ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨b⟩, rest⟩
    simp only [IsSilentStep, PFunctor.FreeM.Displayed.Decoration.map,
      OpenProcess.mapBoundary, StepOver.mapContext]
    cases b
    · -- Context path: `⟨F, tr⟩ ↦ ⟨F, ⟨T, tr⟩⟩`.
      constructor
      · intro h
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      · intro h
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b'
      · -- Second factor: `⟨T, ⟨F, tr⟩⟩ ↦ ⟨F, ⟨F, tr⟩⟩`.
        constructor
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
      · -- First factor: `⟨T, ⟨T, tr⟩⟩ ↦ ⟨T, tr⟩`.
        constructor
        · intro h
          refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro tr
    exact traceList_interface_empty_eq _ _
  · rintro ⟨⟨b⟩, rest⟩
    cases b
    · exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b' <;> exact ⟨rfl, rfl, rfl⟩
  · change R.rel
      ((fun tr => parLeftPathEquiv
          (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree tr) <$>
        TypeTree.samplePath
          (TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (W₁.step s₁).tree
              | ⟨false⟩ => (W₂.step s₂).tree
            | ⟨false⟩ => (K.step k).tree)
          (TypeTree.Sampler.interleave schedulerSampler
            (TypeTree.Sampler.interleave schedulerSampler
              (W₁.stepSampler s₁) (W₂.stepSampler s₂))
            (K.stepSampler k)))
      (TypeTree.samplePath
        (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₁.step s₁).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₂.step s₂).tree)
        (TypeTree.Sampler.interleave schedulerSampler
          (W₁.stepSampler s₁)
          (TypeTree.Sampler.interleave schedulerSampler
            (K.stepSampler k) (W₂.stepSampler s₂))))
    set e := parLeftPathEquiv
      (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree with he
    let h : ULift.{w, 0} Leaf →
        m (TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₁.step s₁).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₂.step s₂).tree)) := fun leaf =>
      match leaf with
      | ⟨.first⟩ => TypeTree.samplePath _ (W₁.stepSampler s₁) >>= fun tr =>
          pure ⟨⟨true⟩, tr⟩
      | ⟨.second⟩ => TypeTree.samplePath _ (W₂.stepSampler s₂) >>= fun tr =>
          pure ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩
      | ⟨.context⟩ => TypeTree.samplePath _ (K.stepSampler k) >>= fun tr =>
          pure ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩
    have hR : TypeTree.samplePath
        (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₁.step s₁).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₂.step s₂).tree)
        (TypeTree.Sampler.interleave schedulerSampler
          (W₁.stepSampler s₁)
          (TypeTree.Sampler.interleave schedulerSampler
            (K.stepSampler k) (W₂.stepSampler s₂))) =
        leftDraw schedulerSampler >>= h := by
      rw [leftDraw_bind]
      simp only [TypeTree.Sampler.interleave, TypeTree.samplePath]
      refine bind_congr fun b => ?_
      obtain ⟨bb⟩ := b
      cases bb
      · simp only [TypeTree.samplePath, bind_assoc, pure_bind]
        refine bind_congr fun b' => ?_
        obtain ⟨bb'⟩ := b'
        cases bb' <;> rfl
      · rfl
    have hL : (fun tr => e tr) <$>
        TypeTree.samplePath
          (TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (W₁.step s₁).tree
              | ⟨false⟩ => (W₂.step s₂).tree
            | ⟨false⟩ => (K.step k).tree)
          (TypeTree.Sampler.interleave schedulerSampler
            (TypeTree.Sampler.interleave schedulerSampler
              (W₁.stepSampler s₁) (W₂.stepSampler s₂))
            (K.stepSampler k)) =
        sourceDraw schedulerSampler >>= h := by
      rw [sourceDraw_bind]
      simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind]
      refine bind_congr fun b => ?_
      obtain ⟨bb⟩ := b
      cases bb
      · simp only [map_pure]
        rfl
      · simp only [TypeTree.samplePath, bind_assoc, map_pure, pure_bind]
        refine bind_congr fun b' => ?_
        obtain ⟨bb'⟩ := b'
        cases bb' <;> rfl
    rw [hL, hR]
    exact R.bind_congr h hσ

/-! ## Path re-encoding for the right par/wire factorizations -/

/-- Regroup the nested scheduler coins of `plug (par/wire ⋯) K` onto the
right-factored shape: the second component keeps a single `true` coin, the
first component moves under two `false` coins, and the context moves under
`false, true`. -/
def parRightPathEquiv (t₁ t₂ tk : TypeTree.{w}) :
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
        | ⟨true⟩ => t₁
        | ⟨false⟩ => t₂
      | ⟨false⟩ => tk) ≃
    TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => t₂
      | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
        | ⟨true⟩ => tk
        | ⟨false⟩ => t₁) where
  toFun := fun
    | ⟨⟨true⟩, ⟨⟨true⟩, tr⟩⟩ => ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩
    | ⟨⟨true⟩, ⟨⟨false⟩, tr⟩⟩ => ⟨⟨true⟩, tr⟩
    | ⟨⟨false⟩, tr⟩ => ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩
  invFun := fun
    | ⟨⟨true⟩, tr⟩ => ⟨⟨true⟩, ⟨⟨false⟩, tr⟩⟩
    | ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩ => ⟨⟨false⟩, tr⟩
    | ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩ => ⟨⟨true⟩, ⟨⟨true⟩, tr⟩⟩
  left_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · rfl
    · obtain ⟨⟨b'⟩, tr'⟩ := tr
      cases b' <;> rfl
  right_inv := by
    rintro ⟨⟨b⟩, tr⟩
    cases b
    · obtain ⟨⟨b'⟩, tr'⟩ := tr
      cases b' <;> rfl
    · rfl

/-! ## Sampler-aware right par factorization -/

open OpenProcessFactorization in
/-- Closing a parallel composition factors through its right component, up to
sampler equivalence, conditionally on the source/right scheduler-transport
fact.  The sampler-aware strengthening of
`openTheory_plug_par_right_activation_equiv`. -/
theorem openTheory_plug_par_right_sampler_equiv [Monad m] [LawfulMonad m]
    (R : MonadRelFamily m)
    (hσ : R.rel (sourceDraw schedulerSampler) (rightDraw schedulerSampler))
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (K : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessSamplerEquiv R
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
  refine ⟨fun (⟨⟨s₁, s₂⟩, k⟩ : (W₁.Proc × W₂.Proc) × K.Proc)
      (⟨s₂', k', s₁'⟩ : W₂.Proc × K.Proc × W₁.Proc) =>
      s₁ = s₁' ∧ s₂ = s₂' ∧ k = k',
    ⟨?_⟩,
    fun ⟨⟨s₁, s₂⟩, k⟩ => ⟨⟨s₂, k, s₁⟩, rfl, rfl, rfl⟩,
    fun ⟨s₂, k, s₁⟩ => ⟨⟨⟨s₁, s₂⟩, k⟩, rfl, rfl, rfl⟩⟩
  rintro ⟨⟨s₁, s₂⟩, k⟩ ⟨s₂', k', s₁'⟩ ⟨h1, h2, h3⟩
  subst h1
  subst h2
  subst h3
  refine ⟨parRightPathEquiv (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree,
    ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨b⟩, rest⟩
    simp only [IsSilentStep, PFunctor.FreeM.Displayed.Decoration.map,
      OpenProcess.mapBoundary, StepOver.mapContext]
    cases b
    · -- Context path: `⟨F, tr⟩ ↦ ⟨F, ⟨T, tr⟩⟩`.
      constructor
      · intro h
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
            BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
            BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      · intro h
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
            BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
            BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b'
      · -- Second component: `⟨T, ⟨F, tr⟩⟩ ↦ ⟨T, tr⟩`.
        constructor
        · intro h
          refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
      · -- First component: `⟨T, ⟨T, tr⟩⟩ ↦ ⟨F, ⟨F, tr⟩⟩`.
        constructor
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp
                    ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp
                    ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro tr
    exact traceList_interface_empty_eq _ _
  · rintro ⟨⟨b⟩, rest⟩
    cases b
    · exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b' <;> exact ⟨rfl, rfl, rfl⟩
  · change R.rel
      ((fun tr => parRightPathEquiv
          (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree tr) <$>
        TypeTree.samplePath
          (TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (W₁.step s₁).tree
              | ⟨false⟩ => (W₂.step s₂).tree
            | ⟨false⟩ => (K.step k).tree)
          (TypeTree.Sampler.interleave schedulerSampler
            (TypeTree.Sampler.interleave schedulerSampler
              (W₁.stepSampler s₁) (W₂.stepSampler s₂))
            (K.stepSampler k)))
      (TypeTree.samplePath
        (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₂.step s₂).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₁.step s₁).tree)
        (TypeTree.Sampler.interleave schedulerSampler
          (W₂.stepSampler s₂)
          (TypeTree.Sampler.interleave schedulerSampler
            (K.stepSampler k) (W₁.stepSampler s₁))))
    set e := parRightPathEquiv
      (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree with he
    let h : ULift.{w, 0} Leaf →
        m (TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₂.step s₂).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₁.step s₁).tree)) := fun leaf =>
      match leaf with
      | ⟨.first⟩ => TypeTree.samplePath _ (W₁.stepSampler s₁) >>= fun tr =>
          pure ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩
      | ⟨.second⟩ => TypeTree.samplePath _ (W₂.stepSampler s₂) >>= fun tr =>
          pure ⟨⟨true⟩, tr⟩
      | ⟨.context⟩ => TypeTree.samplePath _ (K.stepSampler k) >>= fun tr =>
          pure ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩
    have hR : TypeTree.samplePath
        (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₂.step s₂).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₁.step s₁).tree)
        (TypeTree.Sampler.interleave schedulerSampler
          (W₂.stepSampler s₂)
          (TypeTree.Sampler.interleave schedulerSampler
            (K.stepSampler k) (W₁.stepSampler s₁))) =
        rightDraw schedulerSampler >>= h := by
      rw [rightDraw_bind]
      simp only [TypeTree.Sampler.interleave, TypeTree.samplePath]
      refine bind_congr fun b => ?_
      obtain ⟨bb⟩ := b
      cases bb
      · simp only [TypeTree.samplePath, bind_assoc, pure_bind]
        refine bind_congr fun b' => ?_
        obtain ⟨bb'⟩ := b'
        cases bb' <;> rfl
      · rfl
    have hL : (fun tr => e tr) <$>
        TypeTree.samplePath
          (TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (W₁.step s₁).tree
              | ⟨false⟩ => (W₂.step s₂).tree
            | ⟨false⟩ => (K.step k).tree)
          (TypeTree.Sampler.interleave schedulerSampler
            (TypeTree.Sampler.interleave schedulerSampler
              (W₁.stepSampler s₁) (W₂.stepSampler s₂))
            (K.stepSampler k)) =
        sourceDraw schedulerSampler >>= h := by
      rw [sourceDraw_bind]
      simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind]
      refine bind_congr fun b => ?_
      obtain ⟨bb⟩ := b
      cases bb
      · simp only [map_pure]
        rfl
      · simp only [TypeTree.samplePath, bind_assoc, map_pure, pure_bind]
        refine bind_congr fun b' => ?_
        obtain ⟨bb'⟩ := b'
        cases bb' <;> rfl
    rw [hL, hR]
    exact R.bind_congr h hσ

/-! ## Sampler-aware right wire factorization -/

open OpenProcessFactorization in
/-- Closing a wired composition factors through its right factor, up to
sampler equivalence, conditionally on the source/right scheduler-transport
fact.  The sampler-aware strengthening of
`openTheory_plug_wire_right_activation_equiv`. -/
theorem openTheory_plug_wire_right_sampler_equiv [Monad m] [LawfulMonad m]
    (R : MonadRelFamily m)
    (hσ : R.rel (sourceDraw schedulerSampler) (rightDraw schedulerSampler))
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    (W₂ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessSamplerEquiv R
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
  refine ⟨fun (⟨⟨s₁, s₂⟩, k⟩ : (W₁.Proc × W₂.Proc) × K.Proc)
      (⟨s₂', k', s₁'⟩ : W₂.Proc × K.Proc × W₁.Proc) =>
      s₁ = s₁' ∧ s₂ = s₂' ∧ k = k',
    ⟨?_⟩,
    fun ⟨⟨s₁, s₂⟩, k⟩ => ⟨⟨s₂, k, s₁⟩, rfl, rfl, rfl⟩,
    fun ⟨s₂, k, s₁⟩ => ⟨⟨⟨s₁, s₂⟩, k⟩, rfl, rfl, rfl⟩⟩
  rintro ⟨⟨s₁, s₂⟩, k⟩ ⟨s₂', k', s₁'⟩ ⟨h1, h2, h3⟩
  subst h1
  subst h2
  subst h3
  refine ⟨parRightPathEquiv (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree,
    ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨b⟩, rest⟩
    simp only [IsSilentStep, PFunctor.FreeM.Displayed.Decoration.map,
      OpenProcess.mapBoundary, StepOver.mapContext]
    cases b
    · -- Context path: `⟨F, tr⟩ ↦ ⟨F, ⟨T, tr⟩⟩`.
      constructor
      · intro h
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
            BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
            BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      · intro h
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
            BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
            BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b'
      · -- Second factor: `⟨T, ⟨F, tr⟩⟩ ↦ ⟨T, tr⟩`.
        constructor
        · intro h
          refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
      · -- First factor: `⟨T, ⟨T, tr⟩⟩ ↦ ⟨F, ⟨F, tr⟩⟩`.
        constructor
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
        · intro h
          refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
          all_goals intro X ons
          · simp [OpenNodeContext.close, BoundaryAction.closed]
          · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
          · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
          · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary,
              BoundaryAction.mapBoundary]
          · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro tr
    exact traceList_interface_empty_eq _ _
  · rintro ⟨⟨b⟩, rest⟩
    cases b
    · exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨⟨b'⟩, rest'⟩ := rest
      cases b' <;> exact ⟨rfl, rfl, rfl⟩
  · change R.rel
      ((fun tr => parRightPathEquiv
          (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree tr) <$>
        TypeTree.samplePath
          (TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (W₁.step s₁).tree
              | ⟨false⟩ => (W₂.step s₂).tree
            | ⟨false⟩ => (K.step k).tree)
          (TypeTree.Sampler.interleave schedulerSampler
            (TypeTree.Sampler.interleave schedulerSampler
              (W₁.stepSampler s₁) (W₂.stepSampler s₂))
            (K.stepSampler k)))
      (TypeTree.samplePath
        (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₂.step s₂).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₁.step s₁).tree)
        (TypeTree.Sampler.interleave schedulerSampler
          (W₂.stepSampler s₂)
          (TypeTree.Sampler.interleave schedulerSampler
            (K.stepSampler k) (W₁.stepSampler s₁))))
    set e := parRightPathEquiv
      (W₁.step s₁).tree (W₂.step s₂).tree (K.step k).tree with he
    let h : ULift.{w, 0} Leaf →
        m (TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₂.step s₂).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₁.step s₁).tree)) := fun leaf =>
      match leaf with
      | ⟨.first⟩ => TypeTree.samplePath _ (W₁.stepSampler s₁) >>= fun tr =>
          pure ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩
      | ⟨.second⟩ => TypeTree.samplePath _ (W₂.stepSampler s₂) >>= fun tr =>
          pure ⟨⟨true⟩, tr⟩
      | ⟨.context⟩ => TypeTree.samplePath _ (K.stepSampler k) >>= fun tr =>
          pure ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩
    have hR : TypeTree.samplePath
        (TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => (W₂.step s₂).tree
          | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => (K.step k).tree
            | ⟨false⟩ => (W₁.step s₁).tree)
        (TypeTree.Sampler.interleave schedulerSampler
          (W₂.stepSampler s₂)
          (TypeTree.Sampler.interleave schedulerSampler
            (K.stepSampler k) (W₁.stepSampler s₁))) =
        rightDraw schedulerSampler >>= h := by
      rw [rightDraw_bind]
      simp only [TypeTree.Sampler.interleave, TypeTree.samplePath]
      refine bind_congr fun b => ?_
      obtain ⟨bb⟩ := b
      cases bb
      · simp only [TypeTree.samplePath, bind_assoc, pure_bind]
        refine bind_congr fun b' => ?_
        obtain ⟨bb'⟩ := b'
        cases bb' <;> rfl
      · rfl
    have hL : (fun tr => e tr) <$>
        TypeTree.samplePath
          (TypeTree.node (ULift.{w, 0} Bool) fun
            | ⟨true⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
              | ⟨true⟩ => (W₁.step s₁).tree
              | ⟨false⟩ => (W₂.step s₂).tree
            | ⟨false⟩ => (K.step k).tree)
          (TypeTree.Sampler.interleave schedulerSampler
            (TypeTree.Sampler.interleave schedulerSampler
              (W₁.stepSampler s₁) (W₂.stepSampler s₂))
            (K.stepSampler k)) =
        sourceDraw schedulerSampler >>= h := by
      rw [sourceDraw_bind]
      simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind]
      refine bind_congr fun b => ?_
      obtain ⟨bb⟩ := b
      cases bb
      · simp only [map_pure]
        rfl
      · simp only [TypeTree.samplePath, bind_assoc, map_pure, pure_bind]
        refine bind_congr fun b' => ?_
        obtain ⟨bb'⟩ := b'
        cases bb' <;> rfl
    rw [hL, hR]
    exact R.bind_congr h hσ

end UC
end Interaction
