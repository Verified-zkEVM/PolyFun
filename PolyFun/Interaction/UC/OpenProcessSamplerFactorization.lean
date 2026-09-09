/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.OpenProcess
public import PolyFun.Interaction.UC.OpenProcessFactorization
public import PolyFun.Interaction.UC.OpenProcessModel
public import PolyFun.Interaction.UC.OpenProcessSamplerCoherence
public import PolyFun.Interaction.UC.OpenProcessSamplerEquiv

/-!
# Sampler-aware coherence of the open-process theory

The structural coherence laws of `openTheory` hold up to
`OpenProcessActivationEquiv`, which erases sampler effects and uses delay
matching. This module strengthens the plug laws to `OpenProcessSamplerEquiv`,
which retains sampled-path effects, **conditionally on named
scheduler-transport hypotheses**: a single shared `schedulerSampler` does not
preserve per-step scheduling distributions across reassociation, so each law
takes exactly the `MonadRelFamily` fact about reassociated scheduler draws
that it needs. `MonadRelFamily.top` discharges every such hypothesis
trivially, recovering sampler-blind strong path equivalences unconditionally.

Each law is one instance of the shapes in `OpenProcessSamplerCoherence`: after
the normalization equalities push boundary adaptation into the injections, the
composite injections of every leaf agree on both sides — everything is closed,
so only activation survives — and the scheduler nodes are internal.

`plug` commutation needs the scheduler to be `R`-fair: flipping the scheduler
coin must be invisible to the relation family
(`R.rel schedulerSampler (schedulerFlip <$> schedulerSampler)`). The
factorizations need the source-shaped draw `sourceDraw` to be related to the
left- or right-factored draw.

The activation-equivalence laws in `OpenProcessModel` and
`OpenProcessFactorization` keep their direct proofs rather than becoming
corollaries: they hold for an arbitrary `m` with no `Monad` instance, while
sampled paths — and hence this module — require `[Monad m] [LawfulMonad m]`.
-/

public section

universe u v w w'

namespace Interaction
namespace UC

open Concurrent

/-! ## The empty boundary carries no traffic -/

/-- Any two traces over the empty interface are equal: the interface has no
positions, so no packet exists and both traces are the empty word. -/
theorem traceList_interface_empty_eq
    (x y : PFunctor.TraceList Interface.empty) : x = y :=
  match x, y with
  | [], [] => rfl
  | ⟨a, _⟩ :: _, _ => a.elim
  | [], ⟨a, _⟩ :: _ => a.elim

/-! ## Scheduler draws for the factorization reassociations -/

namespace OpenProcessFactorization

/-- Draw a `Leaf` with the source-shaped coin encoding
(`sourceSchedule`): the composite is selected first, then its component. -/
@[expose]
def sourceDraw {m : Type w → Type w'} [Monad m]
    (σ : m (ULift.{w, 0} Bool)) : m (ULift.{w, 0} Leaf) :=
  nestedDrawLeft σ σ

/-- Draw a `Leaf` with the left-factored coin encoding (`leftSchedule`). -/
@[expose]
def leftDraw {m : Type w → Type w'} [Monad m]
    (σ : m (ULift.{w, 0} Bool)) : m (ULift.{w, 0} Leaf) :=
  nestedDrawFactorLeft σ σ

/-- Draw a `Leaf` with the right-factored coin encoding (`rightSchedule`). -/
@[expose]
def rightDraw {m : Type w → Type w'} [Monad m]
    (σ : m (ULift.{w, 0} Bool)) : m (ULift.{w, 0} Leaf) :=
  nestedDrawFactorRight σ σ

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
        | ⟨false⟩ => h ⟨.context⟩ :=
  nestedDrawLeft_bind σ σ h

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
            | ⟨false⟩ => h ⟨.second⟩ :=
  nestedDrawFactorLeft_bind σ σ h

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
            | ⟨false⟩ => h ⟨.first⟩ :=
  nestedDrawFactorRight_bind σ σ h

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

/-! ## Closed composites of the theory's injections

Every injection used by `openTheory` keeps the closed-world node data and the
activation flag. A closing context therefore decorates a leaf identically
whichever adaptations precede it, which is what the sampler-level shapes ask
of the two sides of a plug factorization. -/

section ClosedComposites

variable (Party : Type u)

/- The injections are unfolded only here, to check that composites agree
nodewise. Traces are compared as lists, so `FreeMonoid` and `Idx` stay
transparent to `rw` and `apply` at implicit transparency. -/
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx

attribute [local simp] TypeTree.Node.ContextHom.comp OpenNodeContext.close
  OpenNodeContext.inlTensor OpenNodeContext.inrTensor OpenNodeContext.map
  OpenNodeContext.wireLeft OpenNodeContext.wireRight OpenNodeProfile.mapBoundary
  BoundaryAction.closed BoundaryAction.embedInlTensor BoundaryAction.embedInrTensor
  BoundaryAction.mapBoundary BoundaryAction.wireLeft BoundaryAction.wireRight

theorem close_comp_inlTensor (Δ₁ Δ₂ : PortBoundary) :
    TypeTree.Node.ContextHom.comp (OpenNodeContext.close.{u, w} Party (PortBoundary.tensor Δ₁ Δ₂))
        (OpenNodeContext.inlTensor Party Δ₁ Δ₂) =
      OpenNodeContext.close Party Δ₁ := by
  funext X ons
  simp

theorem close_comp_inrTensor (Δ₁ Δ₂ : PortBoundary) :
    TypeTree.Node.ContextHom.comp (OpenNodeContext.close.{u, w} Party (PortBoundary.tensor Δ₁ Δ₂))
        (OpenNodeContext.inrTensor Party Δ₁ Δ₂) =
      OpenNodeContext.close Party Δ₂ := by
  funext X ons
  simp

theorem close_comp_wireLeft (Δ₁ Γ Δ₂ : PortBoundary) :
    TypeTree.Node.ContextHom.comp (OpenNodeContext.close.{u, w} Party (PortBoundary.tensor Δ₁ Δ₂))
        (OpenNodeContext.wireLeft Party Δ₁ Γ Δ₂) =
      OpenNodeContext.close Party (PortBoundary.tensor Δ₁ Γ) := by
  funext X ons
  simp

theorem close_comp_wireRight (Δ₁ Γ Δ₂ : PortBoundary) :
    TypeTree.Node.ContextHom.comp (OpenNodeContext.close.{u, w} Party (PortBoundary.tensor Δ₁ Δ₂))
        (OpenNodeContext.wireRight Party Δ₁ Γ Δ₂) =
      OpenNodeContext.close Party (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) := by
  funext X ons
  simp

/-- The closing context after adapting a wired pair on the left is the
closing context of the pair's left factor. -/
theorem close_comp_map_comp_wireLeft {Δ₁ Γ Δ₂ Δ : PortBoundary}
    (φ : PortBoundary.Hom (PortBoundary.tensor Δ₁ Δ₂) Δ) :
    TypeTree.Node.ContextHom.comp (OpenNodeContext.close.{u, w} Party Δ)
        (TypeTree.Node.ContextHom.comp (OpenNodeContext.map Party φ)
          (OpenNodeContext.wireLeft Party Δ₁ Γ Δ₂)) =
      OpenNodeContext.close Party (PortBoundary.tensor Δ₁ Γ) := by
  funext X ons
  simp

/-- The closing context after adapting a wired pair on the right, and the
right factor before wiring, is the closing context of that factor. -/
theorem close_comp_map_comp_wireRight_comp_map {Δ₁ Γ Δ₂ Δ Δ' : PortBoundary}
    (φ : PortBoundary.Hom (PortBoundary.tensor Δ₁ Δ₂) Δ)
    (ψ : PortBoundary.Hom Δ' (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    TypeTree.Node.ContextHom.comp (OpenNodeContext.close.{u, w} Party Δ)
        (TypeTree.Node.ContextHom.comp
          (TypeTree.Node.ContextHom.comp (OpenNodeContext.map Party φ)
            (OpenNodeContext.wireRight Party Δ₁ Γ Δ₂))
          (OpenNodeContext.map Party ψ)) =
      OpenNodeContext.close Party Δ' := by
  funext X ons
  simp

/-- The closing context after adapting a wired pair on the left, and the
left factor before wiring, is the closing context of that factor. -/
theorem close_comp_map_comp_wireLeft_comp_map {Δ₁ Γ Δ₂ Δ Δ' : PortBoundary}
    (φ : PortBoundary.Hom (PortBoundary.tensor Δ₁ Δ₂) Δ)
    (ψ : PortBoundary.Hom Δ' (PortBoundary.tensor Δ₁ Γ)) :
    TypeTree.Node.ContextHom.comp (OpenNodeContext.close.{u, w} Party Δ)
        (TypeTree.Node.ContextHom.comp
          (TypeTree.Node.ContextHom.comp (OpenNodeContext.map Party φ)
            (OpenNodeContext.wireLeft Party Δ₁ Γ Δ₂))
          (OpenNodeContext.map Party ψ)) =
      OpenNodeContext.close Party Δ' := by
  funext X ons
  simp

/-- The closing context after adapting a wired pair on the right is the
closing context of the pair's right factor. -/
theorem close_comp_map_comp_wireRight {Δ₁ Γ Δ₂ Δ : PortBoundary}
    (φ : PortBoundary.Hom (PortBoundary.tensor Δ₁ Δ₂) Δ) :
    TypeTree.Node.ContextHom.comp (OpenNodeContext.close.{u, w} Party Δ)
        (TypeTree.Node.ContextHom.comp (OpenNodeContext.map Party φ)
          (OpenNodeContext.wireRight Party Δ₁ Γ Δ₂)) =
      OpenNodeContext.close Party (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) := by
  funext X ons
  simp

/-- The closing context after wiring and adapting the right factor is the
closing context of that factor. -/
theorem close_comp_wireRight_comp_map {Δ₁ Γ Δ₂ Δ' : PortBoundary}
    (ψ : PortBoundary.Hom Δ' (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    TypeTree.Node.ContextHom.comp (OpenNodeContext.close.{u, w} Party (PortBoundary.tensor Δ₁ Δ₂))
        (TypeTree.Node.ContextHom.comp (OpenNodeContext.wireRight Party Δ₁ Γ Δ₂)
          (OpenNodeContext.map Party ψ)) =
      OpenNodeContext.close Party Δ' := by
  funext X ons
  simp

/-- The closing context after wiring and adapting the left factor is the
closing context of that factor. -/
theorem close_comp_wireLeft_comp_map {Δ₁ Γ Δ₂ Δ' : PortBoundary}
    (ψ : PortBoundary.Hom Δ' (PortBoundary.tensor Δ₁ Γ)) :
    TypeTree.Node.ContextHom.comp (OpenNodeContext.close.{u, w} Party (PortBoundary.tensor Δ₁ Δ₂))
        (TypeTree.Node.ContextHom.comp (OpenNodeContext.wireLeft Party Δ₁ Γ Δ₂)
          (OpenNodeContext.map Party ψ)) =
      OpenNodeContext.close Party Δ' := by
  funext X ons
  simp

/-! ### Tensor equivalences reindex the injections

Pushing a boundary equivalence through an injection is another injection, or a
composite of injections, because the equivalences only relabel positions. -/

theorem map_tensorComm_comp_inlTensor (Δ₁ Δ₂ : PortBoundary) :
    TypeTree.Node.ContextHom.comp
        (OpenNodeContext.map.{u, w} Party (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom)
        (OpenNodeContext.inlTensor Party Δ₁ Δ₂) =
      OpenNodeContext.inrTensor Party Δ₂ Δ₁ := by
  funext X ons
  simp only [TypeTree.Node.ContextHom.comp, Function.comp_apply, OpenNodeContext.map,
    OpenNodeProfile.mapBoundary, OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor,
    BoundaryAction.mapBoundary, OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor,
    OpenNodeProfile.mk.injEq, BoundaryAction.mk.injEq, true_and]
  rw [← PFunctor.Trace.mapChart_comp]
  refine congrArg (PFunctor.Trace.mapChart · ons.boundary.emit) ?_
  refine PFunctor.Chart.ext _ _ (fun a => ?_) (fun a => ?_)
  · rfl
  · funext b; rfl

theorem map_tensorComm_comp_inrTensor (Δ₁ Δ₂ : PortBoundary) :
    TypeTree.Node.ContextHom.comp
        (OpenNodeContext.map.{u, w} Party (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom)
        (OpenNodeContext.inrTensor Party Δ₁ Δ₂) =
      OpenNodeContext.inlTensor Party Δ₂ Δ₁ := by
  funext X ons
  simp only [TypeTree.Node.ContextHom.comp, Function.comp_apply, OpenNodeContext.map,
    OpenNodeProfile.mapBoundary, OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor,
    BoundaryAction.mapBoundary, OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor,
    OpenNodeProfile.mk.injEq, BoundaryAction.mk.injEq, true_and]
  rw [← PFunctor.Trace.mapChart_comp]
  refine congrArg (PFunctor.Trace.mapChart · ons.boundary.emit) ?_
  refine PFunctor.Chart.ext _ _ (fun a => ?_) (fun a => ?_)
  · rfl
  · funext b; rfl

theorem map_tensorAssoc_comp_inlTensor_comp_inlTensor (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    TypeTree.Node.ContextHom.comp
        (TypeTree.Node.ContextHom.comp
          (OpenNodeContext.map.{u, w} Party (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom)
          (OpenNodeContext.inlTensor Party (PortBoundary.tensor Δ₁ Δ₂) Δ₃))
        (OpenNodeContext.inlTensor Party Δ₁ Δ₂) =
      OpenNodeContext.inlTensor Party Δ₁ (PortBoundary.tensor Δ₂ Δ₃) := by
  funext X ons
  simp only [TypeTree.Node.ContextHom.comp, Function.comp_apply, OpenNodeContext.map,
    OpenNodeProfile.mapBoundary, OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor,
    BoundaryAction.mapBoundary, OpenNodeProfile.mk.injEq, BoundaryAction.mk.injEq, true_and]
  rw [← PFunctor.Trace.mapChart_comp, ← PFunctor.Trace.mapChart_comp]
  refine congrArg (PFunctor.Trace.mapChart · ons.boundary.emit) ?_
  refine PFunctor.Chart.ext _ _ (fun a => ?_) (fun a => ?_)
  · rfl
  · funext b; rfl

theorem map_tensorAssoc_comp_inlTensor_comp_inrTensor (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    TypeTree.Node.ContextHom.comp
        (TypeTree.Node.ContextHom.comp
          (OpenNodeContext.map.{u, w} Party (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom)
          (OpenNodeContext.inlTensor Party (PortBoundary.tensor Δ₁ Δ₂) Δ₃))
        (OpenNodeContext.inrTensor Party Δ₁ Δ₂) =
      TypeTree.Node.ContextHom.comp
        (OpenNodeContext.inrTensor Party Δ₁ (PortBoundary.tensor Δ₂ Δ₃))
        (OpenNodeContext.inlTensor Party Δ₂ Δ₃) := by
  funext X ons
  simp only [TypeTree.Node.ContextHom.comp, Function.comp_apply, OpenNodeContext.map,
    OpenNodeProfile.mapBoundary, OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor,
    BoundaryAction.mapBoundary, OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor,
    OpenNodeProfile.mk.injEq, BoundaryAction.mk.injEq, true_and]
  rw [← PFunctor.Trace.mapChart_comp, ← PFunctor.Trace.mapChart_comp,
    ← PFunctor.Trace.mapChart_comp]
  refine congrArg (PFunctor.Trace.mapChart · ons.boundary.emit) ?_
  refine PFunctor.Chart.ext _ _ (fun a => ?_) (fun a => ?_)
  · rfl
  · funext b; rfl

theorem map_tensorAssoc_comp_inrTensor (Δ₁ Δ₂ Δ₃ : PortBoundary) :
    TypeTree.Node.ContextHom.comp
        (OpenNodeContext.map.{u, w} Party (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom)
        (OpenNodeContext.inrTensor Party (PortBoundary.tensor Δ₁ Δ₂) Δ₃) =
      TypeTree.Node.ContextHom.comp
        (OpenNodeContext.inrTensor Party Δ₁ (PortBoundary.tensor Δ₂ Δ₃))
        (OpenNodeContext.inrTensor Party Δ₂ Δ₃) := by
  funext X ons
  simp only [TypeTree.Node.ContextHom.comp, Function.comp_apply, OpenNodeContext.map,
    OpenNodeProfile.mapBoundary, OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor,
    BoundaryAction.mapBoundary, OpenNodeProfile.mk.injEq, BoundaryAction.mk.injEq, true_and]
  rw [← PFunctor.Trace.mapChart_comp, ← PFunctor.Trace.mapChart_comp]
  refine congrArg (PFunctor.Trace.mapChart · ons.boundary.emit) ?_
  refine PFunctor.Chart.ext _ _ (fun a => ?_) (fun a => ?_)
  · rfl
  · funext b; rfl

/-- Commuting a wire's two factors turns the left wiring of the swapped right
factor into the right wiring of the original. -/
theorem map_tensorComm_comp_wireLeft_comp_map_tensorComm (Δ₁ Γ Δ₂ : PortBoundary) :
    TypeTree.Node.ContextHom.comp
        (TypeTree.Node.ContextHom.comp
          (OpenNodeContext.map.{u, w} Party (PortBoundary.Equiv.tensorComm Δ₂ Δ₁).toHom)
          (OpenNodeContext.wireLeft Party Δ₂ (PortBoundary.swap Γ) Δ₁))
        (OpenNodeContext.map Party
          (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom) =
      OpenNodeContext.wireRight Party Δ₁ Γ Δ₂ := by
  funext X ons
  simp only [TypeTree.Node.ContextHom.comp, Function.comp_apply, OpenNodeContext.map,
    OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary, OpenNodeContext.wireLeft,
    BoundaryAction.wireLeft, OpenNodeContext.wireRight, BoundaryAction.wireRight,
    OpenNodeProfile.mk.injEq, BoundaryAction.mk.injEq, true_and]
  funext x
  simp only [PFunctor.Trace.mapChart_apply, PFunctor.Trace.mapPartial_apply,
    List.filterMap_filterMap]
  apply List.filterMap_congr
  rintro ⟨(_ | _), _⟩ _ <;> rfl

/-- Commuting a wire's two factors turns the right wiring of the swapped left
factor into the left wiring of the original. -/
theorem map_tensorComm_comp_wireRight_comp_map_tensorComm (Δ₁ Γ Δ₂ : PortBoundary) :
    TypeTree.Node.ContextHom.comp
        (TypeTree.Node.ContextHom.comp
          (OpenNodeContext.map.{u, w} Party (PortBoundary.Equiv.tensorComm Δ₂ Δ₁).toHom)
          (OpenNodeContext.wireRight Party Δ₂ (PortBoundary.swap Γ) Δ₁))
        (OpenNodeContext.map Party (PortBoundary.Equiv.tensorComm Δ₁ Γ).toHom) =
      OpenNodeContext.wireLeft Party Δ₁ Γ Δ₂ := by
  funext X ons
  simp only [TypeTree.Node.ContextHom.comp, Function.comp_apply, OpenNodeContext.map,
    OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary, OpenNodeContext.wireLeft,
    BoundaryAction.wireLeft, OpenNodeContext.wireRight, BoundaryAction.wireRight,
    OpenNodeProfile.mk.injEq, BoundaryAction.mk.injEq, true_and]
  funext x
  simp only [PFunctor.Trace.mapChart_apply, PFunctor.Trace.mapPartial_apply,
    List.filterMap_filterMap]
  apply List.filterMap_congr
  rintro ⟨(_ | _), _⟩ _ <;> rfl

end ClosedComposites

/-- The scheduler node is internal. -/
theorem isInternalNode_schedulerNode (Party : Type u) (Δ : PortBoundary) :
    OpenNodeContext.IsInternalNode (schedulerNode.{u, w} Party Δ) :=
  rfl

variable (Party : Type u) (m : Type w → Type w')
  (schedulerSampler : m (ULift.{w, 0} Bool))

open OpenProcessFactorization

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
  simp only [openTheory]
  exact interleave_comm_samplerEquiv R W K schedulerSampler schedulerSampler
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _) (R.symm hfair)

/-! ## Sampler-aware left factorizations -/

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
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave, OpenProcess.mapBoundary_eq_mapHom,
    OpenProcess.interleave_mapHom_right]
  exact interleave_factorLeft_samplerEquiv R W₁ W₂ K schedulerSampler schedulerSampler
    schedulerSampler schedulerSampler
    (close_comp_inlTensor Party Δ₁ Δ₂)
    ((close_comp_inrTensor Party Δ₁ Δ₂).trans
      (close_comp_map_comp_wireRight_comp_map Party (Δ₁ := PortBoundary.swap Δ₁)
        (Γ := PortBoundary.swap Δ₂) (Δ₂ := PortBoundary.empty) _ _).symm)
    (close_comp_map_comp_wireLeft Party (Δ₁ := PortBoundary.swap Δ₁) (Γ := PortBoundary.swap Δ₂)
      (Δ₂ := PortBoundary.empty) _).symm
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _).close
    (isInternalNode_schedulerNode Party _)
    ((isInternalNode_schedulerNode Party _).map _).close hσ

/-- Closing a wired composition factors through its left factor, up to
sampler equivalence, conditionally on the same scheduler-transport fact as the
parallel case. -/
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
            (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom W₂))) := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_eq_mapHom, OpenProcess.interleave_mapHom_right]
  exact interleave_factorLeft_samplerEquiv R W₁ W₂ K schedulerSampler schedulerSampler
    schedulerSampler schedulerSampler
    (close_comp_wireLeft Party Δ₁ Γ Δ₂)
    ((close_comp_wireRight Party Δ₁ Γ Δ₂).trans
      (close_comp_wireRight_comp_map Party (Δ₁ := PortBoundary.swap Δ₁)
        (Γ := PortBoundary.swap Δ₂) (Δ₂ := PortBoundary.swap Γ) _).symm)
    (close_comp_wireLeft Party (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)
      (PortBoundary.swap Γ)).symm
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _).close
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _).close hσ

/-! ## Sampler-aware right factorizations -/

/-- Closing a parallel composition factors through its right component, up to
sampler equivalence, conditionally on the scheduler-transport fact
`R.rel (sourceDraw schedulerSampler) (rightDraw schedulerSampler)`. The
mirror of `openTheory_plug_par_left_sampler_equiv`. -/
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
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave]
  simp only [OpenProcess.mapBoundary_eq_mapHom]
  rw [OpenProcess.interleave_mapHom_left, OpenProcess.interleave_mapHom_right]
  exact interleave_factorRight_samplerEquiv R W₁ W₂ K schedulerSampler schedulerSampler
    schedulerSampler schedulerSampler
    ((close_comp_inlTensor Party Δ₁ Δ₂).trans
      (close_comp_map_comp_wireRight_comp_map Party (Δ₁ := PortBoundary.swap Δ₂)
        (Γ := PortBoundary.swap Δ₁) (Δ₂ := PortBoundary.empty) _ _).symm)
    (close_comp_inrTensor Party Δ₁ Δ₂)
    (close_comp_map_comp_wireLeft_comp_map Party (Δ₁ := PortBoundary.swap Δ₂)
      (Γ := PortBoundary.swap Δ₁) (Δ₂ := PortBoundary.empty)
      (Δ' := PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) _ _).symm
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _).close
    (isInternalNode_schedulerNode Party _)
    ((isInternalNode_schedulerNode Party _).map _).close hσ

/-- Closing a wired composition factors through its right factor, up to
sampler equivalence, conditionally on the same scheduler-transport fact as the
parallel case. The mirror of `openTheory_plug_wire_left_sampler_equiv`. -/
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
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave, OpenProcess.mapBoundary_eq_mapHom,
    OpenProcess.interleave_mapHom_left]
  exact interleave_factorRight_samplerEquiv R W₁ W₂ K schedulerSampler schedulerSampler
    schedulerSampler schedulerSampler
    ((close_comp_wireLeft Party Δ₁ Γ Δ₂).trans
      (close_comp_map_comp_wireRight Party (Δ₁ := PortBoundary.swap Δ₂)
        (Γ := PortBoundary.swap Δ₁) (Δ₂ := Γ) _).symm)
    (close_comp_wireRight Party Δ₁ Γ Δ₂)
    (close_comp_map_comp_wireLeft_comp_map Party (Δ₁ := PortBoundary.swap Δ₂)
      (Γ := PortBoundary.swap Δ₁) (Δ₂ := Γ)
      (Δ' := PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) _ _).symm
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _).close
    (isInternalNode_schedulerNode Party _)
    ((isInternalNode_schedulerNode Party _).map _).close hσ

/-! ## Sampler-aware monoidal laws

The open laws move packets across the tensor equivalences, so their leaves are
decorated by reindexed injections; the reindexing lemmas above make the two
sides' composite injections equal. -/

/-- Parallel composition is commutative up to sampler equivalence, provided
the scheduler is `R`-fair. -/
theorem openTheory_par_comm_sampler_equiv [Monad m] [LawfulMonad m]
    (R : MonadRelFamily m)
    (hfair : R.rel schedulerSampler (schedulerFlip <$> schedulerSampler))
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂) :
    OpenProcessSamplerEquiv R
      (OpenProcess.mapBoundary (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom
        ((openTheory Party m schedulerSampler).par W₁ W₂))
      ((openTheory Party m schedulerSampler).par W₂ W₁) := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave, map_tensorComm_comp_inlTensor,
    map_tensorComm_comp_inrTensor]
  exact interleave_comm_samplerEquiv R W₁ W₂ schedulerSampler schedulerSampler
    ((isInternalNode_schedulerNode Party _).map _) (isInternalNode_schedulerNode Party _)
    (R.symm hfair)

/-- Parallel composition is associative up to sampler equivalence, provided
the scheduler is `R`-fair, the left-factored transport fact holds, and `R` is
bind-congruent: the left factorization followed by commutation of the inner
pair. -/
theorem openTheory_par_assoc_sampler_equiv [Monad m] [LawfulMonad m]
    (R : MonadRelFamily m) [R.IsBindCongr]
    (hfair : R.rel schedulerSampler (schedulerFlip <$> schedulerSampler))
    (hσ : R.rel (sourceDraw schedulerSampler) (leftDraw schedulerSampler))
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (W₃ : OpenProcess.{u, v, w, w'} m Party Δ₃) :
    OpenProcessSamplerEquiv R
      (OpenProcess.mapBoundary (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom
        ((openTheory Party m schedulerSampler).par
          ((openTheory Party m schedulerSampler).par W₁ W₂) W₃))
      ((openTheory Party m schedulerSampler).par W₁
        ((openTheory Party m schedulerSampler).par W₂ W₃)) := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave]
  exact interleave_assoc_samplerEquiv R W₁ W₂ W₃ schedulerSampler schedulerSampler
    schedulerSampler schedulerSampler schedulerSampler
    (map_tensorAssoc_comp_inlTensor_comp_inlTensor Party Δ₁ Δ₂ Δ₃)
    (map_tensorAssoc_comp_inlTensor_comp_inrTensor Party Δ₁ Δ₂ Δ₃)
    (map_tensorAssoc_comp_inrTensor Party Δ₁ Δ₂ Δ₃)
    ((isInternalNode_schedulerNode Party _).map _)
    (((isInternalNode_schedulerNode Party _).inlTensor _).map _)
    (isInternalNode_schedulerNode Party _) (isInternalNode_schedulerNode Party _)
    ((isInternalNode_schedulerNode Party _).inrTensor _)
    (OpenNodeContext.preservesActivation_inrTensor Δ₁ _)
    (OpenNodeContext.emitsAlong_inrTensor Δ₁ _) hσ (R.symm hfair)

/-- Wiring is commutative up to sampler equivalence and boundary reshaping,
provided the scheduler is `R`-fair. -/
theorem openTheory_wire_comm_sampler_equiv [Monad m] [LawfulMonad m]
    (R : MonadRelFamily m)
    (hfair : R.rel schedulerSampler (schedulerFlip <$> schedulerSampler))
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    (W₂ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).wire W₁ W₂)
      (OpenProcess.mapBoundary (PortBoundary.Equiv.tensorComm Δ₂ Δ₁).toHom
        ((openTheory Party m schedulerSampler).wire
          (OpenProcess.mapBoundary
            (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom W₂)
          (OpenProcess.mapBoundary (PortBoundary.Equiv.tensorComm Δ₁ Γ).toHom W₁))) := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave]
  simp only [OpenProcess.mapBoundary_eq_mapHom]
  rw [OpenProcess.interleave_mapHom_left, OpenProcess.interleave_mapHom_right,
    map_tensorComm_comp_wireLeft_comp_map_tensorComm,
    map_tensorComm_comp_wireRight_comp_map_tensorComm]
  exact interleave_comm_samplerEquiv R W₁ W₂ schedulerSampler schedulerSampler
    (isInternalNode_schedulerNode Party _) ((isInternalNode_schedulerNode Party _).map _)
    (R.symm hfair)

/-! ## Sampler equivalence is a congruence for the theory

Given the relation family is a congruence for the continuation of `bind`
(`MonadRelFamily.IsBindCongr`), each operation of `openTheory` preserves
sampler equivalence in each argument: every injection preserves activation and
relabels traces. -/

section Congruence

variable [Monad m] [LawfulMonad m] (R : MonadRelFamily m) [R.IsBindCongr]

open OpenNodeContext

omit [LawfulMonad m] [R.IsBindCongr] in
theorem openTheory_map_congr_sampler_equiv {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂) {W W' : OpenProcess.{u, v, w, w'} m Party Δ₁}
    (h : OpenProcessSamplerEquiv R W W') :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).map φ W)
      ((openTheory Party m schedulerSampler).map φ W') := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_eq_mapHom, OpenProcess.mapBoundary_eq_mapHom]
  exact OpenProcess.mapHom_congr_samplerEquiv R (preservesActivation_map φ) (emitsAlong_map φ) h

theorem openTheory_par_congr_left_sampler_equiv {Δ₁ Δ₂ : PortBoundary}
    {W₁ W₁' : OpenProcess.{u, v, w, w'} m Party Δ₁} (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (h : OpenProcessSamplerEquiv R W₁ W₁') :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).par W₁ W₂)
      ((openTheory Party m schedulerSampler).par W₁' W₂) := by
  simp only [openTheory]
  exact OpenProcess.interleave_congr_left_samplerEquiv R W₁ W₂
    (preservesActivation_inlTensor Δ₁ Δ₂) (emitsAlong_inlTensor Δ₁ Δ₂) schedulerSampler h

theorem openTheory_par_congr_right_sampler_equiv {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) {W₂ W₂' : OpenProcess.{u, v, w, w'} m Party Δ₂}
    (h : OpenProcessSamplerEquiv R W₂ W₂') :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).par W₁ W₂)
      ((openTheory Party m schedulerSampler).par W₁ W₂') := by
  simp only [openTheory]
  exact OpenProcess.interleave_congr_right_samplerEquiv R W₁ W₂
    (preservesActivation_inrTensor Δ₁ Δ₂) (emitsAlong_inrTensor Δ₁ Δ₂) schedulerSampler h

theorem openTheory_wire_congr_left_sampler_equiv {Δ₁ Γ Δ₂ : PortBoundary}
    {W₁ W₁' : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ)}
    (W₂ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (h : OpenProcessSamplerEquiv R W₁ W₁') :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).wire W₁ W₂)
      ((openTheory Party m schedulerSampler).wire W₁' W₂) := by
  simp only [openTheory]
  exact OpenProcess.interleave_congr_left_samplerEquiv R W₁ W₂
    (preservesActivation_wireLeft Δ₁ Γ Δ₂) (emitsAlong_wireLeft Δ₁ Γ Δ₂) schedulerSampler h

theorem openTheory_wire_congr_right_sampler_equiv {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    {W₂ W₂' : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h : OpenProcessSamplerEquiv R W₂ W₂') :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).wire W₁ W₂)
      ((openTheory Party m schedulerSampler).wire W₁ W₂') := by
  simp only [openTheory]
  exact OpenProcess.interleave_congr_right_samplerEquiv R W₁ W₂
    (preservesActivation_wireRight Δ₁ Γ Δ₂) (emitsAlong_wireRight Δ₁ Γ Δ₂) schedulerSampler h

theorem openTheory_plug_congr_left_sampler_equiv {Δ : PortBoundary}
    {W W' : OpenProcess.{u, v, w, w'} m Party Δ}
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ))
    (h : OpenProcessSamplerEquiv R W W') :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).plug W K)
      ((openTheory Party m schedulerSampler).plug W' K) := by
  simp only [openTheory]
  exact OpenProcess.interleave_congr_left_samplerEquiv R W K
    (preservesActivation_close Δ) (emitsAlong_close Δ) schedulerSampler h

theorem openTheory_plug_congr_right_sampler_equiv {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w, w'} m Party Δ)
    {K K' : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ)}
    (h : OpenProcessSamplerEquiv R K K') :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).plug W K)
      ((openTheory Party m schedulerSampler).plug W K') := by
  simp only [openTheory]
  exact OpenProcess.interleave_congr_right_samplerEquiv R W K
    (preservesActivation_close _) (emitsAlong_close _) schedulerSampler h

end Congruence

end UC
end Interaction
