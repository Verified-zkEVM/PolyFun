/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.OpenProcess
public import PolyFun.Interaction.UC.OpenProcessModel

/-!
# Plug factorization for the process model, up to activation equivalence

`OpenTheory.HasPlugWireFactor` asks that closing a `par` or `wire` composite
against a context factor through one component, with the other absorbed into
the context. The process-backed `openTheory` satisfies none of those as
equalities: each binary composition prepends its own scheduler node, so the
two sides of a factorization do not even give their step trees the same shape.

They do agree up to `OpenProcessActivationEquiv`. The regrouping only moves
`.internal` scheduler nodes, and `activationLTS` labels those silent, so the
delay bisimulation absorbs them. This file proves the four laws, which is what
lets a scheduling-insensitive observation satisfy
`Observation.RespectsFactorization` and so hand the process model the UC
composition theorems (see `OpenProcessEmulates.lean`).

## Main results

* `openTheory_plug_par_left_activation_equiv` and
  `openTheory_plug_par_right_activation_equiv`
* `openTheory_plug_wire_left_activation_equiv` and
  `openTheory_plug_wire_right_activation_equiv`

Each is a `OpenProcessActivationEquiv.of_step_match` bisimulation whose state
relation is a regrouping of the nested product of component states, and whose
four step obligations re-encode a two-bit scheduler path as a one-bit one (or
the reverse). The `_right` variants are not derived from the `_left` ones:
that would need activation equivalence to be a congruence for `plug`, which is
not currently available.
-/

public section

universe u v w w'

namespace Interaction
open PFunctor.FreeM.Displayed (Decoration)
namespace UC

open Concurrent

variable (Party : Type u)
variable (m : Type w → Type w')
variable (schedulerSampler : m (ULift.{w, 0} Bool))

/-- Closing a parallel composition factors through its left component, up to
activation equivalence: absorbing `W₂` into the context regroups the internal
scheduler nesting without changing which steps activate a party.

This is `OpenTheory.HasPlugWireFactor.plug_par_left` for the process model. The
strict equality fails — the two sides nest their scheduler nodes differently,
so the step trees do not even share a shape — but the regrouping only moves
`.internal` nodes, which `activationLTS` labels silent. -/
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
  simp only [openTheory, OpenProcess.interleave]
  refine OpenProcessActivationEquiv.of_step_match
    (fun ⟨⟨s₁, s₂⟩, k⟩ ⟨s₁', k', s₂'⟩ => s₁ = s₁' ∧ s₂ = s₂' ∧ k = k')
    (fun ⟨⟨s₁, s₂⟩, k⟩ => ⟨⟨s₁, k, s₂⟩, rfl, rfl, rfl⟩)
    (fun ⟨s₁, k, s₂⟩ => ⟨⟨⟨s₁, s₂⟩, k⟩, rfl, rfl, rfl⟩) ?_ ?_ ?_ ?_
  all_goals intro ⟨⟨s₁, s₂⟩, k⟩ ⟨s₁', k', s₂'⟩ ⟨h1, h2, h3⟩
  all_goals subst h1; subst h2; subst h3
  · intro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine .inl ⟨⟨⟨true⟩, rest'⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine .inl ⟨⟨⟨false⟩, ⟨⟨false⟩, rest'⟩⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2)))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      refine .inl ⟨⟨⟨false⟩, ⟨⟨true⟩, rest⟩⟩, ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
      refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2)))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine ⟨⟨⟨true⟩, rest'⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine ⟨⟨⟨false⟩, ⟨⟨false⟩, rest'⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      refine ⟨⟨⟨false⟩, ⟨⟨true⟩, rest⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
      · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      refine .inl ⟨⟨⟨true⟩, ⟨⟨true⟩, rest⟩⟩, ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
      refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine .inl ⟨⟨⟨false⟩, rest'⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2)))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine .inl ⟨⟨⟨true⟩, ⟨⟨false⟩, rest'⟩⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2)))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      refine ⟨⟨⟨true⟩, ⟨⟨true⟩, rest⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine ⟨⟨⟨false⟩, rest'⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2)))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine ⟨⟨⟨true⟩, ⟨⟨false⟩, rest'⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenNodeContext.close, BoundaryAction.closed]

/-- Closing a wired composition factors through its left factor, up to
activation equivalence.

This is `OpenTheory.HasPlugWireFactor.plug_wire_left` for the process model.
The argument is the same regrouping as
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
  simp only [openTheory, OpenProcess.interleave]
  refine OpenProcessActivationEquiv.of_step_match
    (fun ⟨⟨s₁, s₂⟩, k⟩ ⟨s₁', k', s₂'⟩ => s₁ = s₁' ∧ s₂ = s₂' ∧ k = k')
    (fun ⟨⟨s₁, s₂⟩, k⟩ => ⟨⟨s₁, k, s₂⟩, rfl, rfl, rfl⟩)
    (fun ⟨s₁, k, s₂⟩ => ⟨⟨⟨s₁, s₂⟩, k⟩, rfl, rfl, rfl⟩) ?_ ?_ ?_ ?_
  all_goals intro ⟨⟨s₁, s₂⟩, k⟩ ⟨s₁', k', s₂'⟩ ⟨h1, h2, h3⟩
  all_goals subst h1; subst h2; subst h3
  · intro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine .inl ⟨⟨⟨true⟩, rest'⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine .inl ⟨⟨⟨false⟩, ⟨⟨false⟩, rest'⟩⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      refine .inl ⟨⟨⟨false⟩, ⟨⟨true⟩, rest⟩⟩, ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
      refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine ⟨⟨⟨true⟩, rest'⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine ⟨⟨⟨false⟩, ⟨⟨false⟩, rest'⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      refine ⟨⟨⟨false⟩, ⟨⟨true⟩, rest⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      refine .inl ⟨⟨⟨true⟩, ⟨⟨true⟩, rest⟩⟩, ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
      refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine .inl ⟨⟨⟨false⟩, rest'⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine .inl ⟨⟨⟨true⟩, ⟨⟨false⟩, rest'⟩⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      refine ⟨⟨⟨true⟩, ⟨⟨true⟩, rest⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine ⟨⟨⟨false⟩, rest'⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine ⟨⟨⟨true⟩, ⟨⟨false⟩, rest'⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.close, BoundaryAction.closed]

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
  simp only [openTheory, OpenProcess.interleave]
  refine OpenProcessActivationEquiv.of_step_match
    (fun ⟨⟨s₁, s₂⟩, k⟩ ⟨s₂', k', s₁'⟩ => s₁ = s₁' ∧ s₂ = s₂' ∧ k = k')
    (fun ⟨⟨s₁, s₂⟩, k⟩ => ⟨⟨s₂, k, s₁⟩, rfl, rfl, rfl⟩)
    (fun ⟨s₂, k, s₁⟩ => ⟨⟨⟨s₁, s₂⟩, k⟩, rfl, rfl, rfl⟩) ?_ ?_ ?_ ?_
  all_goals intro ⟨⟨s₁, s₂⟩, k⟩ ⟨s₂', k', s₁'⟩ ⟨h1, h2, h3⟩
  all_goals subst h1; subst h2; subst h3
  · intro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine .inl ⟨⟨⟨false⟩, ⟨⟨false⟩, rest'⟩⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2)))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine .inl ⟨⟨⟨true⟩, rest'⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      refine .inl ⟨⟨⟨false⟩, ⟨⟨true⟩, rest⟩⟩, ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
      refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2))))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
      · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine ⟨⟨⟨false⟩, ⟨⟨false⟩, rest'⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine ⟨⟨⟨true⟩, rest'⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      refine ⟨⟨⟨false⟩, ⟨⟨true⟩, rest⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
      · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      refine .inl ⟨⟨⟨true⟩, ⟨⟨false⟩, rest⟩⟩, ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
      refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine .inl ⟨⟨⟨false⟩, rest'⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine .inl ⟨⟨⟨true⟩, ⟨⟨true⟩, rest'⟩⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2)))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      refine ⟨⟨⟨true⟩, ⟨⟨false⟩, rest⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine ⟨⟨⟨false⟩, rest'⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine ⟨⟨⟨true⟩, ⟨⟨true⟩, rest'⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mp
                  ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenNodeContext.close, BoundaryAction.closed]

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
  simp only [openTheory, OpenProcess.interleave]
  refine OpenProcessActivationEquiv.of_step_match
    (fun ⟨⟨s₁, s₂⟩, k⟩ ⟨s₂', k', s₁'⟩ => s₁ = s₁' ∧ s₂ = s₂' ∧ k = k')
    (fun ⟨⟨s₁, s₂⟩, k⟩ => ⟨⟨s₂, k, s₁⟩, rfl, rfl, rfl⟩)
    (fun ⟨s₂, k, s₁⟩ => ⟨⟨⟨s₁, s₂⟩, k⟩, rfl, rfl, rfl⟩) ?_ ?_ ?_ ?_
  all_goals intro ⟨⟨s₁, s₂⟩, k⟩ ⟨s₂', k', s₁'⟩ ⟨h1, h2, h3⟩
  all_goals subst h1; subst h2; subst h3
  · intro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine .inl ⟨⟨⟨false⟩, ⟨⟨false⟩, rest'⟩⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine .inl ⟨⟨⟨true⟩, rest'⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      refine .inl ⟨⟨⟨false⟩, ⟨⟨true⟩, rest⟩⟩, ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
      refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2))))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
      · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine ⟨⟨⟨false⟩, ⟨⟨false⟩, rest'⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine ⟨⟨⟨true⟩, rest'⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      refine ⟨⟨⟨false⟩, ⟨⟨true⟩, rest⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
      · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      refine .inl ⟨⟨⟨true⟩, ⟨⟨false⟩, rest⟩⟩, ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
      refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine .inl ⟨⟨⟨false⟩, rest'⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine .inl ⟨⟨⟨true⟩, ⟨⟨true⟩, rest'⟩⟩, ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at hsilent ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp hsilent.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      refine ⟨⟨⟨true⟩, ⟨⟨false⟩, rest⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
        OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
      all_goals intro X ons
      · simp [OpenNodeContext.close, BoundaryAction.closed]
      · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
      · simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine ⟨⟨⟨false⟩, rest'⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mpr
                ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.close, BoundaryAction.closed]
      | false =>
        refine ⟨⟨⟨true⟩, ⟨⟨true⟩, rest'⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, Decoration.map,
          OpenProcess.mapBoundary, StepOver.mapContext] at h ⊢
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mpr
              ((isSilentDecoration_iff_map _ ?_ _ _).mp
                ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))))⟩
        all_goals intro X ons
        · simp [OpenNodeContext.close, BoundaryAction.closed]
        · simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
        · simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
        · simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
        · simp [OpenNodeContext.close, BoundaryAction.closed]

end UC
end Interaction
