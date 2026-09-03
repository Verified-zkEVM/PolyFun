/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all PolyFun.Interaction.UC.OpenProcess
public import PolyFun.Interaction.UC.OpenProcess
public import PolyFun.Interaction.UC.OpenProcessCoherence
public import PolyFun.Interaction.UC.OpenProcessInterleave
public import PolyFun.Interaction.UC.OpenTheory

/-!
# Concrete `OpenTheory` model backed by `OpenProcess m`

This file provides the first concrete realization of `UC.OpenTheory`
using actual open processes (`OpenProcess m Party Δ`), i.e., processes
that carry a per-step nodewise-monadic sampler in the intermediate monad
`m`.

## Implemented operations

* `map` adapts boundary actions along a `PortBoundary.Hom`, with a proven
  `IsLawfulMap` instance (functoriality). The per-step sampler is left
  unchanged; only the boundary-action decoration is pushed forward.

* `par` places two open processes side by side using binary-choice
  interleaving: a scheduling node chooses left or right, then runs the
  selected subprocess's step protocol. Emitted packets are injected into
  the appropriate summand of the tensor output interface. The scheduler
  move is resolved by the theory's shared `schedulerSampler : m (ULift
  Bool)`; per-branch samplers are assembled via
  `TypeTree.Sampler.interleave`.

* `wire` connects a shared internal boundary between two processes.
  Packets on the shared boundary are filtered out (deferred to runtime
  routing), while packets on the remaining external boundaries are
  preserved. Samplers are threaded the same way as for `par`.

* `plug` closes an open system against a matching context by
  internalizing all boundary traffic. Samplers are again threaded via
  the scheduler-interleaving pattern.

## Laws up to activation equivalence

The model is `IsLawful` strictly. The monoidal, traced, and compact closed
laws hold up to `OpenProcessActivationEquiv`, each as one instance of the
coherence shapes in `OpenProcessCoherence` (reassociation, commutation,
re-homing, unit absorption) after the normalization equalities push boundary
adaptation into the injections.
-/

public section

universe u v w w'

namespace Interaction
open PFunctor.FreeM.Displayed (Decoration)
namespace UC

open Concurrent

section Model

variable (Party : Type u)
variable (m : Type w → Type w')
variable (schedulerSampler : m (ULift.{w, 0} Bool))

/-- The canonical internal scheduler node shared by `par`, `wire`, and `plug`. -/
@[expose]
def schedulerNode (Δ : PortBoundary) :
    OpenNodeProfile.{u, w} Party Δ (ULift.{w, 0} Bool) where
  controllers := fun _ => []
  views := fun _ => .hidden
  boundary := .internal Δ _

/--
The concrete open-composition theory backed by `OpenProcess m`.

* `Obj Δ` is `OpenProcess m Party Δ`, the boundary-indexed family of
  open concurrent processes carrying per-step `m`-samplers.
* `map` adapts boundary actions along a `PortBoundary.Hom`, preserving
  samplers verbatim.
* `par`, `wire`, and `plug` all use `OpenProcess.interleave` with the
  appropriate context morphisms and thread the shared `schedulerSampler`
  through `TypeTree.Sampler.interleave`.
-/
@[expose]
def openTheory : OpenTheory where
  Obj Δ := OpenProcess.{u, v, w, w'} m Party Δ
  map φ p := p.mapBoundary φ
  par {Δ₁} {Δ₂} p₁ p₂ :=
    p₁.interleave p₂
      (OpenNodeContext.inlTensor Party Δ₁ Δ₂)
      (OpenNodeContext.inrTensor Party Δ₁ Δ₂)
      (schedulerNode Party (PortBoundary.tensor Δ₁ Δ₂))
      schedulerSampler
  wire {Δ₁} {Γ} {Δ₂} p₁ p₂ :=
    p₁.interleave p₂
      (OpenNodeContext.wireLeft Party Δ₁ Γ Δ₂)
      (OpenNodeContext.wireRight Party Δ₁ Γ Δ₂)
      (schedulerNode Party (PortBoundary.tensor Δ₁ Δ₂))
      schedulerSampler
  plug {Δ} p k :=
    p.interleave k
      (OpenNodeContext.close Party Δ)
      (OpenNodeContext.close Party (PortBoundary.swap Δ))
      (schedulerNode Party PortBoundary.empty)
      schedulerSampler

instance lawfulMap_openTheory :
    OpenTheory.IsLawfulMap (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  map_id {Δ} W := by
    change W.mapBoundary (PortBoundary.Hom.id Δ) = W
    simp only [OpenProcess.mapBoundary]
    rw [OpenNodeContext.map_id]
    cases W with | mk Proc step stepSampler =>
    congr 1
    funext s
    simp only [StepOver.mapContext]
    exact congrArg₂ (StepOver.mk _)
      (PFunctor.FreeM.Displayed.Decoration.map_id _ _) rfl
  map_comp {Δ₁} {Δ₂} {Δ₃} g f W := by
    change W.mapBoundary (PortBoundary.Hom.comp g f) =
      (W.mapBoundary f).mapBoundary g
    simp only [OpenProcess.mapBoundary]
    rw [← OpenNodeContext.map_comp]
    cases W with | mk Proc step stepSampler =>
    congr 1
    funext s
    simp only [StepOver.mapContext]
    exact congrArg₂ (StepOver.mk _)
      (PFunctor.FreeM.Displayed.Decoration.map_comp _ _ _ _).symm rfl

instance lawfulPar_openTheory :
    OpenTheory.IsLawfulPar (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  __ := lawfulMap_openTheory Party m schedulerSampler
  map_par {Δ₁} {Δ₁'} {Δ₂} {Δ₂'} f₁ f₂ W₁ W₂ := by
    change OpenProcess.mapBoundary (PortBoundary.Hom.tensor f₁ f₂)
        (W₁.interleave W₂ _ _ _ schedulerSampler) =
      (OpenProcess.mapBoundary f₁ W₁).interleave
        (OpenProcess.mapBoundary f₂ W₂) _ _ _ schedulerSampler
    -- The structural content lives at the `ProcessOver` layer: pushing a
    -- tensor-boundary map across `interleave` matches mapping each side
    -- first, using `map_tensor_comp_inlTensor`/`inrTensor` on the
    -- injections. The scheduler argument closes definitionally because
    -- boundary-mapping a purely internal node preserves the `.internal`
    -- tag (the trace-monoid unit `1` is fixed by `PFunctor.Trace.mapChart`).
    have hproc :
        (W₁.toProcess.interleave W₂.toProcess
            (OpenNodeContext.inlTensor Party Δ₁ Δ₂)
            (OpenNodeContext.inrTensor Party Δ₁ Δ₂)
            (schedulerNode Party (PortBoundary.tensor Δ₁ Δ₂))).mapContext
              (OpenNodeContext.map Party (PortBoundary.Hom.tensor f₁ f₂)) =
          (W₁.toProcess.mapContext (OpenNodeContext.map Party f₁)).interleave
            (W₂.toProcess.mapContext (OpenNodeContext.map Party f₂))
            (OpenNodeContext.inlTensor Party Δ₁' Δ₂')
            (OpenNodeContext.inrTensor Party Δ₁' Δ₂')
            (schedulerNode Party (PortBoundary.tensor Δ₁' Δ₂')) := by
      rw [ProcessOver.mapContext_interleave, ProcessOver.interleave_mapContext,
        OpenNodeContext.map_tensor_comp_inlTensor,
        OpenNodeContext.map_tensor_comp_inrTensor]
      congr 1
    -- Lift to the `OpenProcess` equality: `Proc` is `Proc₁ × Proc₂` on
    -- both sides; `step` is the `.step` of each side of `hproc` (defeq);
    -- `stepSampler` is `Sampler.interleave schedulerSampler ...`, same
    -- term on both sides (since `mapBoundary` preserves `stepSampler`).
    cases W₁ with | mk Proc₁ step₁ stepSampler₁ =>
    cases W₂ with | mk Proc₂ step₂ stepSampler₂ =>
    simp only [OpenProcess.mapBoundary, OpenProcess.interleave]
    exact OpenProcess.ext_of_step_eq
      (eq_of_heq (OpenProcess.heq_step_of_processOver_eq hproc)) HEq.rfl

instance lawfulWire_openTheory :
    OpenTheory.IsLawfulWire (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  __ := lawfulMap_openTheory Party m schedulerSampler
  map_wire {Δ₁} {Δ₁'} {Γ} {Δ₂} {Δ₂'} f₁ f₂ W₁ W₂ := by
    change OpenProcess.mapBoundary (PortBoundary.Hom.tensor f₁ f₂)
        (W₁.interleave W₂ _ _ _ schedulerSampler) =
      (OpenProcess.mapBoundary
        (PortBoundary.Hom.tensor f₁ (PortBoundary.Hom.id Γ)) W₁).interleave
        (OpenProcess.mapBoundary (PortBoundary.Hom.tensor
          (PortBoundary.Hom.id (PortBoundary.swap Γ)) f₂) W₂) _ _ _
        schedulerSampler
    -- Same pattern as `map_par`, with the wire injections carrying the
    -- shared boundary `Γ` as a fixed axis: `map_tensor_comp_wireLeft`
    -- transports `f₁` past the left injection, and `map_tensor_comp_wireRight`
    -- transports `f₂` past the right injection.
    have hproc :
        (W₁.toProcess.interleave W₂.toProcess
            (OpenNodeContext.wireLeft Party Δ₁ Γ Δ₂)
            (OpenNodeContext.wireRight Party Δ₁ Γ Δ₂)
            (schedulerNode Party (PortBoundary.tensor Δ₁ Δ₂))).mapContext
              (OpenNodeContext.map Party (PortBoundary.Hom.tensor f₁ f₂)) =
          (W₁.toProcess.mapContext
              (OpenNodeContext.map Party
                (PortBoundary.Hom.tensor f₁ (PortBoundary.Hom.id Γ)))).interleave
            (W₂.toProcess.mapContext
              (OpenNodeContext.map Party
                (PortBoundary.Hom.tensor
                  (PortBoundary.Hom.id (PortBoundary.swap Γ)) f₂)))
            (OpenNodeContext.wireLeft Party Δ₁' Γ Δ₂')
            (OpenNodeContext.wireRight Party Δ₁' Γ Δ₂')
            (schedulerNode Party (PortBoundary.tensor Δ₁' Δ₂')) := by
      rw [ProcessOver.mapContext_interleave, ProcessOver.interleave_mapContext,
        OpenNodeContext.map_tensor_comp_wireLeft,
        OpenNodeContext.map_tensor_comp_wireRight]
      congr 1
    cases W₁ with | mk Proc₁ step₁ stepSampler₁ =>
    cases W₂ with | mk Proc₂ step₂ stepSampler₂ =>
    simp only [OpenProcess.mapBoundary, OpenProcess.interleave]
    exact OpenProcess.ext_of_step_eq
      (eq_of_heq (OpenProcess.heq_step_of_processOver_eq hproc)) HEq.rfl

instance lawfulPlug_openTheory :
    OpenTheory.IsLawfulPlug (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  __ := lawfulMap_openTheory Party m schedulerSampler
  map_plug {Δ₁} {Δ₂} f W K := by
    change (OpenProcess.mapBoundary f W).interleave K _ _ _ schedulerSampler =
      W.interleave (OpenProcess.mapBoundary (PortBoundary.Hom.swap f) K) _ _ _
        schedulerSampler
    -- Only one side is boundary-mapped on each inequation: on the LHS, `W`
    -- carries `map Party f`, absorbed by `close Party Δ₂` via `close_comp_map`;
    -- on the RHS, `K` carries `map Party (swap f)`, absorbed by
    -- `close Party (swap Δ₁)` via the same lemma applied to `swap f`.
    have hproc :
        (W.toProcess.mapContext (OpenNodeContext.map Party f)).interleave K.toProcess
            (OpenNodeContext.close Party Δ₂)
            (OpenNodeContext.close Party (PortBoundary.swap Δ₂))
            (schedulerNode Party PortBoundary.empty) =
          W.toProcess.interleave
            (K.toProcess.mapContext
              (OpenNodeContext.map Party (PortBoundary.Hom.swap f)))
            (OpenNodeContext.close Party Δ₁)
            (OpenNodeContext.close Party (PortBoundary.swap Δ₁))
            (schedulerNode Party PortBoundary.empty) := by
      rw [ProcessOver.interleave_mapContext_left,
        ProcessOver.interleave_mapContext_right,
        OpenNodeContext.close_comp_map, OpenNodeContext.close_comp_map]
    cases W with | mk ProcW stepW stepSamplerW =>
    cases K with | mk ProcK stepK stepSamplerK =>
    simp only [OpenProcess.mapBoundary, OpenProcess.interleave]
    exact OpenProcess.ext_of_step_eq
      (eq_of_heq (OpenProcess.heq_step_of_processOver_eq hproc)) HEq.rfl

instance : OpenTheory.IsLawful (openTheory.{u, v, w, w'} Party m schedulerSampler) where

/-! ## Monoidal, traced, and compact closed laws up to activation equivalence

Every law below is an instance of the coherence shapes in
`OpenProcessCoherence`: `simp only [openTheory]` exposes the nesting of
`interleave`s, the normalization equalities `mapBoundary_interleave` and
`interleave_mapHom_{left,right}` push boundary adaptation into the injections,
and one of reassociation, commutation, re-homing, or unit absorption closes the
goal. The scheduler nodes are silent by construction and every injection the
theory uses preserves activation. -/

open OpenNodeContext (preservesActivation_map preservesActivation_inlTensor
  preservesActivation_inrTensor preservesActivation_wireLeft preservesActivation_wireRight
  preservesActivation_close)

/-- The scheduler node is never externally activated. -/
theorem schedulerNode_isActivated (Δ : PortBoundary) :
    (schedulerNode Party Δ).boundary.isActivated = false := rfl

/-- Boundary adaptation keeps the scheduler node silent. -/
theorem map_schedulerNode_isActivated {Δ Δ' : PortBoundary} (φ : PortBoundary.Hom Δ Δ') :
    (OpenNodeContext.map.{u, w} Party φ _ (schedulerNode Party Δ)).boundary.isActivated =
      false :=
  (OpenNodeContext.preservesActivation_map φ _ _).trans (schedulerNode_isActivated Party Δ)

/-- Parallel composition of open processes is associative up to activation
equivalence: reassociating the internal scheduler nesting preserves the same
coarse scheduler/activation structure. -/
theorem openTheory_par_assoc_activation_equiv
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
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
  rw [OpenProcess.mapBoundary_interleave]
  exact interleave_assoc_activationEquiv W₁ W₂ W₃ schedulerSampler schedulerSampler
    schedulerSampler schedulerSampler
    (preservesActivation_inlTensor Δ₁ Δ₂) (preservesActivation_inrTensor Δ₁ Δ₂)
    ((preservesActivation_map _).comp (preservesActivation_inlTensor _ Δ₃))
    ((preservesActivation_map _).comp (preservesActivation_inrTensor _ Δ₃))
    (preservesActivation_inlTensor Δ₂ Δ₃) (preservesActivation_inrTensor Δ₂ Δ₃)
    (preservesActivation_inlTensor Δ₁ _) (preservesActivation_inrTensor Δ₁ _)
    (schedulerNode_isActivated Party _) (map_schedulerNode_isActivated Party _)
    (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _)

/-- Parallel composition is commutative up to activation equivalence: swapping
the two components (and relabeling the scheduler's branch choice) preserves
the coarse scheduler/activation structure. -/
theorem openTheory_par_comm_activation_equiv
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂) :
    OpenProcessActivationEquiv
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom
        ((openTheory Party m schedulerSampler).par W₁ W₂))
      ((openTheory Party m schedulerSampler).par W₂ W₁) := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave]
  exact interleave_comm_activationEquiv W₁ W₂ schedulerSampler schedulerSampler
    ((preservesActivation_map _).comp (preservesActivation_inlTensor Δ₁ Δ₂))
    ((preservesActivation_map _).comp (preservesActivation_inrTensor Δ₁ Δ₂))
    (preservesActivation_inlTensor Δ₂ Δ₁) (preservesActivation_inrTensor Δ₂ Δ₁)
    (map_schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _)

/-- Plugging is commutative up to activation equivalence: closing `W` against
`K` and closing `K` against `W` are the same interleaving with the scheduler's
branch choice relabeled. -/
theorem openTheory_plug_comm_activation_equiv
    {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w, w'} m Party Δ)
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ)) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).plug W K)
      ((openTheory Party m schedulerSampler).plug K W) := by
  simp only [openTheory]
  exact interleave_comm_activationEquiv W K schedulerSampler schedulerSampler
    (preservesActivation_close Δ) (preservesActivation_close _)
    (preservesActivation_close _) (preservesActivation_close _)
    (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _)

/-- Sequential wiring is associative up to activation equivalence. -/
theorem openTheory_wire_assoc_activation_equiv
    {Δ₁ Γ₁ Γ₂ Δ₃ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ₁))
    (W₂ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ₁) Γ₂))
    (W₃ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ₂) Δ₃)) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).wire
        ((openTheory Party m schedulerSampler).wire W₁ W₂) W₃)
      ((openTheory Party m schedulerSampler).wire W₁
        ((openTheory Party m schedulerSampler).wire W₂ W₃)) := by
  simp only [openTheory]
  exact interleave_assoc_activationEquiv W₁ W₂ W₃ schedulerSampler schedulerSampler
    schedulerSampler schedulerSampler
    (preservesActivation_wireLeft Δ₁ Γ₁ Γ₂) (preservesActivation_wireRight Δ₁ Γ₁ Γ₂)
    (preservesActivation_wireLeft Δ₁ Γ₂ Δ₃) (preservesActivation_wireRight Δ₁ Γ₂ Δ₃)
    (preservesActivation_wireLeft _ Γ₂ Δ₃) (preservesActivation_wireRight _ Γ₂ Δ₃)
    (preservesActivation_wireLeft Δ₁ Γ₁ Δ₃) (preservesActivation_wireRight Δ₁ Γ₁ Δ₃)
    (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _)
    (schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _)

/-- A parallel factor that does not touch the wired boundary can be moved out
of the wire, up to activation equivalence. -/
theorem openTheory_wire_par_superpose_activation_equiv
    {Δ₁ Δ₂ Γ Δ₃ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₂ Γ))
    (W₃ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₃)) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).wire
        (OpenProcess.mapBoundary (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Γ).symm.toHom
          ((openTheory Party m schedulerSampler).par W₁ W₂))
        W₃)
      (OpenProcess.mapBoundary (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom
        ((openTheory Party m schedulerSampler).par W₁
          ((openTheory Party m schedulerSampler).wire W₂ W₃))) := by
  simp only [openTheory, OpenProcess.mapBoundary_interleave]
  exact interleave_assoc_activationEquiv W₁ W₂ W₃ schedulerSampler schedulerSampler
    schedulerSampler schedulerSampler
    ((preservesActivation_map _).comp (preservesActivation_inlTensor Δ₁ _))
    ((preservesActivation_map _).comp (preservesActivation_inrTensor Δ₁ _))
    (preservesActivation_wireLeft _ Γ Δ₃) (preservesActivation_wireRight _ Γ Δ₃)
    (preservesActivation_wireLeft Δ₂ Γ Δ₃) (preservesActivation_wireRight Δ₂ Γ Δ₃)
    ((preservesActivation_map _).comp (preservesActivation_inlTensor Δ₁ _))
    ((preservesActivation_map _).comp (preservesActivation_inrTensor Δ₁ _))
    (map_schedulerNode_isActivated Party _) (schedulerNode_isActivated Party _)
    (schedulerNode_isActivated Party _) (map_schedulerNode_isActivated Party _)

/-- Wiring is commutative up to activation equivalence and boundary
reshaping. -/
theorem openTheory_wire_comm_activation_equiv
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    (W₂ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).wire W₁ W₂)
      (OpenProcess.mapBoundary (PortBoundary.Equiv.tensorComm Δ₂ Δ₁).toHom
        ((openTheory Party m schedulerSampler).wire
          (OpenProcess.mapBoundary
            (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom W₂)
          (OpenProcess.mapBoundary (PortBoundary.Equiv.tensorComm Δ₁ Γ).toHom W₁))) := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave]
  simp only [OpenProcess.mapBoundary_eq_mapHom]
  rw [OpenProcess.interleave_mapHom_left, OpenProcess.interleave_mapHom_right]
  exact interleave_comm_activationEquiv W₁ W₂ schedulerSampler schedulerSampler
    (preservesActivation_wireLeft Δ₁ Γ Δ₂) (preservesActivation_wireRight Δ₁ Γ Δ₂)
    (((preservesActivation_map _).comp (preservesActivation_wireLeft _ _ _)).comp
      (preservesActivation_map _))
    (((preservesActivation_map _).comp (preservesActivation_wireRight _ _ _)).comp
      (preservesActivation_map _))
    (schedulerNode_isActivated Party _) (map_schedulerNode_isActivated Party _)

/-- The monoidal unit: a single-state process with a trivial step. -/
def openTheoryUnit : OpenProcess.{u, v, w, w'} m Party PortBoundary.empty where
  Proc := PUnit
  step := fun _ =>
    { tree := .done
      semantics := ⟨⟩
      next := fun _ => PUnit.unit }
  stepSampler := fun _ => ⟨⟩

/-- Every step of the unit is silent. -/
theorem openTheoryUnit_isSilentStep (s : (openTheoryUnit Party m).Proc)
    (tr : ((openTheoryUnit Party m).step s).tree.Path) :
    IsSilentStep (openTheoryUnit.{u, v, w, w'} Party m) s tr := by
  simp only [IsSilentStep, openTheoryUnit, IsSilentDecoration]

/-- The monoidal unit is a left identity for parallel composition up to
activation equivalence. -/
theorem openTheory_par_left_unit_activation_equiv
    {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w, w'} m Party Δ) :
    OpenProcessActivationEquiv
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom
        ((openTheory Party m schedulerSampler).par
          (openTheoryUnit Party m) W))
      W := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave]
  have : Inhabited (openTheoryUnit.{u, v, w, w'} Party m).Proc := ⟨PUnit.unit⟩
  exact interleave_unit_left_activationEquiv (openTheoryUnit Party m) W
    (openTheoryUnit_isSilentStep Party m)
    ((preservesActivation_map _).comp (preservesActivation_inlTensor _ Δ))
    ((preservesActivation_map _).comp (preservesActivation_inrTensor _ Δ))
    (map_schedulerNode_isActivated Party _) schedulerSampler

/-- The monoidal unit is a right identity for parallel composition up to
activation equivalence. -/
theorem openTheory_par_right_unit_activation_equiv
    {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w, w'} m Party Δ) :
    OpenProcessActivationEquiv
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyRight Δ).toHom
        ((openTheory Party m schedulerSampler).par W
          (openTheoryUnit Party m)))
      W := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave]
  have : Inhabited (openTheoryUnit.{u, v, w, w'} Party m).Proc := ⟨PUnit.unit⟩
  exact interleave_unit_right_activationEquiv W (openTheoryUnit Party m)
    (openTheoryUnit_isSilentStep Party m)
    ((preservesActivation_map _).comp (preservesActivation_inlTensor Δ _))
    ((preservesActivation_map _).comp (preservesActivation_inrTensor Δ _))
    (map_schedulerNode_isActivated Party _) schedulerSampler

/-- The identity wire on `Γ`: a single-state process with a trivial step on
the boundary `swap Γ ⊗ Γ`. -/
def openTheoryIdWire (Γ : PortBoundary) :
    OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Γ) where
  Proc := PUnit
  step := fun _ =>
    { tree := .done
      semantics := ⟨⟩
      next := fun _ => PUnit.unit }
  stepSampler := fun _ => ⟨⟩

instance : OpenTheory.HasUnit (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  unit := openTheoryUnit Party m

instance : OpenTheory.HasIdWire (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  idWire := openTheoryIdWire Party m

theorem openTheory_unit :
    OpenTheory.HasUnit.unit (T := openTheory.{u, v, w, w'} Party m schedulerSampler) =
      openTheoryUnit Party m :=
  rfl

theorem openTheory_idWire (Γ : PortBoundary) :
    OpenTheory.HasIdWire.idWire (T := openTheory.{u, v, w, w'} Party m schedulerSampler) Γ =
      openTheoryIdWire Party m Γ :=
  rfl

/-- Every step of the identity wire is silent. -/
theorem openTheoryIdWire_isSilentStep (Γ : PortBoundary) (s : (openTheoryIdWire Party m Γ).Proc)
    (tr : ((openTheoryIdWire Party m Γ).step s).tree.Path) :
    IsSilentStep (openTheoryIdWire.{u, v, w, w'} Party m Γ) s tr := by
  simp only [IsSilentStep, openTheoryIdWire, IsSilentDecoration]

/-- Left zig-zag: wiring the identity wire on the left is a no-op up to
activation equivalence. -/
theorem openTheory_wire_id_wire_activation_equiv
    (Γ : PortBoundary)
    {Δ₂ : PortBoundary}
    (W₂ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).wire
        (openTheoryIdWire Party m Γ) W₂)
      W₂ := by
  simp only [openTheory]
  have : Inhabited (openTheoryIdWire.{u, v, w, w'} Party m Γ).Proc := ⟨PUnit.unit⟩
  exact interleave_unit_left_activationEquiv (openTheoryIdWire Party m Γ) W₂
    (openTheoryIdWire_isSilentStep Party m Γ)
    (preservesActivation_wireLeft _ Γ Δ₂) (preservesActivation_wireRight _ Γ Δ₂)
    (schedulerNode_isActivated Party _) schedulerSampler

/-- Right zig-zag: wiring the identity wire on the right is a no-op up to
activation equivalence. -/
theorem openTheory_wire_id_wire_right_activation_equiv
    (Γ : PortBoundary)
    {Δ₁ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor Δ₁ Γ)) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).wire W₁
        (openTheoryIdWire Party m Γ))
      W₁ := by
  simp only [openTheory]
  have : Inhabited (openTheoryIdWire.{u, v, w, w'} Party m Γ).Proc := ⟨PUnit.unit⟩
  exact interleave_unit_right_activationEquiv W₁ (openTheoryIdWire Party m Γ)
    (openTheoryIdWire_isSilentStep Party m Γ)
    (preservesActivation_wireLeft Δ₁ Γ Γ) (preservesActivation_wireRight Δ₁ Γ Γ)
    (schedulerNode_isActivated Party _) schedulerSampler

/-- Plugging is wiring through the whole boundary, up to activation
equivalence and boundary reshaping. -/
theorem openTheory_plug_eq_wire_activation_equiv
    {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w, w'} m Party Δ)
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ)) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).plug W K)
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
        ((openTheory Party m schedulerSampler).wire
          (OpenProcess.mapBoundary
            (PortBoundary.Equiv.tensorEmptyLeft Δ).symm.toHom W)
          (OpenProcess.mapBoundary
              (PortBoundary.Equiv.tensorEmptyRight
              (PortBoundary.swap Δ)).symm.toHom K))) := by
  simp only [openTheory]
  rw [OpenProcess.mapBoundary_interleave]
  simp only [OpenProcess.mapBoundary_eq_mapHom]
  rw [OpenProcess.interleave_mapHom_left, OpenProcess.interleave_mapHom_right]
  exact interleave_rehome_activationEquiv W K schedulerSampler schedulerSampler
    (preservesActivation_close Δ) (preservesActivation_close _)
    (((preservesActivation_map _).comp (preservesActivation_wireLeft _ _ _)).comp
      (preservesActivation_map _))
    (((preservesActivation_map _).comp (preservesActivation_wireRight _ _ _)).comp
      (preservesActivation_map _))
    (schedulerNode_isActivated Party _) (map_schedulerNode_isActivated Party _)

/-- The monoidal unit is the identity wire on the empty boundary, up to
activation equivalence and boundary reshaping. -/
theorem openTheory_unit_eq_activation_equiv :
    OpenProcessActivationEquiv
      (openTheoryUnit.{u, v, w, w'} Party m)
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
        (openTheoryIdWire Party m PortBoundary.empty)) := by
  refine OpenProcessActivationEquiv.of_step_match (fun _ _ => True)
    (fun _ => ⟨PUnit.unit, trivial⟩) (fun _ => ⟨PUnit.unit, trivial⟩) ?_ ?_ ?_ ?_
  · intro _ _ _ _ _
    exact .inl ⟨PUnit.unit, trivial, trivial⟩
  · intro _ _ _ _ hvisible
    exact absurd trivial hvisible
  · intro _ _ _ _ _
    exact .inl ⟨PUnit.unit, trivial, trivial⟩
  · intro _ _ _ _ hvisible
    exact absurd trivial hvisible

end Model

end UC
end Interaction
