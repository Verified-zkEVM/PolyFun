/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.OpenProcess
public import PolyFun.Interaction.UC.OpenProcess
public import PolyFun.Interaction.Concurrent.RoutedInterleave

/-!
# Routed interleaving and re-decoration of open processes

Two additions to the open-process substrate consumed by the concrete
`OpenTheory` models.

* `OpenProcess.mapHom` re-decorates every step along an arbitrary node-context
  hom, keeping states and samplers; `OpenProcess.mapBoundary` is the special
  case of the hom induced by a boundary morphism (`mapBoundary_eq_mapHom`).
  `OpenNodeContext.PreservesActivation` singles out the homs that keep
  activation flags, which is all that silence sees (`isSilentStep_mapHom_iff`);
  every structural hom of the open-process framework preserves activation.
* `OpenProcess.interleaveRouted` lifts `ProcessOver.interleaveRouted` to open
  processes with samplers: a scheduler node chooses a side, that side steps,
  and a route may update the other side's state from the completed path.
  Plain `interleave` is the trivially routed form
  (`interleave_eq_interleaveRouted`), and `mapHom` pushes through routed
  interleaving on either side (`mapHom_interleaveRouted`,
  `interleaveRouted_mapHom_left`, `interleaveRouted_mapHom_right`).

Routes are arbitrary functions of a state and a completed path; nothing here
inspects boundary traffic. A communicating composition supplies routes that
deliver the packets emitted along the path, while the composition laws of
`OpenProcessModel` concern the trivially routed instance.

`OpenProcess.ext_of_step_eq` and `OpenProcess.heq_step_of_processOver_eq` are
the extensionality helpers those laws use to lift `ProcessOver` equalities.
-/

public section

universe u v w w'

namespace Interaction
namespace UC

open Concurrent

/-! ## Activation-preserving context homs -/

namespace OpenNodeContext

variable {Party : Type u}

/-- A node-context hom preserves the activation flag of every node. Silence,
and hence activation equivalence, is invariant under such homs. -/
@[expose]
def PreservesActivation {Δ₁ Δ₂ : PortBoundary}
    (h : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₂)) : Prop :=
  ∀ (X : Type w) (ons : OpenNodeContext Party Δ₁ X),
    (h X ons).boundary.isActivated = ons.boundary.isActivated

theorem preservesActivation_id (Δ : PortBoundary) :
    PreservesActivation (TypeTree.Node.ContextHom.id (OpenNodeContext.{u, w} Party Δ)) :=
  fun _ _ => rfl

theorem PreservesActivation.comp {Δ₁ Δ₂ Δ₃ : PortBoundary}
    {g : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ₃)}
    {f : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₂)}
    (hg : PreservesActivation g) (hf : PreservesActivation f) :
    PreservesActivation (TypeTree.Node.ContextHom.comp g f) :=
  fun X ons => (hg X (f X ons)).trans (hf X ons)

theorem preservesActivation_map {Δ₁ Δ₂ : PortBoundary} (φ : PortBoundary.Hom Δ₁ Δ₂) :
    PreservesActivation (OpenNodeContext.map.{u, w} Party φ) := by
  intro X ons
  simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]

theorem preservesActivation_inlTensor (Δ₁ Δ₂ : PortBoundary) :
    PreservesActivation (OpenNodeContext.inlTensor.{u, w} Party Δ₁ Δ₂) := by
  intro X ons
  simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]

theorem preservesActivation_inrTensor (Δ₁ Δ₂ : PortBoundary) :
    PreservesActivation (OpenNodeContext.inrTensor.{u, w} Party Δ₁ Δ₂) := by
  intro X ons
  simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]

theorem preservesActivation_wireLeft (Δ₁ Γ Δ₂ : PortBoundary) :
    PreservesActivation (OpenNodeContext.wireLeft.{u, w} Party Δ₁ Γ Δ₂) := by
  intro X ons
  simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]

theorem preservesActivation_wireRight (Δ₁ Γ Δ₂ : PortBoundary) :
    PreservesActivation (OpenNodeContext.wireRight.{u, w} Party Δ₁ Γ Δ₂) := by
  intro X ons
  simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]

theorem preservesActivation_close (Δ : PortBoundary) :
    PreservesActivation (OpenNodeContext.close.{u, w} Party Δ) := by
  intro X ons
  simp [OpenNodeContext.close, BoundaryAction.closed]

end OpenNodeContext

namespace OpenProcess

variable {m : Type w → Type w'} {Party : Type u}

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
the equalities below rewrite through the interleaved dynamical model there.
`implicit_reducible` (unlike `reducible`) stays invisible to simp validation and
instance search. -/
attribute [local implicit_reducible] PFunctor.DynSystem.expose PFunctor.DynSystem.update
  PFunctor.DynSystem.mk' Concurrent.ProcessOver.interleave Concurrent.ProcessOver.interleaveRouted
  Concurrent.ProcessOver.mapContext OpenProcess.interleave

/-! ## Extensionality -/

/-- Extensionality for `OpenProcess` when both sides share the same residual
state type `Proc` definitionally, the `step` fields are equal as functions,
and the `stepSampler` fields are HEq (which reduces to literal equality once
`step` agrees). -/
theorem ext_of_step_eq {Δ : PortBoundary} {Proc : Type v}
    {step₁ step₂ : Proc → StepOver (OpenNodeContext.{u, w} Party Δ) Proc}
    {stepSampler₁ : ∀ s, TypeTree.Sampler.{w, w'} m (step₁ s).tree}
    {stepSampler₂ : ∀ s, TypeTree.Sampler.{w, w'} m (step₂ s).tree}
    (hstep : step₁ = step₂)
    (hsampler : HEq stepSampler₁ stepSampler₂) :
    (OpenProcess.mk Proc step₁ stepSampler₁ :
      OpenProcess.{u, v, w, w'} m Party Δ) =
      OpenProcess.mk Proc step₂ stepSampler₂ := by
  subst hstep
  cases hsampler
  rfl

/-- Derive step equality (as a function) from a `ProcessOver` equality
between two processes on the same residual state space. -/
theorem heq_step_of_processOver_eq.{v₀, w₀, w₂}
    {Proc : Type v₀} {Γ : Interaction.TypeTree.Node.Context.{w₀, w₂}}
    {P₁ P₂ : Concurrent.ProcessOver.{v₀, w₀, w₂} Proc Γ}
    (h : P₁ = P₂) :
    HEq P₁.step P₂.step :=
  h ▸ HEq.rfl

/-! ## Re-decoration along a context hom -/

/-- Re-decorate every step of an open process along a node-context hom,
keeping the residual states and the per-state samplers. -/
@[expose]
def mapHom {Δ₁ Δ₂ : PortBoundary}
    (h : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₂))
    (op : OpenProcess.{u, v, w, w'} m Party Δ₁) : OpenProcess.{u, v, w, w'} m Party Δ₂ where
  Proc := op.Proc
  step := fun s => (op.step s).mapContext h
  stepSampler := op.stepSampler

/-- Boundary adaptation is re-decoration along the induced context hom. -/
theorem mapBoundary_eq_mapHom {Δ₁ Δ₂ : PortBoundary} (φ : PortBoundary.Hom Δ₁ Δ₂)
    (op : OpenProcess.{u, v, w, w'} m Party Δ₁) :
    op.mapBoundary φ = op.mapHom (OpenNodeContext.map Party φ) :=
  rfl

/-- Re-decoration projects to `ProcessOver.mapContext`. -/
theorem toProcess_mapHom {Δ₁ Δ₂ : PortBoundary}
    (h : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₂))
    (op : OpenProcess.{u, v, w, w'} m Party Δ₁) :
    (op.mapHom h).toProcess = op.toProcess.mapContext h :=
  rfl

/-- Silence is invariant under re-decoration along an activation-preserving
hom. -/
theorem isSilentStep_mapHom_iff {Δ₁ Δ₂ : PortBoundary}
    {h : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₂)}
    (hh : OpenNodeContext.PreservesActivation h)
    (op : OpenProcess.{u, v, w, w'} m Party Δ₁) (s : op.Proc) (tr : (op.step s).tree.Path) :
    IsSilentStep (op.mapHom h) s tr ↔ IsSilentStep op s tr := by
  unfold IsSilentStep
  exact isSilentDecoration_iff_map h hh _ _

/-! ## Routed interleaving -/

/-- A route from an open process into a state space: how a completed step path
at a given state updates the other side. -/
abbrev Route {Δ₁ : PortBoundary} (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (P₂ : Type v) :
    Type (max v w) :=
  ∀ s₁ : p₁.Proc, TypeTree.Path (p₁.step s₁).tree → P₂ → P₂

/--
Binary-choice interleaving of two open processes with routing hooks.

Structure on `Proc` and `step` is delegated to `ProcessOver.interleaveRouted`,
so the scheduler node chooses a side, that side steps with its decoration
mapped into `Δ`, and its completed path is handed to the route updating the
other side. The per-state sampler is assembled by `TypeTree.Sampler.interleave`
exactly as for `interleave`.
-/
@[expose]
def interleaveRouted {Δ₁ Δ₂ Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool))
    (route₁ : Route p₁ p₂.Proc) (route₂ : Route p₂ p₁.Proc) :
    OpenProcess.{u, v, w, w'} m Party Δ where
  Proc := p₁.Proc × p₂.Proc
  step := (p₁.toProcess.interleaveRouted p₂.toProcess f₁ f₂ schedulerCtx route₁ route₂).step
  stepSampler := fun (s₁, s₂) =>
    TypeTree.Sampler.interleave schedulerSampler
      (p₁.stepSampler s₁) (p₂.stepSampler s₂)

/-- Routed interleaving projects to the structural routed interleaving of the
underlying processes, discarding only the assembled sampler. -/
theorem toProcess_interleaveRouted {Δ₁ Δ₂ Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool))
    (route₁ : Route p₁ p₂.Proc) (route₂ : Route p₂ p₁.Proc) :
    (p₁.interleaveRouted p₂ f₁ f₂ schedulerCtx schedulerSampler route₁ route₂).toProcess =
      p₁.toProcess.interleaveRouted p₂.toProcess f₁ f₂ schedulerCtx route₁ route₂ :=
  rfl

/-- Interleaving is routed interleaving with the trivial routes. -/
theorem interleave_eq_interleaveRouted {Δ₁ Δ₂ Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool)) :
    p₁.interleave p₂ f₁ f₂ schedulerCtx schedulerSampler =
      p₁.interleaveRouted p₂ f₁ f₂ schedulerCtx schedulerSampler
        (fun _ _ s => s) (fun _ _ s => s) :=
  rfl

/-- Re-decorating a routed interleaving is routed interleaving with each
injection post-composed by the hom; the routes are untouched. -/
theorem mapHom_interleaveRouted {Δ₁ Δ₂ Δ Δ' : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool))
    (route₁ : Route p₁ p₂.Proc) (route₂ : Route p₂ p₁.Proc)
    (g : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ)
      (OpenNodeContext.{u, w} Party Δ')) :
    (p₁.interleaveRouted p₂ f₁ f₂ schedulerCtx schedulerSampler route₁ route₂).mapHom g =
      p₁.interleaveRouted p₂
        (TypeTree.Node.ContextHom.comp g f₁) (TypeTree.Node.ContextHom.comp g f₂)
        (g _ schedulerCtx) schedulerSampler route₁ route₂ := by
  have hproc :
      (p₁.toProcess.interleaveRouted p₂.toProcess f₁ f₂ schedulerCtx route₁ route₂).mapContext g =
        p₁.toProcess.interleaveRouted p₂.toProcess
          (TypeTree.Node.ContextHom.comp g f₁) (TypeTree.Node.ContextHom.comp g f₂)
          (g _ schedulerCtx) route₁ route₂ :=
    ProcessOver.mapContext_interleaveRouted p₁.toProcess p₂.toProcess f₁ f₂ schedulerCtx
      route₁ route₂ g
  cases p₁ with | mk Proc₁ step₁ stepSampler₁ =>
  cases p₂ with | mk Proc₂ step₂ stepSampler₂ =>
  simp only [mapHom, interleaveRouted]
  exact ext_of_step_eq (eq_of_heq (heq_step_of_processOver_eq hproc)) HEq.rfl

/-- Re-decorating the left operand before routed interleaving pre-composes
the left injection; the routes are the same functions. -/
theorem interleaveRouted_mapHom_left {Δ₁ Δ₁' Δ₂ Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (g₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₁'))
    (f₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁')
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool))
    (route₁ : Route p₁ p₂.Proc) (route₂ : Route p₂ p₁.Proc) :
    (p₁.mapHom g₁).interleaveRouted p₂ f₁ f₂ schedulerCtx schedulerSampler route₁ route₂ =
      p₁.interleaveRouted p₂ (TypeTree.Node.ContextHom.comp f₁ g₁) f₂
        schedulerCtx schedulerSampler route₁ route₂ := by
  have hproc :
      (p₁.toProcess.mapContext g₁).interleaveRouted p₂.toProcess f₁ f₂ schedulerCtx
          route₁ route₂ =
        p₁.toProcess.interleaveRouted p₂.toProcess
          (TypeTree.Node.ContextHom.comp f₁ g₁) f₂ schedulerCtx route₁ route₂ :=
    ProcessOver.interleaveRouted_mapContext_left p₁.toProcess p₂.toProcess g₁ f₁ f₂
      schedulerCtx route₁ route₂
  cases p₁ with | mk Proc₁ step₁ stepSampler₁ =>
  cases p₂ with | mk Proc₂ step₂ stepSampler₂ =>
  simp only [mapHom, interleaveRouted]
  exact ext_of_step_eq (eq_of_heq (heq_step_of_processOver_eq hproc)) HEq.rfl

/-- Re-decorating the right operand before routed interleaving pre-composes
the right injection; the routes are the same functions. -/
theorem interleaveRouted_mapHom_right {Δ₁ Δ₂ Δ₂' Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (g₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ₂'))
    (f₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂')
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool))
    (route₁ : Route p₁ p₂.Proc) (route₂ : Route p₂ p₁.Proc) :
    p₁.interleaveRouted (p₂.mapHom g₂) f₁ f₂ schedulerCtx schedulerSampler route₁ route₂ =
      p₁.interleaveRouted p₂ f₁ (TypeTree.Node.ContextHom.comp f₂ g₂)
        schedulerCtx schedulerSampler route₁ route₂ := by
  have hproc :
      p₁.toProcess.interleaveRouted (p₂.toProcess.mapContext g₂) f₁ f₂ schedulerCtx
          route₁ route₂ =
        p₁.toProcess.interleaveRouted p₂.toProcess f₁
          (TypeTree.Node.ContextHom.comp f₂ g₂) schedulerCtx route₁ route₂ :=
    ProcessOver.interleaveRouted_mapContext_right p₁.toProcess p₂.toProcess g₂ f₁ f₂
      schedulerCtx route₁ route₂
  cases p₁ with | mk Proc₁ step₁ stepSampler₁ =>
  cases p₂ with | mk Proc₂ step₂ stepSampler₂ =>
  simp only [mapHom, interleaveRouted]
  exact ext_of_step_eq (eq_of_heq (heq_step_of_processOver_eq hproc)) HEq.rfl

/-- Boundary adaptation pushes through routed interleaving. -/
theorem mapBoundary_interleaveRouted {Δ₁ Δ₂ Δ Δ' : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool))
    (route₁ : Route p₁ p₂.Proc) (route₂ : Route p₂ p₁.Proc)
    (φ : PortBoundary.Hom Δ Δ') :
    (p₁.interleaveRouted p₂ f₁ f₂ schedulerCtx schedulerSampler route₁ route₂).mapBoundary φ =
      p₁.interleaveRouted p₂
        (TypeTree.Node.ContextHom.comp (OpenNodeContext.map Party φ) f₁)
        (TypeTree.Node.ContextHom.comp (OpenNodeContext.map Party φ) f₂)
        (OpenNodeContext.map Party φ _ schedulerCtx) schedulerSampler route₁ route₂ :=
  mapHom_interleaveRouted p₁ p₂ f₁ f₂ schedulerCtx schedulerSampler route₁ route₂ _

/-! ## Normalizing maps around plain interleavings -/

/-- Re-decorating a plain interleaving post-composes both injections. -/
theorem mapHom_interleave {Δ₁ Δ₂ Δ Δ' : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool))
    (g : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ)
      (OpenNodeContext.{u, w} Party Δ')) :
    (p₁.interleave p₂ f₁ f₂ schedulerCtx schedulerSampler).mapHom g =
      p₁.interleave p₂
        (TypeTree.Node.ContextHom.comp g f₁) (TypeTree.Node.ContextHom.comp g f₂)
        (g _ schedulerCtx) schedulerSampler := by
  rw [interleave_eq_interleaveRouted, interleave_eq_interleaveRouted, mapHom_interleaveRouted]

/-- Boundary adaptation of a plain interleaving post-composes both injections. -/
theorem mapBoundary_interleave {Δ₁ Δ₂ Δ Δ' : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool)) (φ : PortBoundary.Hom Δ Δ') :
    (p₁.interleave p₂ f₁ f₂ schedulerCtx schedulerSampler).mapBoundary φ =
      p₁.interleave p₂
        (TypeTree.Node.ContextHom.comp (OpenNodeContext.map Party φ) f₁)
        (TypeTree.Node.ContextHom.comp (OpenNodeContext.map Party φ) f₂)
        (OpenNodeContext.map Party φ _ schedulerCtx) schedulerSampler :=
  mapHom_interleave p₁ p₂ f₁ f₂ schedulerCtx schedulerSampler _

/-- Re-decorating the left operand before a plain interleaving pre-composes
the left injection. -/
theorem interleave_mapHom_left {Δ₁ Δ₁' Δ₂ Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (g₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₁'))
    (f₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁')
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool)) :
    (p₁.mapHom g₁).interleave p₂ f₁ f₂ schedulerCtx schedulerSampler =
      p₁.interleave p₂ (TypeTree.Node.ContextHom.comp f₁ g₁) f₂
        schedulerCtx schedulerSampler := by
  have hproc :
      (p₁.toProcess.mapContext g₁).interleave p₂.toProcess f₁ f₂ schedulerCtx =
        p₁.toProcess.interleave p₂.toProcess
          (TypeTree.Node.ContextHom.comp f₁ g₁) f₂ schedulerCtx :=
    ProcessOver.interleave_mapContext_left p₁.toProcess p₂.toProcess g₁ f₁ f₂ schedulerCtx
  cases p₁ with | mk Proc₁ step₁ stepSampler₁ =>
  cases p₂ with | mk Proc₂ step₂ stepSampler₂ =>
  simp only [mapHom, interleave]
  exact ext_of_step_eq (eq_of_heq (heq_step_of_processOver_eq hproc)) HEq.rfl

/-- Re-decorating the right operand before a plain interleaving pre-composes
the right injection. -/
theorem interleave_mapHom_right {Δ₁ Δ₂ Δ₂' Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (g₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ₂'))
    (f₁ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂')
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool)) :
    p₁.interleave (p₂.mapHom g₂) f₁ f₂ schedulerCtx schedulerSampler =
      p₁.interleave p₂ f₁ (TypeTree.Node.ContextHom.comp f₂ g₂)
        schedulerCtx schedulerSampler := by
  have hproc :
      p₁.toProcess.interleave (p₂.toProcess.mapContext g₂) f₁ f₂ schedulerCtx =
        p₁.toProcess.interleave p₂.toProcess f₁
          (TypeTree.Node.ContextHom.comp f₂ g₂) schedulerCtx :=
    ProcessOver.interleave_mapContext_right p₁.toProcess p₂.toProcess g₂ f₁ f₂ schedulerCtx
  cases p₁ with | mk Proc₁ step₁ stepSampler₁ =>
  cases p₂ with | mk Proc₂ step₂ stepSampler₂ =>
  simp only [mapHom, interleave]
  exact ext_of_step_eq (eq_of_heq (heq_step_of_processOver_eq hproc)) HEq.rfl

end OpenProcess

end UC
end Interaction
