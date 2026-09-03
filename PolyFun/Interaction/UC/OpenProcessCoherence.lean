/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.OpenProcess
public import PolyFun.Interaction.UC.OpenProcessInterleave

/-!
# Coherence of interleaving up to activation equivalence

Every coherence law of the process-backed open theories compares two ways of
nesting `OpenProcess.interleave` around the same component processes. This
module proves those comparisons once, for arbitrary activation-preserving
context homs and silent scheduler nodes, so that each concrete law is an
instance.

* `isSilentStep_interleaveRouted_left_iff` / `_right_iff` characterize silence
  of a composite step by silence of the scheduled component's step.
* `interleave_assoc_activationEquiv`, `interleave_comm_activationEquiv`,
  `interleave_rehome_activationEquiv`, and
  `interleave_unit_left_activationEquiv` / `_right_` are the three shapes
  behind every law: regrouping three components, swapping two, changing the
  homs and scheduler node of a fixed nesting, and absorbing a component all
  of whose steps are silent.
* `interleave_congr_left` / `_right` and `mapHom_congr` make activation
  equivalence a congruence for interleaving and re-decoration, which is what
  lets the shapes be chained through nested positions.

Activation equivalence erases packets and samplers, so these are structural
coherence facts, not security statements; the sampler-aware strengthening
lives separately.
-/

public section

universe u v w w'

namespace Interaction
namespace UC

open Concurrent
open PFunctor.FreeM.Displayed (Decoration)

variable {m : Type w → Type w'} {Party : Type u}

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
the proofs below rewrite through the interleaved dynamical model there.
`implicit_reducible` (unlike `reducible`) stays invisible to simp validation and
instance search. -/
attribute [local implicit_reducible] PFunctor.DynSystem.expose PFunctor.DynSystem.update
  PFunctor.DynSystem.mk' Concurrent.ProcessOver.interleave Concurrent.ProcessOver.interleaveRouted
  OpenProcess.mapHom OpenProcess.interleave OpenProcess.interleaveRouted

namespace OpenProcess

/-! ## Silence of a composite step -/

/-- A composite step scheduled to the left component is silent exactly when
the component's step is, provided the scheduler node is silent and the left
injection preserves activation. -/
theorem isSilentStep_interleaveRouted_left_iff {Δ₁ Δ₂ Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    (f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (hf₁ : OpenNodeContext.PreservesActivation f₁)
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (hc : c.boundary.isActivated = false) (σ : m (ULift.{w, 0} Bool))
    (r₁ : Route p₁ p₂.Proc) (r₂ : Route p₂ p₁.Proc)
    (s₁ : p₁.Proc) (s₂ : p₂.Proc) (tr : (p₁.step s₁).tree.Path) :
    IsSilentStep (p₁.interleaveRouted p₂ f₁ f₂ c σ r₁ r₂) (s₁, s₂) ⟨⟨true⟩, tr⟩ ↔
      IsSilentStep p₁ s₁ tr := by
  simp only [IsSilentStep, interleaveRouted, ProcessOver.interleaveRouted, ProcessOver.ofStep,
    PFunctor.DynSystem.expose_mk', IsSilentDecoration]
  rw [isSilentDecoration_iff_map f₁ hf₁, hc]
  simp

/-- A composite step scheduled to the right component is silent exactly when
the component's step is. -/
theorem isSilentStep_interleaveRouted_right_iff {Δ₁ Δ₂ Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ)}
    (hf₂ : OpenNodeContext.PreservesActivation f₂)
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (hc : c.boundary.isActivated = false) (σ : m (ULift.{w, 0} Bool))
    (r₁ : Route p₁ p₂.Proc) (r₂ : Route p₂ p₁.Proc)
    (s₁ : p₁.Proc) (s₂ : p₂.Proc) (tr : (p₂.step s₂).tree.Path) :
    IsSilentStep (p₁.interleaveRouted p₂ f₁ f₂ c σ r₁ r₂) (s₁, s₂) ⟨⟨false⟩, tr⟩ ↔
      IsSilentStep p₂ s₂ tr := by
  simp only [IsSilentStep, interleaveRouted, ProcessOver.interleaveRouted, ProcessOver.ofStep,
    PFunctor.DynSystem.expose_mk', IsSilentDecoration]
  rw [isSilentDecoration_iff_map f₂ hf₂, hc]
  simp

/-- Silence of a left-scheduled step of a plain interleaving. -/
theorem isSilentStep_interleave_left_iff {Δ₁ Δ₂ Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    (f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (hf₁ : OpenNodeContext.PreservesActivation f₁)
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (hc : c.boundary.isActivated = false) (σ : m (ULift.{w, 0} Bool))
    (s₁ : p₁.Proc) (s₂ : p₂.Proc) (tr : (p₁.step s₁).tree.Path) :
    IsSilentStep (p₁.interleave p₂ f₁ f₂ c σ) (s₁, s₂) ⟨⟨true⟩, tr⟩ ↔
      IsSilentStep p₁ s₁ tr :=
  isSilentStep_interleaveRouted_left_iff p₁ p₂ f₂ hf₁ hc σ (fun _ _ s => s) (fun _ _ s => s)
    s₁ s₂ tr

/-- Silence of a right-scheduled step of a plain interleaving. -/
theorem isSilentStep_interleave_right_iff {Δ₁ Δ₂ Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ)}
    (hf₂ : OpenNodeContext.PreservesActivation f₂)
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (hc : c.boundary.isActivated = false) (σ : m (ULift.{w, 0} Bool))
    (s₁ : p₁.Proc) (s₂ : p₂.Proc) (tr : (p₂.step s₂).tree.Path) :
    IsSilentStep (p₁.interleave p₂ f₁ f₂ c σ) (s₁, s₂) ⟨⟨false⟩, tr⟩ ↔
      IsSilentStep p₂ s₂ tr :=
  isSilentStep_interleaveRouted_right_iff p₁ p₂ f₁ hf₂ hc σ (fun _ _ s => s) (fun _ _ s => s)
    s₁ s₂ tr

end OpenProcess

/-! ## Branches of a composite step -/

namespace OpenProcess

variable {Δ₁ Δ₂ Δ Δ' : PortBoundary}
  (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
  (f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
    (OpenNodeContext.{u, w} Party Δ))
  (f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
    (OpenNodeContext.{u, w} Party Δ))
  (c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)) (σ : m (ULift.{w, 0} Bool))
  (g : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ)
    (OpenNodeContext.{u, w} Party Δ'))
  (s₁ : p₁.Proc) (s₂ : p₂.Proc)

/-- A left-scheduled composite step is silent when the scheduler node is and
the re-decorated component step is. -/
theorem isSilentStep_interleave_left_iff_decoration (tr : (p₁.step s₁).tree.Path) :
    IsSilentStep (p₁.interleave p₂ f₁ f₂ c σ) (s₁, s₂) ⟨⟨true⟩, tr⟩ ↔
      c.boundary.isActivated = false ∧
        IsSilentDecoration (Decoration.map f₁ _ (p₁.step s₁).semantics) tr := by
  simp only [IsSilentStep, OpenProcess.interleave, ProcessOver.interleave, ProcessOver.ofStep,
    PFunctor.DynSystem.expose_mk', IsSilentDecoration]

/-- A right-scheduled composite step is silent when the scheduler node is and
the re-decorated component step is. -/
theorem isSilentStep_interleave_right_iff_decoration (tr : (p₂.step s₂).tree.Path) :
    IsSilentStep (p₁.interleave p₂ f₁ f₂ c σ) (s₁, s₂) ⟨⟨false⟩, tr⟩ ↔
      c.boundary.isActivated = false ∧
        IsSilentDecoration (Decoration.map f₂ _ (p₂.step s₂).semantics) tr := by
  simp only [IsSilentStep, OpenProcess.interleave, ProcessOver.interleave, ProcessOver.ofStep,
    PFunctor.DynSystem.expose_mk', IsSilentDecoration]

/-- Silence of the left branch of a re-decorated composite step. -/
theorem isSilentDecoration_map_interleave_left (tr : (p₁.step s₁).tree.Path) :
    IsSilentDecoration
        (Decoration.map g _ ((p₁.interleave p₂ f₁ f₂ c σ).step (s₁, s₂)).semantics)
        ⟨⟨true⟩, tr⟩ ↔
      (g _ c).boundary.isActivated = false ∧
        IsSilentDecoration (Decoration.map g _ (Decoration.map f₁ _ (p₁.step s₁).semantics))
          tr := by
  simp only [OpenProcess.interleave, ProcessOver.interleave, ProcessOver.ofStep,
    PFunctor.DynSystem.expose_mk', OpenNodeContext.decoration_map_node, IsSilentDecoration]

/-- Silence of the right branch of a re-decorated composite step. -/
theorem isSilentDecoration_map_interleave_right (tr : (p₂.step s₂).tree.Path) :
    IsSilentDecoration
        (Decoration.map g _ ((p₁.interleave p₂ f₁ f₂ c σ).step (s₁, s₂)).semantics)
        ⟨⟨false⟩, tr⟩ ↔
      (g _ c).boundary.isActivated = false ∧
        IsSilentDecoration (Decoration.map g _ (Decoration.map f₂ _ (p₂.step s₂).semantics))
          tr := by
  simp only [OpenProcess.interleave, ProcessOver.interleave, ProcessOver.ofStep,
    PFunctor.DynSystem.expose_mk', OpenNodeContext.decoration_map_node, IsSilentDecoration]

/-- The boundary trace of a left-scheduled composite step. -/
theorem boundaryTrace_interleave_left (tr : (p₁.step s₁).tree.Path) :
    OpenNodeContext.boundaryTrace _ ((p₁.interleave p₂ f₁ f₂ c σ).step (s₁, s₂)).semantics
        ⟨⟨true⟩, tr⟩ =
      c.boundary.emit ⟨true⟩ *
        OpenNodeContext.boundaryTrace _ (Decoration.map f₁ _ (p₁.step s₁).semantics) tr := by
  simp only [OpenProcess.interleave, ProcessOver.interleave, ProcessOver.ofStep,
    PFunctor.DynSystem.expose_mk']
  exact OpenNodeContext.boundaryTrace_node _ _ _ _

/-- The boundary trace of a right-scheduled composite step. -/
theorem boundaryTrace_interleave_right (tr : (p₂.step s₂).tree.Path) :
    OpenNodeContext.boundaryTrace _ ((p₁.interleave p₂ f₁ f₂ c σ).step (s₁, s₂)).semantics
        ⟨⟨false⟩, tr⟩ =
      c.boundary.emit ⟨false⟩ *
        OpenNodeContext.boundaryTrace _ (Decoration.map f₂ _ (p₂.step s₂).semantics) tr := by
  simp only [OpenProcess.interleave, ProcessOver.interleave, ProcessOver.ofStep,
    PFunctor.DynSystem.expose_mk']
  exact OpenNodeContext.boundaryTrace_node _ _ _ _

/-- The boundary trace of the left branch of a re-decorated composite step. -/
theorem boundaryTrace_map_interleave_left (tr : (p₁.step s₁).tree.Path) :
    OpenNodeContext.boundaryTrace _
        (Decoration.map g _ ((p₁.interleave p₂ f₁ f₂ c σ).step (s₁, s₂)).semantics)
        ⟨⟨true⟩, tr⟩ =
      (g _ c).boundary.emit ⟨true⟩ *
        OpenNodeContext.boundaryTrace _
          (Decoration.map g _ (Decoration.map f₁ _ (p₁.step s₁).semantics)) tr := by
  simp only [OpenProcess.interleave, ProcessOver.interleave, ProcessOver.ofStep,
    PFunctor.DynSystem.expose_mk', OpenNodeContext.decoration_map_node]
  exact OpenNodeContext.boundaryTrace_node _ _ _ _

/-- The boundary trace of the right branch of a re-decorated composite step. -/
theorem boundaryTrace_map_interleave_right (tr : (p₂.step s₂).tree.Path) :
    OpenNodeContext.boundaryTrace _
        (Decoration.map g _ ((p₁.interleave p₂ f₁ f₂ c σ).step (s₁, s₂)).semantics)
        ⟨⟨false⟩, tr⟩ =
      (g _ c).boundary.emit ⟨false⟩ *
        OpenNodeContext.boundaryTrace _
          (Decoration.map g _ (Decoration.map f₂ _ (p₂.step s₂).semantics)) tr := by
  simp only [OpenProcess.interleave, ProcessOver.interleave, ProcessOver.ofStep,
    PFunctor.DynSystem.expose_mk', OpenNodeContext.decoration_map_node]
  exact OpenNodeContext.boundaryTrace_node _ _ _ _

end OpenProcess

/-! ## The three coherence shapes -/

section Shapes

variable {Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₂₃ Δ : PortBoundary}
  (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
  (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
  (p₃ : OpenProcess.{u, v, w, w'} m Party Δ₃)

open OpenProcess

/-- **Reassociation.** A left-nested interleaving of three processes is
activation equivalent to a right-nested one with arbitrary
activation-preserving injections and silent scheduler nodes on each side. -/
theorem interleave_assoc_activationEquiv
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₁₂)}
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ₁₂)}
    {g₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {g₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₃)
      (OpenNodeContext.{u, w} Party Δ)}
    {cIn : OpenNodeContext.{u, w} Party Δ₁₂ (ULift.{w, 0} Bool)}
    {cOut : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (σIn σOut : m (ULift.{w, 0} Bool))
    {f₁' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ₂₃)}
    {f₂' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₃)
      (OpenNodeContext.{u, w} Party Δ₂₃)}
    {g₁' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    {g₂' : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂₃)
      (OpenNodeContext.{u, w} Party Δ)}
    {dIn : OpenNodeContext.{u, w} Party Δ₂₃ (ULift.{w, 0} Bool)}
    {dOut : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (τIn τOut : m (ULift.{w, 0} Bool))
    (hf₁ : OpenNodeContext.PreservesActivation f₁) (hf₂ : OpenNodeContext.PreservesActivation f₂)
    (hg₁ : OpenNodeContext.PreservesActivation g₁) (hg₂ : OpenNodeContext.PreservesActivation g₂)
    (hf₁' : OpenNodeContext.PreservesActivation f₁')
    (hf₂' : OpenNodeContext.PreservesActivation f₂')
    (hg₁' : OpenNodeContext.PreservesActivation g₁')
    (hg₂' : OpenNodeContext.PreservesActivation g₂')
    (hcIn : cIn.boundary.isActivated = false) (hcOut : cOut.boundary.isActivated = false)
    (hdIn : dIn.boundary.isActivated = false) (hdOut : dOut.boundary.isActivated = false) :
    OpenProcessActivationEquiv
      ((p₁.interleave p₂ f₁ f₂ cIn σIn).interleave p₃ g₁ g₂ cOut σOut)
      (p₁.interleave (p₂.interleave p₃ f₁' f₂' dIn τIn) g₁' g₂' dOut τOut) := by
  -- silence of each leaf, seen from either nesting
  have L₁ : ∀ s₁ s₂ s₃ (tr : (p₁.step s₁).tree.Path),
      IsSilentStep ((p₁.interleave p₂ f₁ f₂ cIn σIn).interleave p₃ g₁ g₂ cOut σOut)
        ((s₁, s₂), s₃) ⟨⟨true⟩, ⟨⟨true⟩, tr⟩⟩ ↔ IsSilentStep p₁ s₁ tr := fun s₁ s₂ s₃ tr =>
    (isSilentStep_interleave_left_iff _ p₃ g₂ hg₁ hcOut σOut _ s₃ _).trans
      (isSilentStep_interleave_left_iff p₁ p₂ f₂ hf₁ hcIn σIn s₁ s₂ tr)
  have L₂ : ∀ s₁ s₂ s₃ (tr : (p₂.step s₂).tree.Path),
      IsSilentStep ((p₁.interleave p₂ f₁ f₂ cIn σIn).interleave p₃ g₁ g₂ cOut σOut)
        ((s₁, s₂), s₃) ⟨⟨true⟩, ⟨⟨false⟩, tr⟩⟩ ↔ IsSilentStep p₂ s₂ tr := fun s₁ s₂ s₃ tr =>
    (isSilentStep_interleave_left_iff _ p₃ g₂ hg₁ hcOut σOut _ s₃ _).trans
      (isSilentStep_interleave_right_iff p₁ p₂ f₁ hf₂ hcIn σIn s₁ s₂ tr)
  have L₃ : ∀ s₁ s₂ s₃ (tr : (p₃.step s₃).tree.Path),
      IsSilentStep ((p₁.interleave p₂ f₁ f₂ cIn σIn).interleave p₃ g₁ g₂ cOut σOut)
        ((s₁, s₂), s₃) ⟨⟨false⟩, tr⟩ ↔ IsSilentStep p₃ s₃ tr := fun s₁ s₂ s₃ tr =>
    isSilentStep_interleave_right_iff (p₁.interleave p₂ f₁ f₂ cIn σIn) p₃ g₁ hg₂ hcOut σOut
      (s₁, s₂) s₃ tr
  have R₁ : ∀ s₁ s₂ s₃ (tr : (p₁.step s₁).tree.Path),
      IsSilentStep (p₁.interleave (p₂.interleave p₃ f₁' f₂' dIn τIn) g₁' g₂' dOut τOut)
        (s₁, (s₂, s₃)) ⟨⟨true⟩, tr⟩ ↔ IsSilentStep p₁ s₁ tr := fun s₁ s₂ s₃ tr =>
    isSilentStep_interleave_left_iff p₁ (p₂.interleave p₃ f₁' f₂' dIn τIn) g₂' hg₁' hdOut τOut
      s₁ (s₂, s₃) tr
  have R₂ : ∀ s₁ s₂ s₃ (tr : (p₂.step s₂).tree.Path),
      IsSilentStep (p₁.interleave (p₂.interleave p₃ f₁' f₂' dIn τIn) g₁' g₂' dOut τOut)
        (s₁, (s₂, s₃)) ⟨⟨false⟩, ⟨⟨true⟩, tr⟩⟩ ↔ IsSilentStep p₂ s₂ tr := fun s₁ s₂ s₃ tr =>
    (isSilentStep_interleave_right_iff p₁ (p₂.interleave p₃ f₁' f₂' dIn τIn) g₁' hg₂' hdOut τOut
      s₁ (s₂, s₃) _).trans
      (isSilentStep_interleave_left_iff p₂ p₃ f₂' hf₁' hdIn τIn s₂ s₃ tr)
  have R₃ : ∀ s₁ s₂ s₃ (tr : (p₃.step s₃).tree.Path),
      IsSilentStep (p₁.interleave (p₂.interleave p₃ f₁' f₂' dIn τIn) g₁' g₂' dOut τOut)
        (s₁, (s₂, s₃)) ⟨⟨false⟩, ⟨⟨false⟩, tr⟩⟩ ↔ IsSilentStep p₃ s₃ tr := fun s₁ s₂ s₃ tr =>
    (isSilentStep_interleave_right_iff p₁ (p₂.interleave p₃ f₁' f₂' dIn τIn) g₁' hg₂' hdOut τOut
      s₁ (s₂, s₃) _).trans
      (isSilentStep_interleave_right_iff p₂ p₃ f₁' hf₂' hdIn τIn s₂ s₃ tr)
  refine OpenProcessActivationEquiv.of_step_match
    (fun ⟨⟨s₁, s₂⟩, s₃⟩ ⟨s₁', ⟨s₂', s₃'⟩⟩ => s₁ = s₁' ∧ s₂ = s₂' ∧ s₃ = s₃')
    (fun ⟨⟨s₁, s₂⟩, s₃⟩ => ⟨⟨s₁, ⟨s₂, s₃⟩⟩, rfl, rfl, rfl⟩)
    (fun ⟨s₁, ⟨s₂, s₃⟩⟩ => ⟨⟨⟨s₁, s₂⟩, s₃⟩, rfl, rfl, rfl⟩) ?_ ?_ ?_ ?_
  all_goals intro ⟨⟨s₁, s₂⟩, s₃⟩ ⟨s₁', ⟨s₂', s₃'⟩⟩ ⟨h1, h2, h3⟩
  all_goals subst h1; subst h2; subst h3
  · rintro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        exact .inl ⟨⟨⟨true⟩, rest'⟩, (R₁ _ _ _ _).mpr ((L₁ _ _ _ _).mp hsilent), rfl, rfl, rfl⟩
      | false =>
        exact .inl ⟨⟨⟨false⟩, ⟨⟨true⟩, rest'⟩⟩, (R₂ _ _ _ _).mpr ((L₂ _ _ _ _).mp hsilent),
          rfl, rfl, rfl⟩
    | false =>
      exact .inl ⟨⟨⟨false⟩, ⟨⟨false⟩, rest⟩⟩, (R₃ _ _ _ _).mpr ((L₃ _ _ _ _).mp hsilent),
        rfl, rfl, rfl⟩
  · rintro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        exact ⟨⟨⟨true⟩, rest'⟩, fun hs => hvisible ((L₁ _ _ _ _).mpr ((R₁ _ _ _ _).mp hs)),
          rfl, rfl, rfl⟩
      | false =>
        exact ⟨⟨⟨false⟩, ⟨⟨true⟩, rest'⟩⟩,
          fun hs => hvisible ((L₂ _ _ _ _).mpr ((R₂ _ _ _ _).mp hs)), rfl, rfl, rfl⟩
    | false =>
      exact ⟨⟨⟨false⟩, ⟨⟨false⟩, rest⟩⟩,
        fun hs => hvisible ((L₃ _ _ _ _).mpr ((R₃ _ _ _ _).mp hs)), rfl, rfl, rfl⟩
  · rintro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      exact .inl ⟨⟨⟨true⟩, ⟨⟨true⟩, rest⟩⟩, (L₁ _ _ _ _).mpr ((R₁ _ _ _ _).mp hsilent),
        rfl, rfl, rfl⟩
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        exact .inl ⟨⟨⟨true⟩, ⟨⟨false⟩, rest'⟩⟩, (L₂ _ _ _ _).mpr ((R₂ _ _ _ _).mp hsilent),
          rfl, rfl, rfl⟩
      | false =>
        exact .inl ⟨⟨⟨false⟩, rest'⟩, (L₃ _ _ _ _).mpr ((R₃ _ _ _ _).mp hsilent), rfl, rfl, rfl⟩
  · rintro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      exact ⟨⟨⟨true⟩, ⟨⟨true⟩, rest⟩⟩, fun hs => hvisible ((R₁ _ _ _ _).mpr ((L₁ _ _ _ _).mp hs)),
        rfl, rfl, rfl⟩
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        exact ⟨⟨⟨true⟩, ⟨⟨false⟩, rest'⟩⟩,
          fun hs => hvisible ((R₂ _ _ _ _).mpr ((L₂ _ _ _ _).mp hs)), rfl, rfl, rfl⟩
      | false =>
        exact ⟨⟨⟨false⟩, rest'⟩, fun hs => hvisible ((R₃ _ _ _ _).mpr ((L₃ _ _ _ _).mp hs)),
          rfl, rfl, rfl⟩

/-- **Commutation.** Interleaving two processes in either order gives
activation-equivalent composites, for any activation-preserving injections
and silent scheduler nodes. -/
theorem interleave_comm_activationEquiv
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)} (σ : m (ULift.{w, 0} Bool))
    {g₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {g₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    {d : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)} (τ : m (ULift.{w, 0} Bool))
    (hf₁ : OpenNodeContext.PreservesActivation f₁) (hf₂ : OpenNodeContext.PreservesActivation f₂)
    (hg₁ : OpenNodeContext.PreservesActivation g₁) (hg₂ : OpenNodeContext.PreservesActivation g₂)
    (hc : c.boundary.isActivated = false) (hd : d.boundary.isActivated = false) :
    OpenProcessActivationEquiv (p₁.interleave p₂ f₁ f₂ c σ) (p₂.interleave p₁ g₁ g₂ d τ) := by
  refine OpenProcessActivationEquiv.of_step_match
    (fun ⟨s₁, s₂⟩ ⟨s₂', s₁'⟩ => s₁ = s₁' ∧ s₂ = s₂')
    (fun ⟨s₁, s₂⟩ => ⟨⟨s₂, s₁⟩, rfl, rfl⟩)
    (fun ⟨s₂, s₁⟩ => ⟨⟨s₁, s₂⟩, rfl, rfl⟩) ?_ ?_ ?_ ?_
  all_goals intro ⟨s₁, s₂⟩ ⟨s₂', s₁'⟩ ⟨h1, h2⟩
  all_goals subst h1; subst h2
  · rintro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      exact .inl ⟨⟨⟨false⟩, rest⟩,
        (isSilentStep_interleave_right_iff p₂ p₁ g₁ hg₂ hd τ _ _ _).mpr
          ((isSilentStep_interleave_left_iff p₁ p₂ f₂ hf₁ hc σ _ _ _).mp hsilent), rfl, rfl⟩
    | false =>
      exact .inl ⟨⟨⟨true⟩, rest⟩,
        (isSilentStep_interleave_left_iff p₂ p₁ g₂ hg₁ hd τ _ _ _).mpr
          ((isSilentStep_interleave_right_iff p₁ p₂ f₁ hf₂ hc σ _ _ _).mp hsilent), rfl, rfl⟩
  · rintro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      exact ⟨⟨⟨false⟩, rest⟩, fun hs => hvisible
        ((isSilentStep_interleave_left_iff p₁ p₂ f₂ hf₁ hc σ _ _ _).mpr
          ((isSilentStep_interleave_right_iff p₂ p₁ g₁ hg₂ hd τ _ _ _).mp hs)), rfl, rfl⟩
    | false =>
      exact ⟨⟨⟨true⟩, rest⟩, fun hs => hvisible
        ((isSilentStep_interleave_right_iff p₁ p₂ f₁ hf₂ hc σ _ _ _).mpr
          ((isSilentStep_interleave_left_iff p₂ p₁ g₂ hg₁ hd τ _ _ _).mp hs)), rfl, rfl⟩
  · rintro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      exact .inl ⟨⟨⟨false⟩, rest⟩,
        (isSilentStep_interleave_right_iff p₁ p₂ f₁ hf₂ hc σ _ _ _).mpr
          ((isSilentStep_interleave_left_iff p₂ p₁ g₂ hg₁ hd τ _ _ _).mp hsilent), rfl, rfl⟩
    | false =>
      exact .inl ⟨⟨⟨true⟩, rest⟩,
        (isSilentStep_interleave_left_iff p₁ p₂ f₂ hf₁ hc σ _ _ _).mpr
          ((isSilentStep_interleave_right_iff p₂ p₁ g₁ hg₂ hd τ _ _ _).mp hsilent), rfl, rfl⟩
  · rintro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      exact ⟨⟨⟨false⟩, rest⟩, fun hs => hvisible
        ((isSilentStep_interleave_left_iff p₂ p₁ g₂ hg₁ hd τ _ _ _).mpr
          ((isSilentStep_interleave_right_iff p₁ p₂ f₁ hf₂ hc σ _ _ _).mp hs)), rfl, rfl⟩
    | false =>
      exact ⟨⟨⟨true⟩, rest⟩, fun hs => hvisible
        ((isSilentStep_interleave_right_iff p₂ p₁ g₁ hg₂ hd τ _ _ _).mpr
          ((isSilentStep_interleave_left_iff p₁ p₂ f₂ hf₁ hc σ _ _ _).mp hs)), rfl, rfl⟩

/-- **Re-homing.** Changing the injections, scheduler node, and scheduler
sampler of an interleaving preserves activation equivalence. -/
theorem interleave_rehome_activationEquiv
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)} (σ : m (ULift.{w, 0} Bool))
    {g₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    {g₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ)}
    {d : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)} (τ : m (ULift.{w, 0} Bool))
    (hf₁ : OpenNodeContext.PreservesActivation f₁) (hf₂ : OpenNodeContext.PreservesActivation f₂)
    (hg₁ : OpenNodeContext.PreservesActivation g₁) (hg₂ : OpenNodeContext.PreservesActivation g₂)
    (hc : c.boundary.isActivated = false) (hd : d.boundary.isActivated = false) :
    OpenProcessActivationEquiv (p₁.interleave p₂ f₁ f₂ c σ) (p₁.interleave p₂ g₁ g₂ d τ) := by
  have key : ∀ (s₁ : p₁.Proc) (s₂ : p₂.Proc)
      (tr : ((p₁.interleave p₂ f₁ f₂ c σ).step (s₁, s₂)).tree.Path),
      IsSilentStep (p₁.interleave p₂ f₁ f₂ c σ) (s₁, s₂) tr ↔
        IsSilentStep (p₁.interleave p₂ g₁ g₂ d τ) (s₁, s₂) tr := by
    rintro s₁ s₂ ⟨⟨b⟩, rest⟩
    cases b
    · exact (isSilentStep_interleave_right_iff p₁ p₂ f₁ hf₂ hc σ _ _ _).trans
        (isSilentStep_interleave_right_iff p₁ p₂ g₁ hg₂ hd τ _ _ _).symm
    · exact (isSilentStep_interleave_left_iff p₁ p₂ f₂ hf₁ hc σ _ _ _).trans
        (isSilentStep_interleave_left_iff p₁ p₂ g₂ hg₁ hd τ _ _ _).symm
  refine OpenProcessActivationEquiv.of_step_match Eq (fun s => ⟨s, rfl⟩) (fun s => ⟨s, rfl⟩)
    ?_ ?_ ?_ ?_
  all_goals rintro ⟨s₁, s₂⟩ _ rfl
  · intro tr hsilent
    exact .inl ⟨tr, (key s₁ s₂ tr).mp hsilent, rfl⟩
  · intro tr hvisible
    exact ⟨tr, fun hs => hvisible ((key s₁ s₂ tr).mpr hs), rfl⟩
  · intro tr hsilent
    exact .inl ⟨tr, (key s₁ s₂ tr).mpr hsilent, rfl⟩
  · intro tr hvisible
    exact ⟨tr, fun hs => hvisible ((key s₁ s₂ tr).mp hs), rfl⟩

end Shapes

section Units

variable {Δ₀ Δ : PortBoundary}

open OpenProcess

/-- **Left absorption.** Interleaving a process all of whose steps are silent
on the left is invisible to activation equivalence. -/
theorem interleave_unit_left_activationEquiv
    (u : OpenProcess.{u, v, w, w'} m Party Δ₀) [Inhabited u.Proc]
    (p : OpenProcess.{u, v, w, w'} m Party Δ)
    (hu : ∀ (s : u.Proc) (tr : (u.step s).tree.Path), IsSilentStep u s tr)
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₀)
      (OpenNodeContext.{u, w} Party Δ)}
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ)
      (OpenNodeContext.{u, w} Party Δ)}
    (hf₁ : OpenNodeContext.PreservesActivation f₁) (hf₂ : OpenNodeContext.PreservesActivation f₂)
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (hc : c.boundary.isActivated = false) (σ : m (ULift.{w, 0} Bool)) :
    OpenProcessActivationEquiv (u.interleave p f₁ f₂ c σ) p := by
  refine OpenProcessActivationEquiv.of_step_match (fun s₁ s₂ => s₁.2 = s₂)
    (fun ⟨_, s⟩ => ⟨s, rfl⟩) (fun s => ⟨⟨default, s⟩, rfl⟩) ?_ ?_ ?_ ?_
  all_goals intro ⟨t, s⟩ s₂ heq
  all_goals subst heq
  · rintro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true => exact .inr rfl
    | false =>
      exact .inl ⟨rest, (isSilentStep_interleave_right_iff u p f₁ hf₂ hc σ _ _ _).mp hsilent, rfl⟩
  · rintro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      exact absurd ((isSilentStep_interleave_left_iff u p f₂ hf₁ hc σ _ _ _).mpr (hu t rest))
        hvisible
    | false =>
      exact ⟨rest,
        fun hs => hvisible ((isSilentStep_interleave_right_iff u p f₁ hf₂ hc σ _ _ _).mpr hs),
        rfl⟩
  · intro tr hsilent
    exact .inl ⟨⟨⟨false⟩, tr⟩,
      (isSilentStep_interleave_right_iff u p f₁ hf₂ hc σ _ _ _).mpr hsilent,
      rfl⟩
  · intro tr hvisible
    exact ⟨⟨⟨false⟩, tr⟩,
      fun hs => hvisible ((isSilentStep_interleave_right_iff u p f₁ hf₂ hc σ _ _ _).mp hs),
      rfl⟩

/-- **Right absorption.** Interleaving a process all of whose steps are silent
on the right is invisible to activation equivalence. -/
theorem interleave_unit_right_activationEquiv
    (p : OpenProcess.{u, v, w, w'} m Party Δ) (u : OpenProcess.{u, v, w, w'} m Party Δ₀)
    [Inhabited u.Proc]
    (hu : ∀ (s : u.Proc) (tr : (u.step s).tree.Path), IsSilentStep u s tr)
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ)
      (OpenNodeContext.{u, w} Party Δ)}
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₀)
      (OpenNodeContext.{u, w} Party Δ)}
    (hf₁ : OpenNodeContext.PreservesActivation f₁) (hf₂ : OpenNodeContext.PreservesActivation f₂)
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (hc : c.boundary.isActivated = false) (σ : m (ULift.{w, 0} Bool)) :
    OpenProcessActivationEquiv (p.interleave u f₁ f₂ c σ) p := by
  refine OpenProcessActivationEquiv.of_step_match (fun s₁ s₂ => s₁.1 = s₂)
    (fun ⟨s, _⟩ => ⟨s, rfl⟩) (fun s => ⟨⟨s, default⟩, rfl⟩) ?_ ?_ ?_ ?_
  all_goals intro ⟨s, t⟩ s₂ heq
  all_goals subst heq
  · rintro ⟨⟨b⟩, rest⟩ hsilent
    match b with
    | true =>
      exact .inl ⟨rest, (isSilentStep_interleave_left_iff p u f₂ hf₁ hc σ _ _ _).mp hsilent, rfl⟩
    | false => exact .inr rfl
  · rintro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      exact ⟨rest,
        fun hs => hvisible ((isSilentStep_interleave_left_iff p u f₂ hf₁ hc σ _ _ _).mpr hs),
        rfl⟩
    | false =>
      exact absurd ((isSilentStep_interleave_right_iff p u f₁ hf₂ hc σ _ _ _).mpr (hu t rest))
        hvisible
  · intro tr hsilent
    exact .inl ⟨⟨⟨true⟩, tr⟩,
      (isSilentStep_interleave_left_iff p u f₂ hf₁ hc σ _ _ _).mpr hsilent, rfl⟩
  · intro tr hvisible
    exact ⟨⟨⟨true⟩, tr⟩,
      fun hs => hvisible ((isSilentStep_interleave_left_iff p u f₂ hf₁ hc σ _ _ _).mp hs),
      rfl⟩

end Units

/-! ## Congruence -/

section Congruence

open OpenProcess Control

variable {Δ₁ Δ₂ Δ : PortBoundary}

/-- The activation label of a left-scheduled composite step is the component's label. -/
theorem OpenProcess.activationLTS_label_interleave_left
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ)}
    (f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (hf₁ : OpenNodeContext.PreservesActivation f₁)
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (hc : c.boundary.isActivated = false) (σ : m (ULift.{w, 0} Bool))
    (s₁ : p₁.Proc) (s₂ : p₂.Proc) (tr : (p₁.step s₁).tree.Path) :
    (p₁.interleave p₂ f₁ f₂ c σ).activationLTS.label (s₁, s₂) ⟨⟨true⟩, tr⟩ =
      p₁.activationLTS.label s₁ tr := by
  by_cases h : IsSilentStep p₁ s₁ tr
  · rw [activationLTS_label_of_silent _ _ _ h, activationLTS_label_of_silent]
    exact (isSilentStep_interleave_left_iff p₁ p₂ f₂ hf₁ hc σ s₁ s₂ tr).mpr h
  · rw [activationLTS_label_of_not_silent _ _ _ h, activationLTS_label_of_not_silent]
    exact fun h' => h ((isSilentStep_interleave_left_iff p₁ p₂ f₂ hf₁ hc σ s₁ s₂ tr).mp h')

/-- The activation label of a right-scheduled composite step is the component's label. -/
theorem OpenProcess.activationLTS_label_interleave_right
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ)}
    (hf₂ : OpenNodeContext.PreservesActivation f₂)
    {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}
    (hc : c.boundary.isActivated = false) (σ : m (ULift.{w, 0} Bool))
    (s₁ : p₁.Proc) (s₂ : p₂.Proc) (tr : (p₂.step s₂).tree.Path) :
    (p₁.interleave p₂ f₁ f₂ c σ).activationLTS.label (s₁, s₂) ⟨⟨false⟩, tr⟩ =
      p₂.activationLTS.label s₂ tr := by
  by_cases h : IsSilentStep p₂ s₂ tr
  · rw [activationLTS_label_of_silent _ _ _ h, activationLTS_label_of_silent]
    exact (isSilentStep_interleave_right_iff p₁ p₂ f₁ hf₂ hc σ s₁ s₂ tr).mpr h
  · rw [activationLTS_label_of_not_silent _ _ _ h, activationLTS_label_of_not_silent]
    exact fun h' => h ((isSilentStep_interleave_right_iff p₁ p₂ f₁ hf₂ hc σ s₁ s₂ tr).mp h')


/-! ### Lifting component steps to the composite -/

variable (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁) (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
  {f₁ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁) (OpenNodeContext.{u, w} Party Δ)}
  {f₂ : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₂) (OpenNodeContext.{u, w} Party Δ)}
  {c : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool)}

/-- A step of the left component is a step of the composite. -/
theorem OpenProcess.activationLTS_step_interleave_left
    (hf₁ : OpenNodeContext.PreservesActivation f₁) (hc : c.boundary.isActivated = false)
    (σ : m (ULift.{w, 0} Bool)) {s₁ s₁' : p₁.Proc} (s₂ : p₂.Proc)
    {lab : Option Unit} (h : p₁.activationLTS.Step s₁ lab s₁') :
    (p₁.interleave p₂ f₁ f₂ c σ).activationLTS.Step (s₁, s₂) lab (s₁', s₂) := by
  obtain ⟨tr, hlab, hnext⟩ := h
  exact ⟨⟨⟨true⟩, tr⟩, (activationLTS_label_interleave_left p₁ p₂ f₂ hf₁ hc σ s₁ s₂ tr).trans hlab,
    Prod.ext hnext rfl⟩

/-- A step of the right component is a step of the composite. -/
theorem OpenProcess.activationLTS_step_interleave_right
    (hf₂ : OpenNodeContext.PreservesActivation f₂) (hc : c.boundary.isActivated = false)
    (σ : m (ULift.{w, 0} Bool)) (s₁ : p₁.Proc) {s₂ s₂' : p₂.Proc}
    {lab : Option Unit} (h : p₂.activationLTS.Step s₂ lab s₂') :
    (p₁.interleave p₂ f₁ f₂ c σ).activationLTS.Step (s₁, s₂) lab (s₁, s₂') := by
  obtain ⟨tr, hlab, hnext⟩ := h
  exact ⟨⟨⟨false⟩, tr⟩,
    (activationLTS_label_interleave_right p₁ p₂ f₁ hf₂ hc σ s₁ s₂ tr).trans hlab,
    Prod.ext rfl hnext⟩

/-- Silent runs of the left component lift to the composite. -/
theorem OpenProcess.activationLTS_silentSteps_interleave_left
    (hf₁ : OpenNodeContext.PreservesActivation f₁) (hc : c.boundary.isActivated = false)
    (σ : m (ULift.{w, 0} Bool)) {s₁ s₁' : p₁.Proc} (s₂ : p₂.Proc)
    (h : p₁.activationLTS.SilentSteps s₁ s₁') :
    (p₁.interleave p₂ f₁ f₂ c σ).activationLTS.SilentSteps (s₁, s₂) (s₁', s₂) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact ih.tail (activationLTS_step_interleave_left p₁ p₂ hf₁ hc σ s₂ hstep)

/-- Silent runs of the right component lift to the composite. -/
theorem OpenProcess.activationLTS_silentSteps_interleave_right
    (hf₂ : OpenNodeContext.PreservesActivation f₂) (hc : c.boundary.isActivated = false)
    (σ : m (ULift.{w, 0} Bool)) (s₁ : p₁.Proc) {s₂ s₂' : p₂.Proc}
    (h : p₂.activationLTS.SilentSteps s₂ s₂') :
    (p₁.interleave p₂ f₁ f₂ c σ).activationLTS.SilentSteps (s₁, s₂) (s₁, s₂') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact ih.tail (activationLTS_step_interleave_right p₁ p₂ hf₂ hc σ s₁ hstep)

/-- Delay steps of the left component lift to the composite. -/
theorem OpenProcess.activationLTS_delayStep_interleave_left
    (hf₁ : OpenNodeContext.PreservesActivation f₁) (hc : c.boundary.isActivated = false)
    (σ : m (ULift.{w, 0} Bool)) {s₁ s₁' : p₁.Proc} (s₂ : p₂.Proc)
    {lab : Option Unit} (h : p₁.activationLTS.DelayStep s₁ lab s₁') :
    (p₁.interleave p₂ f₁ f₂ c σ).activationLTS.DelayStep (s₁, s₂) lab (s₁', s₂) := by
  cases lab with
  | none => exact activationLTS_silentSteps_interleave_left p₁ p₂ hf₁ hc σ s₂ h
  | some o =>
    obtain ⟨mid, hs, hv⟩ := h
    exact ⟨(mid, s₂), activationLTS_silentSteps_interleave_left p₁ p₂ hf₁ hc σ s₂ hs,
      activationLTS_step_interleave_left p₁ p₂ hf₁ hc σ s₂ hv⟩

/-- Delay steps of the right component lift to the composite. -/
theorem OpenProcess.activationLTS_delayStep_interleave_right
    (hf₂ : OpenNodeContext.PreservesActivation f₂) (hc : c.boundary.isActivated = false)
    (σ : m (ULift.{w, 0} Bool)) (s₁ : p₁.Proc) {s₂ s₂' : p₂.Proc}
    {lab : Option Unit} (h : p₂.activationLTS.DelayStep s₂ lab s₂') :
    (p₁.interleave p₂ f₁ f₂ c σ).activationLTS.DelayStep (s₁, s₂) lab (s₁, s₂') := by
  cases lab with
  | none => exact activationLTS_silentSteps_interleave_right p₁ p₂ hf₂ hc σ s₁ h
  | some o =>
    obtain ⟨mid, hs, hv⟩ := h
    exact ⟨(s₁, mid), activationLTS_silentSteps_interleave_right p₁ p₂ hf₂ hc σ s₁ hs,
      activationLTS_step_interleave_right p₁ p₂ hf₂ hc σ s₁ hv⟩

/-- Every step of the composite is a step of exactly one component. -/
theorem OpenProcess.activationLTS_step_interleave_cases
    (hf₁ : OpenNodeContext.PreservesActivation f₁)
    (hf₂ : OpenNodeContext.PreservesActivation f₂)
    (hc : c.boundary.isActivated = false) (σ : m (ULift.{w, 0} Bool)) {s₁ : p₁.Proc} {s₂ : p₂.Proc}
    {lab : Option Unit} {u : p₁.Proc × p₂.Proc}
    (h : (p₁.interleave p₂ f₁ f₂ c σ).activationLTS.Step (s₁, s₂) lab u) :
    (∃ s₁', p₁.activationLTS.Step s₁ lab s₁' ∧ u = (s₁', s₂)) ∨
      (∃ s₂', p₂.activationLTS.Step s₂ lab s₂' ∧ u = (s₁, s₂')) := by
  obtain ⟨⟨⟨b⟩, tr⟩, hlab, hnext⟩ := h
  cases b
  · right
    exact ⟨(p₂.step s₂).next tr,
      ⟨tr, (activationLTS_label_interleave_right p₁ p₂ f₁ hf₂ hc σ s₁ s₂ tr).symm.trans hlab, rfl⟩,
      hnext.symm⟩
  · left
    exact ⟨(p₁.step s₁).next tr,
      ⟨tr, (activationLTS_label_interleave_left p₁ p₂ f₂ hf₁ hc σ s₁ s₂ tr).symm.trans hlab, rfl⟩,
      hnext.symm⟩

/-! ### Interleaving is a congruence -/

/-- Activation equivalence is preserved by interleaving on the left, for any
scheduler samplers. -/
theorem OpenProcess.interleave_congr_left
    (hf₁ : OpenNodeContext.PreservesActivation f₁)
    (hf₂ : OpenNodeContext.PreservesActivation f₂)
    (hc : c.boundary.isActivated = false) (σ : m (ULift.{w, 0} Bool))
    {q₁ : OpenProcess.{u, v, w, w'} m Party Δ₁}
    (h : OpenProcessActivationEquiv p₁ q₁) (τ : m (ULift.{w, 0} Bool)) :
    OpenProcessActivationEquiv (p₁.interleave p₂ f₁ f₂ c σ) (q₁.interleave p₂ f₁ f₂ c τ) := by
  obtain ⟨rel, ⟨hfwd, hbwd⟩, htot₁, htot₂⟩ := h
  refine ⟨fun a b => rel a.1 b.1 ∧ a.2 = b.2, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨s₁, s₂⟩ ⟨t₁, t₂⟩ ⟨hrel, hst⟩ lab u hstep
    dsimp only at hrel hst
    subst hst
    rcases activationLTS_step_interleave_cases p₁ p₂ hf₁ hf₂ hc σ hstep with
      ⟨s₁', hs, rfl⟩ | ⟨s₂', hs, rfl⟩
    · obtain ⟨t₁', hd, hrel'⟩ := hfwd hrel hs
      exact ⟨(t₁', s₂), activationLTS_delayStep_interleave_left q₁ p₂ hf₁ hc τ s₂ hd, hrel', rfl⟩
    · exact ⟨(t₁, s₂'), (activationLTS_step_interleave_right q₁ p₂ hf₂ hc τ t₁ hs).delay, hrel,
        rfl⟩
  · rintro ⟨t₁, t₂⟩ ⟨s₁, s₂⟩ ⟨hrel, hst⟩ lab u hstep
    dsimp only at hrel hst
    subst hst
    rcases activationLTS_step_interleave_cases q₁ p₂ hf₁ hf₂ hc τ hstep with
      ⟨t₁', hs, rfl⟩ | ⟨t₂', hs, rfl⟩
    · obtain ⟨s₁', hd, hrel'⟩ := hbwd hrel hs
      exact ⟨(s₁', s₂), activationLTS_delayStep_interleave_left p₁ p₂ hf₁ hc σ s₂ hd, hrel', rfl⟩
    · exact ⟨(s₁, t₂'), (activationLTS_step_interleave_right p₁ p₂ hf₂ hc σ s₁ hs).delay, hrel,
        rfl⟩
  · rintro ⟨s₁, s₂⟩
    obtain ⟨t₁, ht⟩ := htot₁ s₁
    exact ⟨(t₁, s₂), ht, rfl⟩
  · rintro ⟨t₁, t₂⟩
    obtain ⟨s₁, hs⟩ := htot₂ t₁
    exact ⟨(s₁, t₂), hs, rfl⟩

/-- Activation equivalence is preserved by interleaving on the right, for any
scheduler samplers. -/
theorem OpenProcess.interleave_congr_right
    (hf₁ : OpenNodeContext.PreservesActivation f₁)
    (hf₂ : OpenNodeContext.PreservesActivation f₂)
    (hc : c.boundary.isActivated = false) (σ : m (ULift.{w, 0} Bool))
    {q₂ : OpenProcess.{u, v, w, w'} m Party Δ₂}
    (h : OpenProcessActivationEquiv p₂ q₂) (τ : m (ULift.{w, 0} Bool)) :
    OpenProcessActivationEquiv (p₁.interleave p₂ f₁ f₂ c σ) (p₁.interleave q₂ f₁ f₂ c τ) := by
  obtain ⟨rel, ⟨hfwd, hbwd⟩, htot₁, htot₂⟩ := h
  refine ⟨fun a b => a.1 = b.1 ∧ rel a.2 b.2, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨s₁, s₂⟩ ⟨t₁, t₂⟩ ⟨hst, hrel⟩ lab u hstep
    dsimp only at hrel hst
    subst hst
    rcases activationLTS_step_interleave_cases p₁ p₂ hf₁ hf₂ hc σ hstep with
      ⟨s₁', hs, rfl⟩ | ⟨s₂', hs, rfl⟩
    · exact ⟨(s₁', t₂), (activationLTS_step_interleave_left p₁ q₂ hf₁ hc τ t₂ hs).delay, rfl,
        hrel⟩
    · obtain ⟨t₂', hd, hrel'⟩ := hfwd hrel hs
      exact ⟨(s₁, t₂'), activationLTS_delayStep_interleave_right p₁ q₂ hf₂ hc τ s₁ hd, rfl, hrel'⟩
  · rintro ⟨t₁, t₂⟩ ⟨s₁, s₂⟩ ⟨hst, hrel⟩ lab u hstep
    dsimp only at hrel hst
    subst hst
    rcases activationLTS_step_interleave_cases p₁ q₂ hf₁ hf₂ hc τ hstep with
      ⟨t₁', hs, rfl⟩ | ⟨t₂', hs, rfl⟩
    · exact ⟨(t₁', s₂), (activationLTS_step_interleave_left p₁ p₂ hf₁ hc σ s₂ hs).delay, rfl,
        hrel⟩
    · obtain ⟨s₂', hd, hrel'⟩ := hbwd hrel hs
      exact ⟨(s₁, s₂'), activationLTS_delayStep_interleave_right p₁ p₂ hf₂ hc σ s₁ hd, rfl, hrel'⟩
  · rintro ⟨s₁, s₂⟩
    obtain ⟨t₂, ht⟩ := htot₁ s₂
    exact ⟨(s₁, t₂), rfl, ht⟩
  · rintro ⟨t₁, t₂⟩
    obtain ⟨s₂, hs⟩ := htot₂ t₂
    exact ⟨(t₁, s₂), rfl, hs⟩

/-! ### Re-decoration is a congruence -/

/-- Re-decoration along an activation-preserving hom does not change activation labels. -/
theorem OpenProcess.activationLTS_label_mapHom {Δ' : PortBoundary}
    {h : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ)
      (OpenNodeContext.{u, w} Party Δ')}
    (hh : OpenNodeContext.PreservesActivation h) (op : OpenProcess.{u, v, w, w'} m Party Δ)
    (s : op.Proc) (tr : (op.step s).tree.Path) :
    (op.mapHom h).activationLTS.label s tr = op.activationLTS.label s tr := by
  by_cases hs : IsSilentStep op s tr
  · rw [activationLTS_label_of_silent _ _ _ hs,
      activationLTS_label_of_silent _ _ _ ((isSilentStep_mapHom_iff hh op s tr).mpr hs)]
  · rw [activationLTS_label_of_not_silent _ _ _ hs,
      activationLTS_label_of_not_silent _ _ _
        (fun h' => hs ((isSilentStep_mapHom_iff hh op s tr).mp h'))]

/-- Re-decoration along an activation-preserving hom has the same activation steps. -/
theorem OpenProcess.activationLTS_step_mapHom_iff {Δ' : PortBoundary}
    {h : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ)
      (OpenNodeContext.{u, w} Party Δ')}
    (hh : OpenNodeContext.PreservesActivation h) (op : OpenProcess.{u, v, w, w'} m Party Δ)
    {s t : op.Proc} {lab : Option Unit} :
    (op.mapHom h).activationLTS.Step s lab t ↔ op.activationLTS.Step s lab t := by
  constructor
  · rintro ⟨tr, hlab, hnext⟩
    exact ⟨tr, (activationLTS_label_mapHom hh op s tr).symm.trans hlab, hnext⟩
  · rintro ⟨tr, hlab, hnext⟩
    exact ⟨tr, (activationLTS_label_mapHom hh op s tr).trans hlab, hnext⟩

/-- Re-decoration along an activation-preserving hom has the same silent runs. -/
theorem OpenProcess.activationLTS_silentSteps_mapHom_iff {Δ' : PortBoundary}
    {h : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ)
      (OpenNodeContext.{u, w} Party Δ')}
    (hh : OpenNodeContext.PreservesActivation h) (op : OpenProcess.{u, v, w, w'} m Party Δ)
    {s t : op.Proc} :
    (op.mapHom h).activationLTS.SilentSteps s t ↔ op.activationLTS.SilentSteps s t := by
  constructor
  · intro hst
    induction hst with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail ((activationLTS_step_mapHom_iff hh op).mp hstep)
  · intro hst
    induction hst with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail ((activationLTS_step_mapHom_iff hh op).mpr hstep)

/-- Re-decoration along an activation-preserving hom has the same delay steps. -/
theorem OpenProcess.activationLTS_delayStep_mapHom_iff {Δ' : PortBoundary}
    {h : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ)
      (OpenNodeContext.{u, w} Party Δ')}
    (hh : OpenNodeContext.PreservesActivation h) (op : OpenProcess.{u, v, w, w'} m Party Δ)
    {s t : op.Proc} {lab : Option Unit} :
    (op.mapHom h).activationLTS.DelayStep s lab t ↔ op.activationLTS.DelayStep s lab t := by
  cases lab with
  | none => exact activationLTS_silentSteps_mapHom_iff hh op
  | some o =>
    constructor
    · rintro ⟨mid, hs, hv⟩
      exact ⟨mid, (activationLTS_silentSteps_mapHom_iff hh op).mp hs,
        (activationLTS_step_mapHom_iff hh op).mp hv⟩
    · rintro ⟨mid, hs, hv⟩
      exact ⟨mid, (activationLTS_silentSteps_mapHom_iff hh op).mpr hs,
        (activationLTS_step_mapHom_iff hh op).mpr hv⟩

/-- Activation equivalence is preserved by re-decoration along an
activation-preserving hom. -/
theorem OpenProcess.mapHom_congr {Δ' : PortBoundary}
    {h : TypeTree.Node.ContextHom (OpenNodeContext.{u, w} Party Δ)
      (OpenNodeContext.{u, w} Party Δ')}
    (hh : OpenNodeContext.PreservesActivation h)
    {op op' : OpenProcess.{u, v, w, w'} m Party Δ} (he : OpenProcessActivationEquiv op op') :
    OpenProcessActivationEquiv (op.mapHom h) (op'.mapHom h) := by
  obtain ⟨rel, ⟨hfwd, hbwd⟩, htot₁, htot₂⟩ := he
  refine ⟨rel, ⟨?_, ?_⟩, htot₁, htot₂⟩
  · intro s t hrel lab s' hstep
    obtain ⟨t', hd, hrel'⟩ := hfwd hrel ((activationLTS_step_mapHom_iff hh op).mp hstep)
    exact ⟨t', (activationLTS_delayStep_mapHom_iff hh op').mpr hd, hrel'⟩
  · intro t s hrel lab t' hstep
    obtain ⟨s', hd, hrel'⟩ := hbwd hrel ((activationLTS_step_mapHom_iff hh op').mp hstep)
    exact ⟨s', (activationLTS_delayStep_mapHom_iff hh op).mpr hd, hrel'⟩

end Congruence

end UC
end Interaction
