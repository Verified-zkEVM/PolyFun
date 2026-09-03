/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Concurrent.Process

/-!
# Routed binary interleaving

`ProcessOver.interleave` prepends a scheduler node and advances only the
scheduled component. `ProcessOver.interleaveRouted` keeps exactly that shape
and adds a *routing hook*: once the scheduled component has completed a step
path, a route may update the other component's state from that path. With the
trivial routes it is `interleave` on the nose (`interleave_eq_interleaveRouted`).

The hook is the structural substrate for communicating compositions of open
systems, where a route delivers the packets emitted along a step to the other
side. This module knows nothing about boundaries or packets: a route is an
arbitrary function of the scheduled side's state and completed path, which is
what lets the context-mapping lemmas hold verbatim for the routed form.
-/

public section

universe v w w₂

namespace Interaction
namespace Concurrent
namespace ProcessOver

/-- A route from a process to a state space: how a completed step path of the
process at a given state updates the other side's state. -/
abbrev Route {P₁ : Type v} {Γ₁ : Interaction.TypeTree.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁) (P₂ : Type v) : Type (max v w) :=
  ∀ s₁ : p₁.Proc, PFunctor.FreeM.Path (p₁.step s₁).tree → P₂ → P₂

/-- The trivial route leaves the other side untouched. -/
abbrev Route.trivial {P₁ P₂ : Type v} {Γ₁ : Interaction.TypeTree.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁) : Route p₁ P₂ :=
  fun _ _ s => s

/--
Binary-choice interleaving with routing hooks.

As in `interleave`, a scheduler node chooses left (`true`) or right (`false`)
and the selected component's step protocol runs with its decoration mapped into
`Δ`. In addition, the completed path of the selected component is handed to
`route₁` (respectively `route₂`), which updates the *other* component's state.
-/
@[expose]
def interleaveRouted
    {P₁ P₂ : Type v}
    {Γ₁ Γ₂ Δ : Interaction.TypeTree.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁)
    (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (f₁ : Interaction.TypeTree.Node.ContextHom Γ₁ Δ)
    (f₂ : Interaction.TypeTree.Node.ContextHom Γ₂ Δ)
    (schedulerCtx : Δ (ULift.{w} Bool))
    (route₁ : Route p₁ P₂) (route₂ : Route p₂ P₁) : ProcessOver.{v, w, w₂} (P₁ × P₂) Δ :=
  ofStep (p₁.Proc × p₂.Proc) fun (s₁, s₂) =>
    let step₁ := p₁.step s₁
    let step₂ := p₂.step s₂
    { tree := .node (ULift.{w} Bool) fun
        | ⟨true⟩ => step₁.tree
        | ⟨false⟩ => step₂.tree
      semantics :=
        ⟨schedulerCtx, fun
          | ⟨true⟩ => PFunctor.FreeM.Displayed.Decoration.map f₁ step₁.tree step₁.semantics
          | ⟨false⟩ => PFunctor.FreeM.Displayed.Decoration.map f₂ step₂.tree step₂.semantics⟩
      next := fun
        | ⟨⟨true⟩, tr⟩ => (step₁.next tr, route₁ s₁ tr s₂)
        | ⟨⟨false⟩, tr⟩ => (route₂ s₂ tr s₁, step₂.next tr) }

/-- Interleaving is routed interleaving with the trivial routes. -/
theorem interleave_eq_interleaveRouted
    {P₁ P₂ : Type v}
    {Γ₁ Γ₂ Δ : Interaction.TypeTree.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁) (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (f₁ : Interaction.TypeTree.Node.ContextHom Γ₁ Δ)
    (f₂ : Interaction.TypeTree.Node.ContextHom Γ₂ Δ)
    (sched : Δ (ULift.{w} Bool)) :
    p₁.interleave p₂ f₁ f₂ sched =
      p₁.interleaveRouted p₂ f₁ f₂ sched (Route.trivial p₁) (Route.trivial p₂) :=
  rfl

/-- Post-composing `mapContext g` distributes over `interleaveRouted`: the
result is the same routed interleaving with each injection pre-composed by
`g`. Routes are untouched because they never see the decoration. -/
theorem mapContext_interleaveRouted
    {P₁ P₂ : Type v}
    {Γ₁ Γ₂ Δ Δ' : Interaction.TypeTree.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁) (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (f₁ : Interaction.TypeTree.Node.ContextHom Γ₁ Δ)
    (f₂ : Interaction.TypeTree.Node.ContextHom Γ₂ Δ)
    (sched : Δ (ULift.{w} Bool))
    (route₁ : Route p₁ P₂) (route₂ : Route p₂ P₁)
    (g : Interaction.TypeTree.Node.ContextHom Δ Δ') :
    (p₁.interleaveRouted p₂ f₁ f₂ sched route₁ route₂).mapContext g =
      p₁.interleaveRouted p₂
        (Interaction.TypeTree.Node.ContextHom.comp g f₁)
        (Interaction.TypeTree.Node.ContextHom.comp g f₂)
        (g _ sched) route₁ route₂ := by
  simp only [mapContext, interleaveRouted, StepOver.mapContext]
  refine ofStep_congr fun ⟨s₁, s₂⟩ => ?_
  dsimp only [ofStep, PFunctor.DynSystem.expose_mk', PFunctor.DynSystem.update_mk']
  congr 1
  simp only [PFunctor.FreeM.liftBind_eq]
  rw [PFunctor.FreeM.Displayed.Decoration.map_liftBind]
  congr 1; funext ⟨b⟩
  cases b
  · exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.TypeTree.basePFunctor) (α := PUnit.{w+1})
        g f₂ _ _
  · exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.TypeTree.basePFunctor) (α := PUnit.{w+1})
        g f₁ _ _

/-- Pre-composing both operands with `mapContext` distributes into the
`interleaveRouted` injections via `ContextHom.comp`. The routes are the same
functions, since `mapContext` preserves every step tree. -/
theorem interleaveRouted_mapContext
    {P₁ P₂ : Type v}
    {Γ₁ Γ₁' Γ₂ Γ₂' Δ : Interaction.TypeTree.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁) (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (g₁ : Interaction.TypeTree.Node.ContextHom Γ₁ Γ₁')
    (g₂ : Interaction.TypeTree.Node.ContextHom Γ₂ Γ₂')
    (f₁ : Interaction.TypeTree.Node.ContextHom Γ₁' Δ)
    (f₂ : Interaction.TypeTree.Node.ContextHom Γ₂' Δ)
    (sched : Δ (ULift.{w} Bool))
    (route₁ : Route p₁ P₂) (route₂ : Route p₂ P₁) :
    (p₁.mapContext g₁).interleaveRouted (p₂.mapContext g₂) f₁ f₂ sched route₁ route₂ =
      p₁.interleaveRouted p₂
        (Interaction.TypeTree.Node.ContextHom.comp f₁ g₁)
        (Interaction.TypeTree.Node.ContextHom.comp f₂ g₂)
        sched route₁ route₂ := by
  simp only [mapContext, interleaveRouted, StepOver.mapContext]
  refine ofStep_congr fun ⟨s₁, s₂⟩ => ?_
  dsimp only [ofStep, PFunctor.DynSystem.expose_mk', PFunctor.DynSystem.update_mk']
  congr 1
  · congr 1; funext ⟨b⟩
    cases b
    · exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.TypeTree.basePFunctor) (α := PUnit.{w+1})
        f₂ g₂ _ _
    · exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.TypeTree.basePFunctor) (α := PUnit.{w+1})
        f₁ g₁ _ _
  · funext ⟨⟨b⟩, tr⟩; cases b <;> rfl

/-- Specialization of `interleaveRouted_mapContext` to the left operand. -/
theorem interleaveRouted_mapContext_left
    {P₁ P₂ : Type v}
    {Γ₁ Γ₁' Γ₂ Δ : Interaction.TypeTree.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁) (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (g₁ : Interaction.TypeTree.Node.ContextHom Γ₁ Γ₁')
    (f₁ : Interaction.TypeTree.Node.ContextHom Γ₁' Δ)
    (f₂ : Interaction.TypeTree.Node.ContextHom Γ₂ Δ)
    (sched : Δ (ULift.{w} Bool))
    (route₁ : Route p₁ P₂) (route₂ : Route p₂ P₁) :
    (p₁.mapContext g₁).interleaveRouted p₂ f₁ f₂ sched route₁ route₂ =
      p₁.interleaveRouted p₂
        (Interaction.TypeTree.Node.ContextHom.comp f₁ g₁) f₂ sched route₁ route₂ := by
  simp only [mapContext, interleaveRouted, StepOver.mapContext]
  refine ofStep_congr fun ⟨s₁, s₂⟩ => ?_
  dsimp only [ofStep, PFunctor.DynSystem.expose_mk', PFunctor.DynSystem.update_mk']
  congr 1
  · congr 1; funext ⟨b⟩
    cases b <;> dsimp
    exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.TypeTree.basePFunctor) (α := PUnit.{w+1})
        f₁ g₁ _ _
  · funext ⟨⟨b⟩, tr⟩; cases b <;> rfl

/-- Specialization of `interleaveRouted_mapContext` to the right operand. -/
theorem interleaveRouted_mapContext_right
    {P₁ P₂ : Type v}
    {Γ₁ Γ₂ Γ₂' Δ : Interaction.TypeTree.Node.Context.{w, w₂}}
    (p₁ : ProcessOver.{v, w, w₂} P₁ Γ₁) (p₂ : ProcessOver.{v, w, w₂} P₂ Γ₂)
    (g₂ : Interaction.TypeTree.Node.ContextHom Γ₂ Γ₂')
    (f₁ : Interaction.TypeTree.Node.ContextHom Γ₁ Δ)
    (f₂ : Interaction.TypeTree.Node.ContextHom Γ₂' Δ)
    (sched : Δ (ULift.{w} Bool))
    (route₁ : Route p₁ P₂) (route₂ : Route p₂ P₁) :
    p₁.interleaveRouted (p₂.mapContext g₂) f₁ f₂ sched route₁ route₂ =
      p₁.interleaveRouted p₂ f₁
        (Interaction.TypeTree.Node.ContextHom.comp f₂ g₂) sched route₁ route₂ := by
  simp only [mapContext, interleaveRouted, StepOver.mapContext]
  refine ofStep_congr fun ⟨s₁, s₂⟩ => ?_
  dsimp only [ofStep, PFunctor.DynSystem.expose_mk', PFunctor.DynSystem.update_mk']
  congr 1
  · congr 1; funext ⟨b⟩
    cases b <;> dsimp
    exact PFunctor.FreeM.Displayed.Decoration.map_comp
        (P := Interaction.TypeTree.basePFunctor) (α := PUnit.{w+1})
        f₂ g₂ _ _
  · funext ⟨⟨b⟩, tr⟩; cases b <;> rfl

end ProcessOver
end Concurrent
end Interaction
