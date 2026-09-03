/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.Interaction.Basic.Sampler
import PolyFun.Interaction.Concurrent.Fairness
import PolyFun.Interaction.Multiparty.Observation
import PolyFun.Interaction.UC.OpenProcess
import PolyFun.Interaction.UC.OpenProcessInterleave
import PolyFun.Interaction.UC.OpenProcessCoherence
import PolyFun.Interaction.UC.OpenTheory.PlugFactorization
import PolyFun.Interaction.UC.OpenTheory.Quotient
import PolyFun.Interaction.UC.EmulatesQuotient
import PolyFun.Interaction.UC.OpenProcessQuotient
import PolyFun.Interaction.UC.ScheduledOpenProcessModel
import PolyFun.Interaction.UC.ScheduledSamplerFactorization
import PolyFun.Interaction.UC.OpenProcessSamplerCoherence

/-!
# Ordinary-import canaries for the interaction API

These examples exercise public computation and characterization laws through
ordinary imports. They mirror downstream uses that otherwise tend to reach for
`import all` after a module-system migration.
-/

@[expose] public section

universe u v w w'

namespace PolyFunTest.ModuleAPI.Interaction

open _root_.Interaction

/-! ## Sampler equations -/

example {m : Type u → Type v} [Monad m] {X : Type u}
    (rest : X → TypeTree.{u}) (sampler : m X)
    (samplerRest : ∀ x, TypeTree.Sampler m (rest x)) :
    TypeTree.samplePath (TypeTree.node X rest) ⟨sampler, samplerRest⟩ = do
      let x ← sampler
      let path ← TypeTree.samplePath (rest x) (samplerRest x)
      return ⟨x, path⟩ :=
  TypeTree.samplePath_node rest sampler samplerRest

/-! ## Temporal and fairness laws -/

example {P : Nat → Prop} :
    Concurrent.ProcessOver.Run.EventuallyAlways P →
      Concurrent.ProcessOver.Run.InfinitelyOften P :=
  Concurrent.ProcessOver.Run.infinitelyOften_of_eventuallyAlways

example {Γ : TypeTree.Node.Context.{u, v}}
    (ticketed : Concurrent.ProcessOver.Ticketed Γ)
    (run : Concurrent.ProcessOver.Run ticketed.toProcess) :
    Concurrent.ProcessOver.Ticketed.StrongFair ticketed run →
      Concurrent.ProcessOver.Ticketed.WeakFair ticketed run :=
  Concurrent.ProcessOver.Ticketed.weakFair_of_strongFair ticketed run

/-! ## Observation factorization -/

example {X : Type u} (k₁ k₂ : Multiparty.Observation X)
    (factor : k₂.1 → k₁.1)
    (hfactor : ∀ x, k₁.2 x = factor (k₂.2 x)) : k₁ ≤ k₂ :=
  ⟨factor, hfactor⟩

/-! ## Open-process boundary traces -/

example {Party : Type u} {Δ : UC.PortBoundary} {P : Type v}
    (step : UC.OpenStep Party Δ P) (path : TypeTree.Path step.tree) :
    UC.OpenStep.boundaryTrace step path =
      UC.OpenNodeContext.boundaryTrace step.tree step.semantics path :=
  UC.OpenStep.boundaryTrace_eq step path

example {Party : Type u} {Δ : UC.PortBoundary} {X : Type w}
    (rest : X → TypeTree.{w})
    (semantics : TypeTree.Decoration (UC.OpenNodeContext.{u, w} Party Δ)
      (TypeTree.node X rest))
    (x : X) (path : TypeTree.Path (rest x)) :
    UC.OpenNodeContext.boundaryTrace (Party := Party) (Δ := Δ)
        (TypeTree.node X rest) semantics ⟨x, path⟩ =
      semantics.1.boundary.emit x *
        UC.OpenNodeContext.boundaryTrace (Party := Party) (Δ := Δ)
          (rest x) (semantics.2 x) path :=
  UC.OpenNodeContext.boundaryTrace_node rest semantics x path

/-! ## Scheduled open processes -/

example {m : Type w → Type w'} {Party : Type u} {Δ : UC.PortBoundary}
    (mass : ℕ+) (process : UC.OpenProcess.{u, v, w, w'} m Party Δ) :
    (UC.ScheduledOpenProcess.withMass mass process).mass = mass := by
  simp

example {m : Type w → Type w'} {Party : Type u} {Δ : UC.PortBoundary}
    (process : UC.OpenProcess.{u, v, w, w'} m Party Δ) :
    (UC.ScheduledOpenProcess.atom process).process = process := by
  simp

example {m : Type w → Type w'} {Party : Type u}
    {Δ₁ Δ₂ : UC.PortBoundary} (phi : UC.PortBoundary.Hom Δ₁ Δ₂)
    (process : UC.ScheduledOpenProcess.{u, v, w, w'} m Party Δ₁) :
    (process.mapBoundary phi).mass = process.mass := by
  simp

example {m : Type w → Type w'} {Party : Type u}
    (scheduler : UC.BinaryScheduler m) (Δ : UC.PortBoundary) :
    (UC.scheduledOpenTheory.{u, v, w, w'} Party m scheduler).Obj Δ =
      UC.ScheduledOpenProcess.{u, v, w, w'} m Party Δ := by
  rfl

example {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (scheduler : UC.BinaryScheduler m) (first second context : ℕ+)
    {α : Type w} (continuation :
      ULift.{w, 0} UC.OpenProcessFactorization.Leaf → m α) :
    UC.BinaryScheduler.sourceDraw scheduler first second context >>= continuation =
      scheduler (first + second) context >>= fun outer ↦
        if outer.down then
          scheduler first second >>= fun inner ↦
            if inner.down then continuation ⟨.first⟩ else continuation ⟨.second⟩
        else
          continuation ⟨.context⟩ :=
  UC.BinaryScheduler.sourceDraw_bind scheduler first second context continuation

/-! ## Routed interleaving and re-decoration -/

example {m : Type → Type} {Party : Type} {Δ₁ Δ₂ Δ : UC.PortBoundary}
    (p₁ : UC.OpenProcess m Party Δ₁) (p₂ : UC.OpenProcess m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom (UC.OpenNodeContext Party Δ₁) (UC.OpenNodeContext Party Δ))
    (f₂ : TypeTree.Node.ContextHom (UC.OpenNodeContext Party Δ₂) (UC.OpenNodeContext Party Δ))
    (c : UC.OpenNodeContext Party Δ (ULift Bool)) (σ : m (ULift Bool)) :
    p₁.interleave p₂ f₁ f₂ c σ =
      p₁.interleaveRouted p₂ f₁ f₂ c σ (fun _ _ s => s) (fun _ _ s => s) :=
  UC.OpenProcess.interleave_eq_interleaveRouted p₁ p₂ f₁ f₂ c σ

example {m : Type → Type} {Party : Type} {Δ₁ Δ₂ : UC.PortBoundary}
    (φ : UC.PortBoundary.Hom Δ₁ Δ₂) (op : UC.OpenProcess m Party Δ₁) :
    op.mapBoundary φ = op.mapHom (UC.OpenNodeContext.map Party φ) :=
  UC.OpenProcess.mapBoundary_eq_mapHom φ op

example {m : Type → Type} {Party : Type} {Δ₁ Δ₂ : UC.PortBoundary}
    (φ : UC.PortBoundary.Hom Δ₁ Δ₂) (op : UC.OpenProcess m Party Δ₁) (s : op.Proc)
    (tr : (op.step s).tree.Path) :
    UC.IsSilentStep (op.mapHom (UC.OpenNodeContext.map Party φ)) s tr ↔
      UC.IsSilentStep op s tr :=
  UC.OpenProcess.isSilentStep_mapHom_iff (UC.OpenNodeContext.preservesActivation_map φ) op s tr

/-! ## Coherence of interleaving -/

example {m : Type → Type} {Party : Type} {Δ₁ Δ₂ Δ : UC.PortBoundary}
    (p₁ : UC.OpenProcess m Party Δ₁) (p₂ : UC.OpenProcess m Party Δ₂)
    {f₁ : TypeTree.Node.ContextHom (UC.OpenNodeContext Party Δ₁) (UC.OpenNodeContext Party Δ)}
    {f₂ : TypeTree.Node.ContextHom (UC.OpenNodeContext Party Δ₂) (UC.OpenNodeContext Party Δ)}
    {c : UC.OpenNodeContext Party Δ (ULift Bool)} (σ : m (ULift Bool))
    {g₁ : TypeTree.Node.ContextHom (UC.OpenNodeContext Party Δ₂) (UC.OpenNodeContext Party Δ)}
    {g₂ : TypeTree.Node.ContextHom (UC.OpenNodeContext Party Δ₁) (UC.OpenNodeContext Party Δ)}
    {d : UC.OpenNodeContext Party Δ (ULift Bool)} (τ : m (ULift Bool))
    (hf₁ : UC.OpenNodeContext.PreservesActivation f₁)
    (hf₂ : UC.OpenNodeContext.PreservesActivation f₂)
    (hg₁ : UC.OpenNodeContext.PreservesActivation g₁)
    (hg₂ : UC.OpenNodeContext.PreservesActivation g₂)
    (hc : c.boundary.isActivated = false) (hd : d.boundary.isActivated = false) :
    UC.OpenProcessActivationEquiv (p₁.interleave p₂ f₁ f₂ c σ) (p₂.interleave p₁ g₁ g₂ d τ) :=
  UC.interleave_comm_activationEquiv p₁ p₂ σ τ hf₁ hf₂ hg₁ hg₂ hc hd

/-! ## Traced laws of the process model -/

example {m : Type → Type} {Party : Type} (σ : m (ULift Bool)) {Δ₁ Γ₁ Γ₂ Δ₃ : UC.PortBoundary}
    (W₁ : UC.OpenProcess m Party (UC.PortBoundary.tensor Δ₁ Γ₁))
    (W₂ : UC.OpenProcess m Party
      (UC.PortBoundary.tensor (UC.PortBoundary.swap Γ₁) Γ₂))
    (W₃ : UC.OpenProcess m Party
      (UC.PortBoundary.tensor (UC.PortBoundary.swap Γ₂) Δ₃)) :
    UC.OpenProcessActivationEquiv
      ((UC.openTheory Party m σ).wire ((UC.openTheory Party m σ).wire W₁ W₂) W₃)
      ((UC.openTheory Party m σ).wire W₁ ((UC.openTheory Party m σ).wire W₂ W₃)) :=
  UC.openTheory_wire_assoc_activation_equiv Party m σ W₁ W₂ W₃

example {m : Type → Type} {Party : Type} (σ : m (ULift Bool)) {Δ₁ Δ₂ Γ Δ₃ : UC.PortBoundary}
    (W₁ : UC.OpenProcess m Party Δ₁)
    (W₂ : UC.OpenProcess m Party (UC.PortBoundary.tensor Δ₂ Γ))
    (W₃ : UC.OpenProcess m Party
      (UC.PortBoundary.tensor (UC.PortBoundary.swap Γ) Δ₃)) :
    UC.OpenProcessActivationEquiv
      ((UC.openTheory Party m σ).wire
        (UC.OpenProcess.mapBoundary (UC.PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Γ).symm.toHom
          ((UC.openTheory Party m σ).par W₁ W₂))
        W₃)
      (UC.OpenProcess.mapBoundary (UC.PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom
        ((UC.openTheory Party m σ).par W₁ ((UC.openTheory Party m σ).wire W₂ W₃))) :=
  UC.openTheory_wire_par_superpose_activation_equiv Party m σ W₁ W₂ W₃

/-! ## Sampler-level coherence -/

example {m : Type → Type} [Monad m] [LawfulMonad m] (σOut σIn : m (ULift Bool)) {α : Type}
    (h : ULift UC.OpenProcessFactorization.Leaf → m α) :
    UC.nestedDrawLeft σOut σIn >>= h =
      σOut >>= fun
        | ⟨true⟩ => σIn >>= fun
          | ⟨true⟩ => h ⟨.first⟩
          | ⟨false⟩ => h ⟨.second⟩
        | ⟨false⟩ => h ⟨.context⟩ :=
  UC.nestedDrawLeft_bind σOut σIn h

example {m : Type → Type} [Monad m] (R : UC.MonadRelFamily m) [R.IsBindCongr] {α β : Type}
    (x : m α) {f g : α → m β} (h : ∀ a, R.rel (f a) (g a)) :
    R.rel (x >>= f) (x >>= g) :=
  R.bind_congr_right x h

example {m : Type → Type} [Monad m] [LawfulMonad m] {Party : Type} {Δ₁ Δ₂ Δ : UC.PortBoundary}
    (R : UC.MonadRelFamily m)
    (p₁ : UC.OpenProcess m Party Δ₁) (p₂ : UC.OpenProcess m Party Δ₂)
    {f₁ : TypeTree.Node.ContextHom (UC.OpenNodeContext Party Δ₁) (UC.OpenNodeContext Party Δ)}
    {f₂ : TypeTree.Node.ContextHom (UC.OpenNodeContext Party Δ₂) (UC.OpenNodeContext Party Δ)}
    {c : UC.OpenNodeContext Party Δ (ULift Bool)} (σ : m (ULift Bool))
    {d : UC.OpenNodeContext Party Δ (ULift Bool)} (τ : m (ULift Bool))
    (hc : UC.OpenNodeContext.IsInternalNode c) (hd : UC.OpenNodeContext.IsInternalNode d)
    (hστ : R.rel (UC.schedulerFlip <$> σ) τ) :
    UC.OpenProcessSamplerEquiv R (p₁.interleave p₂ f₁ f₂ c σ) (p₂.interleave p₁ f₂ f₁ d τ) :=
  UC.interleave_comm_samplerEquiv R p₁ p₂ σ τ hc hd hστ

example {m : Type → Type} [Monad m] [LawfulMonad m] {Party : Type}
    (scheduler : UC.BinaryScheduler m) (R : UC.MonadRelFamily m)
    (coherent : scheduler.IsCoherent R) :
    (UC.Observation.scheduledSampler Party m scheduler R).RespectsFactorization :=
  UC.Observation.respectsFactorization_scheduledSampler Party m scheduler R coherent

example {m : Type → Type} [Monad m] [LawfulMonad m] {Party : Type} (σ : m (ULift Bool))
    (R : UC.MonadRelFamily m) (hfair : R.rel σ (UC.schedulerFlip <$> σ))
    {Δ₁ Γ Δ₂ : UC.PortBoundary}
    (W₁ : UC.OpenProcess m Party (UC.PortBoundary.tensor Δ₁ Γ))
    (W₂ : UC.OpenProcess m Party (UC.PortBoundary.tensor (UC.PortBoundary.swap Γ) Δ₂)) :
    UC.OpenProcessSamplerEquiv R
      ((UC.openTheory Party m σ).wire W₁ W₂)
      (UC.OpenProcess.mapBoundary (UC.PortBoundary.Equiv.tensorComm Δ₂ Δ₁).toHom
        ((UC.openTheory Party m σ).wire
          (UC.OpenProcess.mapBoundary
            (UC.PortBoundary.Equiv.tensorComm (UC.PortBoundary.swap Γ) Δ₂).toHom W₂)
          (UC.OpenProcess.mapBoundary (UC.PortBoundary.Equiv.tensorComm Δ₁ Γ).toHom W₁))) :=
  UC.openTheory_wire_comm_sampler_equiv Party m σ R hfair W₁ W₂

/-! ## Plug factorization laws -/

example {T : UC.OpenTheory} [UC.OpenTheory.HasPlugFactorization T]
    {Δ₁ Δ₂ : UC.PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
    (K : T.Plug (UC.PortBoundary.tensor Δ₁ Δ₂)) :
    T.close (T.par W₁ W₂) K = T.close W₁ (T.parContextLeft W₂ K) :=
  UC.OpenTheory.close_par_left W₁ W₂ K

example {T : UC.OpenTheory} [UC.OpenTheory.HasPlugFactorization T]
    {Δ : UC.PortBoundary} (W : T.Obj Δ) (K : T.Obj (UC.PortBoundary.swap Δ)) :
    T.plug W K = T.plug K W :=
  UC.OpenTheory.plug_comm W K

/-! ## Quotient theories -/

example {T : UC.OpenTheory} (E : UC.OpenTheory.Congruence T) {Δ : UC.PortBoundary}
    {W W' : T.Obj Δ} : E.cls W = E.cls W' ↔ E.rel W W' :=
  E.cls_eq_cls

example {T : UC.OpenTheory} (E : UC.OpenTheory.Congruence T)
    [UC.OpenTheory.HasPlugFactorizationMod E] :
    UC.OpenTheory.HasPlugFactorization (T.quotient E) :=
  inferInstance

example {T : UC.OpenTheory} (E : UC.OpenTheory.Congruence T) {Δ : UC.PortBoundary}
    {real ideal : T.Obj Δ} {Obs : UC.Observation (T.quotient E)} :
    UC.Emulates (E.cls real) (E.cls ideal) Obs ↔ UC.Emulates real ideal (Obs.comap E) :=
  UC.Emulates.quotient_iff E

/-! ## Quotients of the process model -/

example {m : Type → Type} {Party : Type} (σ : m (ULift Bool)) :
    UC.OpenTheory.HasPlugWireFactor
      ((UC.openTheory Party m σ).quotient (UC.openTheory.activationCongruence Party m σ)) :=
  inferInstance

example {m : Type → Type} {Party : Type} (σ : m (ULift Bool))
    (c₁ c₂ : (UC.openTheory Party m σ).Closed) :
    (UC.Observation.activation Party m σ).rel c₁ c₂ ↔
      ((UC.Observation.eq _).comap (UC.openTheory.activationCongruence Party m σ)).rel c₁ c₂ :=
  UC.Observation.activation_rel_iff_comap Party m σ

example {m : Type → Type} [Monad m] [LawfulMonad m] {Party : Type}
    (scheduler : UC.BinaryScheduler m) (R : UC.MonadRelFamily m) [R.IsBindCongr]
    (coherent : scheduler.IsCoherent R) :
    UC.OpenTheory.HasPlugFactorization
      ((UC.scheduledOpenTheory Party m scheduler).quotient
        (UC.scheduledOpenTheory.samplerCongruence Party m scheduler R)) :=
  UC.scheduledOpenTheory.hasPlugFactorization_quotient_samplerCongruence Party m scheduler R
    coherent

end PolyFunTest.ModuleAPI.Interaction
