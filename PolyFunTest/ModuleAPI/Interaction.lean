/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.Interaction.Basic.Sampler
import PolyFun.Interaction.Concurrent.Fairness
import PolyFun.Interaction.Multiparty.Observation
import PolyFun.Interaction.Open.OpenProcess
import PolyFun.Interaction.Open.OpenProcessInterleave
import PolyFun.Interaction.Open.OpenProcessCoherence
import PolyFun.Interaction.Open.OpenTheory.PlugFactorization
import PolyFun.Interaction.Open.OpenTheory.Quotient
import PolyFun.Interaction.Open.OpenSyntax.AtomSubTheory
import PolyFun.Interaction.Open.EmulatesQuotient
import PolyFun.Interaction.Open.OpenProcessQuotient
import PolyFun.Interaction.Open.ScheduledOpenProcessModel
import PolyFun.Interaction.Open.ScheduledSamplerFactorization
import PolyFun.Interaction.Open.OpenProcessSamplerCoherence

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

example {Party : Type u} {Δ : PortBoundary} {P : Type v}
    (step : Open.OpenStep Party Δ P) (path : TypeTree.Path step.tree) :
    Open.OpenStep.boundaryTrace step path =
      Open.OpenNodeContext.boundaryTrace step.tree step.semantics path :=
  Open.OpenStep.boundaryTrace_eq step path

example {Party : Type u} {Δ : PortBoundary} {X : Type w}
    (rest : X → TypeTree.{w})
    (semantics : TypeTree.Decoration (Open.OpenNodeContext.{u, w} Party Δ)
      (TypeTree.node X rest))
    (x : X) (path : TypeTree.Path (rest x)) :
    Open.OpenNodeContext.boundaryTrace (Party := Party) (Δ := Δ)
        (TypeTree.node X rest) semantics ⟨x, path⟩ =
      semantics.1.boundary.emit x *
        Open.OpenNodeContext.boundaryTrace (Party := Party) (Δ := Δ)
          (rest x) (semantics.2 x) path :=
  Open.OpenNodeContext.boundaryTrace_node rest semantics x path

/-! ## Scheduled open processes -/

example {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}
    (mass : ℕ+) (process : Open.OpenProcess.{u, v, w, w'} m Party Δ) :
    (Open.ScheduledOpenProcess.withMass mass process).mass = mass := by
  simp

example {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}
    (process : Open.OpenProcess.{u, v, w, w'} m Party Δ) :
    (Open.ScheduledOpenProcess.atom process).process = process := by
  simp

example {m : Type w → Type w'} {Party : Type u}
    {Δ₁ Δ₂ : PortBoundary} (phi : PortBoundary.Hom Δ₁ Δ₂)
    (process : Open.ScheduledOpenProcess.{u, v, w, w'} m Party Δ₁) :
    (process.mapBoundary phi).mass = process.mass := by
  simp

example {m : Type w → Type w'} {Party : Type u}
    (scheduler : Open.BinaryScheduler m) (Δ : PortBoundary) :
    (Open.scheduledOpenTheory.{u, v, w, w'} Party m scheduler).Obj Δ =
      Open.ScheduledOpenProcess.{u, v, w, w'} m Party Δ := by
  rfl

example {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (scheduler : Open.BinaryScheduler m) (first second context : ℕ+)
    {α : Type w} (continuation :
      ULift.{w, 0} Open.OpenProcessFactorization.Leaf → m α) :
    Open.BinaryScheduler.sourceDraw scheduler first second context >>= continuation =
      scheduler (first + second) context >>= fun outer ↦
        if outer.down then
          scheduler first second >>= fun inner ↦
            if inner.down then continuation ⟨.first⟩ else continuation ⟨.second⟩
        else
          continuation ⟨.context⟩ :=
  Open.BinaryScheduler.sourceDraw_bind scheduler first second context continuation

/-! ## Routed interleaving and re-decoration -/

example {m : Type → Type} {Party : Type} {Δ₁ Δ₂ Δ : PortBoundary}
    (p₁ : Open.OpenProcess m Party Δ₁) (p₂ : Open.OpenProcess m Party Δ₂)
    (f₁ : TypeTree.Node.ContextHom (Open.OpenNodeContext Party Δ₁) (Open.OpenNodeContext Party Δ))
    (f₂ : TypeTree.Node.ContextHom (Open.OpenNodeContext Party Δ₂) (Open.OpenNodeContext Party Δ))
    (c : Open.OpenNodeContext Party Δ (ULift Bool)) (σ : m (ULift Bool)) :
    p₁.interleave p₂ f₁ f₂ c σ =
      p₁.interleaveRouted p₂ f₁ f₂ c σ (fun _ _ s => s) (fun _ _ s => s) :=
  Open.OpenProcess.interleave_eq_interleaveRouted p₁ p₂ f₁ f₂ c σ

example {m : Type → Type} {Party : Type} {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂) (op : Open.OpenProcess m Party Δ₁) :
    op.mapBoundary φ = op.mapHom (Open.OpenNodeContext.map Party φ) :=
  Open.OpenProcess.mapBoundary_eq_mapHom φ op

example {m : Type → Type} {Party : Type} {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂) (op : Open.OpenProcess m Party Δ₁) (s : op.Proc)
    (tr : (op.step s).tree.Path) :
    Open.IsSilentStep (op.mapHom (Open.OpenNodeContext.map Party φ)) s tr ↔
      Open.IsSilentStep op s tr :=
  Open.OpenProcess.isSilentStep_mapHom_iff (Open.OpenNodeContext.preservesActivation_map φ) op s tr

/-! ## Coherence of interleaving -/

example {m : Type → Type} {Party : Type} {Δ₁ Δ₂ Δ : PortBoundary}
    (p₁ : Open.OpenProcess m Party Δ₁) (p₂ : Open.OpenProcess m Party Δ₂)
    {f₁ : TypeTree.Node.ContextHom (Open.OpenNodeContext Party Δ₁) (Open.OpenNodeContext Party Δ)}
    {f₂ : TypeTree.Node.ContextHom (Open.OpenNodeContext Party Δ₂) (Open.OpenNodeContext Party Δ)}
    {c : Open.OpenNodeContext Party Δ (ULift Bool)} (σ : m (ULift Bool))
    {g₁ : TypeTree.Node.ContextHom (Open.OpenNodeContext Party Δ₂) (Open.OpenNodeContext Party Δ)}
    {g₂ : TypeTree.Node.ContextHom (Open.OpenNodeContext Party Δ₁) (Open.OpenNodeContext Party Δ)}
    {d : Open.OpenNodeContext Party Δ (ULift Bool)} (τ : m (ULift Bool))
    (hf₁ : Open.OpenNodeContext.PreservesActivation f₁)
    (hf₂ : Open.OpenNodeContext.PreservesActivation f₂)
    (hg₁ : Open.OpenNodeContext.PreservesActivation g₁)
    (hg₂ : Open.OpenNodeContext.PreservesActivation g₂)
    (hc : c.boundary.isActivated = false) (hd : d.boundary.isActivated = false) :
    Open.OpenProcessActivationEquiv (p₁.interleave p₂ f₁ f₂ c σ) (p₂.interleave p₁ g₁ g₂ d τ) :=
  Open.interleave_comm_activationEquiv p₁ p₂ σ τ hf₁ hf₂ hg₁ hg₂ hc hd

/-! ## Traced laws of the process model -/

example {m : Type → Type} {Party : Type} (σ : m (ULift Bool)) {Δ₁ Γ₁ Γ₂ Δ₃ : PortBoundary}
    (W₁ : Open.OpenProcess m Party (PortBoundary.tensor Δ₁ Γ₁))
    (W₂ : Open.OpenProcess m Party
      (PortBoundary.tensor (PortBoundary.swap Γ₁) Γ₂))
    (W₃ : Open.OpenProcess m Party
      (PortBoundary.tensor (PortBoundary.swap Γ₂) Δ₃)) :
    Open.OpenProcessActivationEquiv
      ((Open.openTheory Party m σ).wire ((Open.openTheory Party m σ).wire W₁ W₂) W₃)
      ((Open.openTheory Party m σ).wire W₁ ((Open.openTheory Party m σ).wire W₂ W₃)) :=
  Open.openTheory_wire_assoc_activation_equiv Party m σ W₁ W₂ W₃

example {m : Type → Type} {Party : Type} (σ : m (ULift Bool)) {Δ₁ Δ₂ Γ Δ₃ : PortBoundary}
    (W₁ : Open.OpenProcess m Party Δ₁)
    (W₂ : Open.OpenProcess m Party (PortBoundary.tensor Δ₂ Γ))
    (W₃ : Open.OpenProcess m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₃)) :
    Open.OpenProcessActivationEquiv
      ((Open.openTheory Party m σ).wire
        (Open.OpenProcess.mapBoundary (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Γ).symm.toHom
          ((Open.openTheory Party m σ).par W₁ W₂))
        W₃)
      (Open.OpenProcess.mapBoundary (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom
        ((Open.openTheory Party m σ).par W₁ ((Open.openTheory Party m σ).wire W₂ W₃))) :=
  Open.openTheory_wire_par_superpose_activation_equiv Party m σ W₁ W₂ W₃

/-! ## Sampler-level coherence -/

example {m : Type → Type} [Monad m] [LawfulMonad m] (σOut σIn : m (ULift Bool)) {α : Type}
    (h : ULift Open.OpenProcessFactorization.Leaf → m α) :
    Open.nestedDrawLeft σOut σIn >>= h =
      σOut >>= fun
        | ⟨true⟩ => σIn >>= fun
          | ⟨true⟩ => h ⟨.first⟩
          | ⟨false⟩ => h ⟨.second⟩
        | ⟨false⟩ => h ⟨.context⟩ :=
  Open.nestedDrawLeft_bind σOut σIn h

example {m : Type → Type} [Monad m] (R : Open.MonadRelFamily m) [R.IsBindCongr] {α β : Type}
    (x : m α) {f g : α → m β} (h : ∀ a, R.rel (f a) (g a)) :
    R.rel (x >>= f) (x >>= g) :=
  R.bind_congr_right x h

example {m : Type → Type} [Monad m] [LawfulMonad m] {Party : Type} {Δ₁ Δ₂ Δ : PortBoundary}
    (R : Open.MonadRelFamily m)
    (p₁ : Open.OpenProcess m Party Δ₁) (p₂ : Open.OpenProcess m Party Δ₂)
    {f₁ : TypeTree.Node.ContextHom (Open.OpenNodeContext Party Δ₁) (Open.OpenNodeContext Party Δ)}
    {f₂ : TypeTree.Node.ContextHom (Open.OpenNodeContext Party Δ₂) (Open.OpenNodeContext Party Δ)}
    {c : Open.OpenNodeContext Party Δ (ULift Bool)} (σ : m (ULift Bool))
    {d : Open.OpenNodeContext Party Δ (ULift Bool)} (τ : m (ULift Bool))
    (hc : Open.OpenNodeContext.IsInternalNode c) (hd : Open.OpenNodeContext.IsInternalNode d)
    (hστ : R.rel (Open.schedulerFlip <$> σ) τ) :
    Open.OpenProcessSamplerEquiv R (p₁.interleave p₂ f₁ f₂ c σ) (p₂.interleave p₁ f₂ f₁ d τ) :=
  Open.interleave_comm_samplerEquiv R p₁ p₂ σ τ hc hd hστ

example {m : Type → Type} [Monad m] [LawfulMonad m] {Party : Type}
    (scheduler : Open.BinaryScheduler m) (R : Open.MonadRelFamily m)
    (coherent : scheduler.IsCoherent R) :
    (Open.Observation.scheduledSampler Party m scheduler R).RespectsFactorization :=
  Open.Observation.respectsFactorization_scheduledSampler Party m scheduler R coherent

example {m : Type → Type} [Monad m] [LawfulMonad m] {Party : Type} (σ : m (ULift Bool))
    (R : Open.MonadRelFamily m) (hfair : R.rel σ (Open.schedulerFlip <$> σ))
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : Open.OpenProcess m Party (PortBoundary.tensor Δ₁ Γ))
    (W₂ : Open.OpenProcess m Party (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    Open.OpenProcessSamplerEquiv R
      ((Open.openTheory Party m σ).wire W₁ W₂)
      (Open.OpenProcess.mapBoundary (PortBoundary.Equiv.tensorComm Δ₂ Δ₁).toHom
        ((Open.openTheory Party m σ).wire
          (Open.OpenProcess.mapBoundary
            (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom W₂)
          (Open.OpenProcess.mapBoundary (PortBoundary.Equiv.tensorComm Δ₁ Γ).toHom W₁))) :=
  Open.openTheory_wire_comm_sampler_equiv Party m σ R hfair W₁ W₂

/-! ## Plug factorization laws -/

example {T : Open.OpenTheory} [Open.OpenTheory.HasPlugFactorization T]
    {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.close (T.par W₁ W₂) K = T.close W₁ (T.parContextLeft W₂ K) :=
  Open.OpenTheory.close_par_left W₁ W₂ K

example {T : Open.OpenTheory} [Open.OpenTheory.HasPlugFactorization T]
    {Δ : PortBoundary} (W : T.Obj Δ) (K : T.Obj (PortBoundary.swap Δ)) :
    T.plug W K = T.plug K W :=
  Open.OpenTheory.plug_comm W K

/-! ## Quotient theories -/

example {T : Open.OpenTheory} (E : Open.OpenTheory.Congruence T) {Δ : PortBoundary}
    {W W' : T.Obj Δ} : E.cls W = E.cls W' ↔ E.rel W W' :=
  E.cls_eq_cls

example {T : Open.OpenTheory} (E : Open.OpenTheory.Congruence T)
    [Open.OpenTheory.HasPlugFactorizationMod E] :
    Open.OpenTheory.HasPlugFactorization (T.quotient E) :=
  inferInstance

example {T : Open.OpenTheory} (E : Open.OpenTheory.Congruence T) {Δ : PortBoundary}
    {real ideal : T.Obj Δ} {Obs : Open.Observation (T.quotient E)} :
    Open.Emulates (E.cls real) (E.cls ideal) Obs ↔ Open.Emulates real ideal (Obs.comap E) :=
  Open.Emulates.quotient_iff E

/-! ## Free-syntax facade -/

example {Atom : PortBoundary → Type u} {Δ₁ Δ₂ : PortBoundary}
    (f : PortBoundary.Hom Δ₁ Δ₂) (e : (Open.OpenSyntax.Expr.theory Atom).Obj Δ₁)
    (T : Open.OpenTheory.{v}) [Open.OpenTheory.HasPlugWireFactor T]
    (interp : ∀ {Δ}, Atom Δ → T.Obj Δ) :
    ((Open.OpenSyntax.Expr.theory Atom).map f e).interpret T interp =
      T.map f (e.interpret T interp) := by
  rw [Open.OpenSyntax.Expr.interpret_map]

example (Atom : PortBoundary → Type u) :
    Open.OpenTheory.HasUnit.unit (T := Open.OpenSyntax.Expr.theory Atom) =
      Open.OpenSyntax.Expr.unit := rfl

example (Atom : PortBoundary → Type u) :
    Open.OpenTheory.HasPlugWireFactor (Open.OpenSyntax.Expr.theory Atom) :=
  Open.OpenSyntax.Expr.hasPlugWireFactor Atom

/-- Structural allowedness uses the same unit and identity-wire data as the
full law instance supplied to interpretation. -/
example (Atom : PortBoundary → Type u) (allowed : ∀ {Δ}, Atom Δ → Prop)
    {Δ : PortBoundary} {e : Open.OpenSyntax.Expr Atom Δ}
    (he : (Open.OpenSyntax.atomSubTheory Atom allowed).mem e) :
    (Open.OpenSyntax.atomSubTheory Atom allowed).mem
      (e.interpret (Open.OpenSyntax.Expr.theory Atom) Open.OpenSyntax.Expr.atom) :=
  Open.OpenSyntax.mem_interpret_of_atoms Atom allowed
    (Open.OpenSyntax.atomSubTheory Atom allowed) Open.OpenSyntax.Expr.atom
    (fun _ ha => Open.OpenSyntax.atomSubTheory.mem_atom Atom allowed ha) he

/-! ## Quotients of the process model -/

example {m : Type → Type} {Party : Type} (σ : m (ULift Bool)) :
    Open.OpenTheory.HasPlugWireFactor
      ((Open.openTheory Party m σ).quotient (Open.openTheory.activationCongruence Party m σ)) :=
  inferInstance

example {m : Type → Type} {Party : Type} (σ : m (ULift Bool))
    (c₁ c₂ : (Open.openTheory Party m σ).Closed) :
    (Open.Observation.activation Party m σ).rel c₁ c₂ ↔
      ((Open.Observation.eq _).comap (Open.openTheory.activationCongruence Party m σ)).rel c₁ c₂ :=
  Open.Observation.activation_rel_iff_comap Party m σ

example {m : Type → Type} [Monad m] [LawfulMonad m] {Party : Type}
    (scheduler : Open.BinaryScheduler m) (R : Open.MonadRelFamily m) [R.IsBindCongr]
    (coherent : scheduler.IsCoherent R) :
    Open.OpenTheory.HasPlugFactorization
      ((Open.scheduledOpenTheory Party m scheduler).quotient
        (Open.scheduledOpenTheory.samplerCongruence Party m scheduler R)) :=
  Open.scheduledOpenTheory.hasPlugFactorization_quotient_samplerCongruence Party m scheduler R
    coherent

end PolyFunTest.ModuleAPI.Interaction
