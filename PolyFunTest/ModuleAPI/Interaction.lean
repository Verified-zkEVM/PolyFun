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
import PolyFun.Interaction.UC.OpenTheory.PlugFactorization
import PolyFun.Interaction.UC.ScheduledOpenProcessModel
import PolyFun.Interaction.UC.ScheduledSamplerFactorization

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

end PolyFunTest.ModuleAPI.Interaction
