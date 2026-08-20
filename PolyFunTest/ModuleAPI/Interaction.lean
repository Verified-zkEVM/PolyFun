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

/-!
# Ordinary-import canaries for the interaction API

These examples exercise public computation and characterization laws through
ordinary imports. They mirror downstream uses that otherwise tend to reach for
`import all` after a module-system migration.
-/

@[expose] public section

universe u v w

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

end PolyFunTest.ModuleAPI.Interaction
