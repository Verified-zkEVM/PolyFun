/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.App.Machine
public import PolyFun.ITree.Resumption

/-! # The application as a resumption and a tau-free interaction tree

These are semantic views of the existing application machine, not alternative runtimes.
Each read, judgment, persistence, publication, or notification is an observable query.
A finite observation may stop while the meeting is still unfinished.
-/

public section

namespace Parliament.Walkthrough

open PFunctor PFunctor.DynSystem Parliament.App

/-- State-free behavior from any residual application state. -/
@[expose] def behavior (config : Configuration) (state : State config) :
    Resumption (Effects config) (Exit config) := (application config).toDynSystem.behavior state

/-- The initialized machine's denotation is its behavior at the ready phase. -/
theorem behavior_ready (config : Configuration) (journal : Journal wordDomain config.rules) :
    behavior config (.ready journal) = (application config).denote journal := rfl

/-- The resumption exposes precisely the query or return selected by the application step. -/
theorem behavior_view (config : Configuration) (state : State config) :
    Resumption.dest (behavior config state) =
      Sum.map (fun value => value) ((Effects config).map (behavior config))
        (machineStep config state) := by
  change Resumption.dest ((application config).toDynSystem.behavior state) =
    Sum.map (fun value => value)
      ((Effects config).map (application config).toDynSystem.behavior) (machineStep config state)
  simpa only [application, DynComputation.view_ofStep] using
    (application config).dest_behavior_view state

/-- A final application state returns without another handler interaction. -/
theorem behavior_done (config : Configuration) (result : Exit config) :
    Resumption.dest (behavior config (.done result)) = .inl result := by
  rw [behavior_view]
  rfl

/-- The existing resumption-to-ITree embedding supplies the application's tree semantics. -/
def behaviorTree (config : Configuration) (state : State config) :
    ITree (Effects config) (Exit config) := (behavior config state).toITree

/-- Embedding does not insert silent transitions between application effects. -/
theorem behaviorTree_tauFree (config : Configuration) (state : State config) :
    ITree.TauFree (behaviorTree config state) := Resumption.toITree_tauFree _

/-- Every application's visible query is preserved, with the same dependent response type. -/
theorem behaviorTree_query (config : Configuration) (state : State config)
    (effect : Effect config) (next : effect.Response → State config)
    (query : machineStep config state = .inr ⟨effect, next⟩) :
    ITree.shape' (behaviorTree config state) =
      .mk (.query effect) (fun answer => behaviorTree config (next answer)) := by
  simp only [behaviorTree, Resumption.shape'_toITree, behavior_view, query]
  rfl

/-- Forgetting a chunk's residual state gives exactly a finite observation of its behavior. -/
theorem chunk_observes_behavior (config : Configuration) (state : State config) (fuel : Nat) :
    FreeM.map DynComputation.Chunk.result ((application config).unrollChunk fuel state) =
      Resumption.truncate fuel (behavior config state) := by
  exact ((application config).unrollChunk_result fuel state).trans
    ((application config).unroll_eq_truncate fuel state)

end Parliament.Walkthrough
