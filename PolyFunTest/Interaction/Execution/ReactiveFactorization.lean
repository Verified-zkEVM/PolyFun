/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveNetwork.Factorization
public import PolyFunTest.Interaction.Execution.ReactiveAssembly

/-!
# Execution through reactive factorization

An environment communicates with two distinct echo components. Moving a component into its
context preserves all finite execution prefixes by the general graph transport theorem.
A separate counterexample checks that renaming a graph without its schedule changes execution.
-/

public section

namespace Interaction.Execution.ReactiveNetwork.FactorizationTests

open PFunctor ReactiveProcess DynSystem
open AssemblyTests (boundary echo)

@[expose] def context : Assembly (PortBoundary.swap (PortBoundary.tensor boundary boundary)) Bool :=
  Assembly.atom (DynComputation.ofFreeM fun _ =>
    (FreeM.liftBind (.send ⟨.inl (), false⟩) fun _ =>
      .liftBind .receive fun
      | ⟨.inr _, _⟩ => .pure .aborted
      | ⟨.inl _, first⟩ => .liftBind (.send ⟨.inr (), true⟩) fun _ =>
        .liftBind .receive fun
        | ⟨.inl _, _⟩ => .pure .aborted
        | ⟨.inr _, second⟩ => .pure (.returned (!first && second)) :
        FreeM (signature Assembly.relayEffect
          (PortBoundary.swap (PortBoundary.tensor boundary boundary))) (Outcome Bool)))

@[expose] def whole := ((echo.diagram.par echo.diagram).plug context.diagram).withEnvironment
  (.inr ())

@[expose] def factored :=
  (echo.diagram.plug (echo.diagram.parContextLeft context.diagram)).withEnvironment (.inr (.inl ()))

@[expose] def impl : (node : (Unit ⊕ Unit) ⊕ Unit) →
    Handler (StateT Unit Id) (whole.effect node) := by
  intro node
  rcases node with node | node
  · rcases node with node | node <;> exact fun operation => operation.elim
  · exact fun operation => operation.elim

/-- The graph equality retains the context's actual identity. -/
theorem factorization : whole.reindex (Diagram.parContextLeftEquiv Unit Unit Unit) = factored :=
  Network.close_par_left echo.diagram echo.diagram context.diagram ()

/-- Every complete residual token state transports through the proved graph factorization. -/
example (fuel : ℕ) (state : State whole Unit) :
    runToken (castHandlers factorization
        (fun node => impl (Diagram.parContextLeftEquiv Unit Unit Unit node))) fuel
        ((state.reindex (Diagram.parContextLeftEquiv Unit Unit Unit)).castNetwork factorization) =
      (fun next => (next.reindex (Diagram.parContextLeftEquiv Unit Unit Unit)).castNetwork
        factorization) <$> runToken impl fuel state :=
  runToken_reindex_cast impl _ factorization fuel state

/-- Every FIFO schedule transports, retaining its delivery positions and residual queues. -/
example (schedule : List (Activation ((Unit ⊕ Unit) ⊕ Unit))) (state : State whole Unit) :
    runFIFO (castHandlers factorization
        (fun node => impl (Diagram.parContextLeftEquiv Unit Unit Unit node)))
        (schedule.map (Activation.reindex (Diagram.parContextLeftEquiv Unit Unit Unit)))
        ((state.reindex (Diagram.parContextLeftEquiv Unit Unit Unit)).castNetwork factorization) =
      (fun next => (next.reindex (Diagram.parContextLeftEquiv Unit Unit Unit)).castNetwork
        factorization) <$> runFIFO impl schedule state :=
  runFIFO_reindex_cast impl _ factorization schedule state

/-- The test really exchanges different messages with both components. -/
example : outcome (.inr ()) (runToken (m := Id) impl 8 (initial whole ())) =
    some (.returned true) := rfl

/-- The environment is still waiting one activation before completion. -/
example : outcome (.inr ()) (runToken (m := Id) impl 7 (initial whole ())) = none := rfl

end Interaction.Execution.ReactiveNetwork.FactorizationTests
