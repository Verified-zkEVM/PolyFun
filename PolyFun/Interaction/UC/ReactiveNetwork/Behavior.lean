/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ReactiveNetwork

/-!
# Exact behavior adequacy for reactive execution

Mapping each private component state to its cofree behavior commutes with actual network
execution under either discipline. This hides state representation while retaining packets,
effect operations and their responses, control, queues, and fuel. The result is an equality
in an arbitrary lawful effect monad: no probability or scheduler-invariance assumption is
hidden in the passage to behavior.
-/

public section

namespace Interaction.UC.ReactiveNetwork

open PFunctor ReactiveProcess DynSystem

variable {Node result S : Type} {boundary : PortBoundary}

/-- Present each component by its exact resumption while retaining the same routing diagram. -/
@[expose] def Network.behavior (network : Network Node boundary result) :
    Network Node boundary result :=
  { network with component := fun id => DynComputation.ofResumption (network.component id).denote }

/-- Hide component state representation through the final-coalgebra behavior map. -/
@[expose] def State.behavior {network : Network Node boundary result} (state : State network S) :
    State network.behavior S :=
  { state with
    localState := fun id => (network.component id).toDynSystem.behavior (state.localState id) }

attribute [local implicit_reducible] signature Response Network.behavior State.behavior
  DynComputation.ofResumption

variable {network : Network Node boundary result} [DecidableEq Node]

private theorem behavior_update (state : State network S) (id : Node)
    (next : (network.component id).State) :
    (fun id' => (network.component id').toDynSystem.behavior
      (Function.update state.localState id next id')) =
      Function.update (fun id' => (network.component id').toDynSystem.behavior
        (state.localState id')) id ((network.component id).toDynSystem.behavior next) := by
  funext id'
  exact Function.apply_update (fun id => (network.component id).toDynSystem.behavior)
    state.localState id next id'

/-- Delivering a packet does not depend on the private representation of its receiver. -/
theorem dispatch_behavior (packet : Destination network) (state : State network S) :
    dispatch (network := network.behavior) packet state.behavior =
      (dispatch packet state).behavior := by
  cases packet <;> rfl

/-- Pending delivery and elapsed time are retained by the behavior map. -/
theorem deliver_behavior (state : State network S) :
    deliver state.behavior = (deliver state).behavior := by
  cases h : state.pending with
  | nil => simp [deliver, State.behavior, h]
  | cons packet rest =>
      cases packet <;> simp [deliver, State.behavior, Network.behavior, h, dispatch]

omit [DecidableEq Node] in
private theorem view_behavior_query (id : Node) (state : State network S)
    (action : Action (network.effect id) (network.ports id))
    (next : Response action → (network.component id).State)
    (h : (network.component id).view (state.localState id) = .inr ⟨action, next⟩) :
    (network.behavior.component id).view (state.behavior.localState id) =
      .inr ⟨action, fun answer => (network.component id).toDynSystem.behavior (next answer)⟩ := by
  change (DynComputation.ofResumption _).view _ = _
  simp only [DynComputation.view_ofResumption, State.behavior]
  rw [DynComputation.dest_behavior_view, h]
  rfl

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Cofree behavior is adequate for one real reactive activation, including its effect. -/
theorem activate_behavior
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (discipline : Discipline) (id : Node) (state : State network S) :
    activate (network := network.behavior) impl discipline id state.behavior =
      State.behavior <$> activate impl discipline id state := by
  cases h : (network.component id).view (state.localState id) with
  | inl value => simp [activate, Network.behavior, State.behavior, h]
  | inr action =>
      rcases action with ⟨action, next⟩
      have hb := view_behavior_query id state action next h
      cases action with
      | effect operation =>
          simp only [activate, hb, h]
          simp [Network.behavior, State.behavior, behavior_update]
      | receive =>
          simp only [activate, hb, h]
          cases hin : state.inbox id <;>
            simp [Network.behavior, State.behavior, hin, behavior_update]
      | send packet =>
          simp only [activate, hb, h]
          cases discipline <;> cases hr : network.route id packet <;>
            simp [Network.behavior, State.behavior, hr, dispatch, behavior_update]
      | tick =>
          simp only [activate, hb, h]
          simp [State.behavior, behavior_update]
      | yield =>
          simp only [activate, hb, h]
          simp [Network.behavior, State.behavior, behavior_update]

omit [DecidableEq Node] in
/-- The behavior map preserves the chosen initialization. -/
theorem initial_behavior (service : S) :
    initial network.behavior service = (initial network service).behavior := rfl

omit [DecidableEq Node] in
/-- Reading a terminal result from execution commutes with the behavior map. -/
theorem outcome_behavior (id : Node) (state : State network S) :
    outcome id state.behavior = outcome id state := by
  cases h : (network.component id).view (state.localState id) <;>
    simp [outcome, Network.behavior, State.behavior, h]

/-- One FIFO operation is adequate at exact behavior. -/
theorem fifoStep_behavior
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (activation : Activation Node) (state : State network S) :
    fifoStep (network := network.behavior) impl activation state.behavior =
      State.behavior <$> fifoStep impl activation state := by
  cases activation with
  | deliver => simp [fifoStep, deliver_behavior]
  | node id => exact activate_behavior impl .fifo id state

/-- Every finite FIFO prefix has the same exact behavior and execution data. -/
theorem runFIFO_behavior
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (schedule : List (Activation Node)) (state : State network S) :
    runFIFO (network := network.behavior) impl schedule state.behavior =
      State.behavior <$> runFIFO impl schedule state := by
  induction schedule generalizing state with
  | nil => simp [runFIFO]
  | cons activation rest ih =>
      simp only [runFIFO, fifoStep_behavior, bind_map_left, map_bind]
      exact bind_congr fun next => ih next

/-- Every finite token prefix has the same exact behavior and execution data. -/
theorem runToken_behavior
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (fuel : ℕ) (state : State network S) :
    runToken (network := network.behavior) impl fuel state.behavior =
      State.behavior <$> runToken impl fuel state := by
  induction fuel generalizing state with
  | zero => simp [runToken]
  | succ fuel ih =>
      simp only [runToken, activate_behavior, bind_map_left, map_bind]
      exact bind_congr fun next => ih next

end Interaction.UC.ReactiveNetwork
