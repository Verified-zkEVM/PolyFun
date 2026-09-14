/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ReactiveNetwork

/-!
# Relabeling typed reactive networks

A bijection changes the presentation of component identities, transporting the dependent
component interfaces, private states, packets, routing, token holder, and FIFO schedules
together. It does not alter effects or introduce new scheduler choices.
-/

public section

namespace Interaction.UC.ReactiveNetwork

open PFunctor ReactiveProcess

variable {Node Node' result S : Type} {boundary : PortBoundary}

/-- Transport the recipient of a dependent packet along a bijection of identities. -/
@[expose] def reindexDestination (network : Network Node boundary result) (e : Node' ≃ Node) :
    Destination network →
      ((id : Node') × Interface.Packet (network.ports (e id)).In) ⊕ Interface.Packet boundary.Out :=
  Sum.map (Equiv.sigmaCongrLeft e).symm id

/-- Present the same diagram on a different type of stable component identities. -/
@[expose] def Network.reindex (network : Network Node boundary result) (e : Node' ≃ Node) :
    Network Node' boundary result where
  effect id := network.effect (e id)
  ports id := network.ports (e id)
  component id := network.component (e id)
  route id packet := reindexDestination network e (network.route (e id) packet)
  ingress packet := (Equiv.sigmaCongrLeft e).symm (network.ingress packet)
  environment := e.symm network.environment

/-- The global environment follows the inverse bijection of component identities. -/
@[simp] theorem Network.reindex_environment (network : Network Node boundary result)
    (e : Node' ≃ Node) : (network.reindex e).environment = e.symm network.environment := rfl

/-- Relabel a complete residual configuration, retaining traffic order and consumed fuel. -/
@[expose] def State.reindex {network : Network Node boundary result} (e : Node' ≃ Node)
    (state : State network S) : State (network.reindex e) S where
  localState id := state.localState (e id)
  inbox id := state.inbox (e id)
  service := state.service
  pending := state.pending.map (reindexDestination network e)
  output := state.output
  focus := e.symm state.focus
  elapsed := state.elapsed

/-- Equality of network data transports a residual configuration without executing a step. -/
@[expose] def State.castNetwork {network network' : Network Node boundary result}
    (h : network = network') (state : State network S) : State network' S := h ▸ state

/-- Component handlers follow equality of the network's declared effect interfaces. -/
@[expose] def castHandlers {m : Type → Type} {network network' : Network Node boundary result}
    (h : network = network')
    (impl : (id : Node) → Handler (StateT S m) (network.effect id)) :
    (id : Node) → Handler (StateT S m) (network'.effect id) := h ▸ impl

/-- Transport along reflexive network equality leaves handlers unchanged. -/
@[simp] theorem castHandlers_rfl {m : Type → Type} {network : Network Node boundary result}
    (impl : (id : Node) → Handler (StateT S m) (network.effect id)) :
    castHandlers rfl impl = impl := rfl

/-- FIFO schedules retain their order and delivery positions under relabeling. -/
@[expose] def Activation.reindex (e : Node' ≃ Node) : Activation Node → Activation Node'
  | .node id => .node (e.symm id)
  | .deliver => .deliver

attribute [local implicit_reducible] signature Response Network.reindex State.reindex

/-- Reading a relabeled node recovers the same return, abort, or unfinished observation. -/
@[simp] theorem outcome_reindex {network : Network Node boundary result} (e : Node' ≃ Node)
    (id : Node') (state : State network S) :
    outcome id (state.reindex e) = outcome (e id) state := by
  simp only [outcome, State.reindex, Network.reindex]
  cases (network.component (e id)).view (state.localState (e id)) <;> rfl

/-- Changing an equal presentation preserves the node's actual observation. -/
@[simp] theorem outcome_castNetwork {network network' : Network Node boundary result}
    (h : network = network') (id : Node) (state : State network S) :
    outcome id (state.castNetwork h) = outcome id state := by
  cases h
  rfl

variable {network : Network Node boundary result} [DecidableEq Node] [DecidableEq Node']

omit [DecidableEq Node] [DecidableEq Node'] in
private theorem packet_reindex (e : Node' ≃ Node) (id : Node')
    (packet : Interface.Packet (network.ports (e id)).In) :
    (Equiv.sigmaCongrLeft (β := fun id => Interface.Packet (network.ports id).In) e).symm
      ⟨e id, packet⟩ = ⟨id, packet⟩ := by
  exact Equiv.symm_apply_apply
    (Equiv.sigmaCongrLeft (β := fun id => Interface.Packet (network.ports id).In) e) ⟨id, packet⟩

/-- Delivery respects dependent recipient types after relabeling. -/
theorem dispatch_reindex (e : Node' ≃ Node) (packet : Destination network)
    (state : State network S) :
    dispatch (reindexDestination network e packet) (state.reindex e) =
      (dispatch packet state).reindex e := by
  cases packet with
  | inr packet => rfl
  | inl packet =>
      rcases packet with ⟨target, packet⟩
      obtain ⟨target, rfl⟩ := e.surjective target
      simp [reindexDestination, packet_reindex, dispatch, State.reindex,
        Function.update_comp_eq_of_injective' _ e.injective]

/-- FIFO queue delivery is independent of the names of its recipients. -/
theorem deliver_reindex (e : Node' ≃ Node) (state : State network S) :
    deliver (state.reindex e) = (deliver state).reindex e := by
  cases h : state.pending with
  | nil => simp [deliver, State.reindex, h]
  | cons packet rest =>
      simp only [deliver, State.reindex, h, List.map_cons]
      change dispatch (reindexDestination network e packet)
          (({ state with pending := rest, elapsed := state.elapsed + 1 }).reindex e) = _
      exact dispatch_reindex e packet _

variable {m : Type → Type} [Monad m] [LawfulMonad m]

omit [DecidableEq Node'] in
/-- Token execution commutes with equality of network presentations. -/
theorem runToken_castNetwork {network' : Network Node boundary result}
    (h : network = network')
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (fuel : ℕ) (state : State network S) :
    runToken (castHandlers h impl) fuel (state.castNetwork h) =
      State.castNetwork h <$> runToken impl fuel state := by
  cases h
  change _ = id <$> _
  simp only [id_map]
  rfl

omit [DecidableEq Node'] in
/-- FIFO execution commutes with equality of network presentations, keeping the schedule. -/
theorem runFIFO_castNetwork {network' : Network Node boundary result}
    (h : network = network')
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (schedule : List (Activation Node)) (state : State network S) :
    runFIFO (castHandlers h impl) schedule (state.castNetwork h) =
      State.castNetwork h <$> runFIFO impl schedule state := by
  cases h
  change _ = id <$> _
  simp only [id_map]
  rfl

/-- A local activation commutes with relabeling its component and effect handler. -/
theorem activate_reindex
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (e : Node' ≃ Node) (discipline : Discipline) (id : Node') (state : State network S) :
    activate (network := network.reindex e) (fun id => impl (e id)) discipline id
        (state.reindex e) =
      State.reindex e <$> activate impl discipline (e id) state := by
  cases h : (network.component (e id)).view (state.localState (e id)) with
  | inl value => simp [activate, Network.reindex, State.reindex, h]
  | inr action =>
      rcases action with ⟨action, next⟩
      cases action with
      | effect operation =>
          simp [activate, Network.reindex, State.reindex, h,
            Function.update_comp_eq_of_injective' _ e.injective]
      | receive =>
          cases hin : state.inbox (e id) <;>
            simp [activate, Network.reindex, State.reindex, h, hin,
              Function.update_comp_eq_of_injective' _ e.injective]
      | send packet =>
          cases discipline with
          | fifo =>
              simp [activate, Network.reindex, State.reindex, h,
                Function.update_comp_eq_of_injective' _ e.injective]
          | token =>
              simpa [activate, Network.reindex, State.reindex, h,
                Function.update_comp_eq_of_injective' _ e.injective] using
                congrArg (pure (f := m)) (dispatch_reindex e (network.route (e id) packet)
                  { state with localState := Function.update state.localState (e id) (next ())
                               elapsed := state.elapsed + 1 })
      | tick =>
          simp [activate, Network.reindex, State.reindex, h,
            Function.update_comp_eq_of_injective' _ e.injective]
      | yield =>
          simp [activate, Network.reindex, State.reindex, h,
            Function.update_comp_eq_of_injective' _ e.injective]

omit [DecidableEq Node] [DecidableEq Node'] in
/-- Initialization commutes with relabeling, including the initial token holder. -/
theorem initial_reindex (e : Node' ≃ Node) (service : S) :
    initial (network.reindex e) service = (initial network service).reindex e := rfl

/-- One scheduled FIFO operation commutes with relabeling. -/
theorem fifoStep_reindex
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (e : Node' ≃ Node) (activation : Activation Node) (state : State network S) :
    fifoStep (network := network.reindex e) (fun id => impl (e id))
        (activation.reindex e) (state.reindex e) =
      State.reindex e <$> fifoStep impl activation state := by
  cases activation with
  | deliver => simp [fifoStep, Activation.reindex, deliver_reindex]
  | node id =>
      obtain ⟨id, rfl⟩ := e.surjective id
      simpa [fifoStep, Activation.reindex] using activate_reindex impl e .fifo id state

/-- Relabeling preserves every FIFO execution prefix, with all effects in their original order. -/
theorem runFIFO_reindex
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (e : Node' ≃ Node) (schedule : List (Activation Node)) (state : State network S) :
    runFIFO (network := network.reindex e) (fun id => impl (e id))
        (schedule.map (Activation.reindex e)) (state.reindex e) =
      State.reindex e <$> runFIFO impl schedule state := by
  induction schedule generalizing state with
  | nil => simp [runFIFO]
  | cons activation rest ih =>
      simp only [List.map_cons, runFIFO, fifoStep_reindex, bind_map_left, map_bind]
      exact bind_congr fun next => ih next

/-- Relabeling preserves token execution, including the identity selected by control transfer. -/
theorem runToken_reindex
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (e : Node' ≃ Node) (fuel : ℕ) (state : State network S) :
    runToken (network := network.reindex e) (fun id => impl (e id)) fuel (state.reindex e) =
      State.reindex e <$> runToken impl fuel state := by
  induction fuel generalizing state with
  | zero => simp [runToken]
  | succ fuel ih =>
      simp only [runToken]
      rw [activate_reindex]
      simp only [State.reindex, Equiv.apply_symm_apply, bind_map_left, map_bind]
      exact bind_congr fun next => ih next

/-- A proved graph factorization transports complete token prefixes, including residual
private states, shared service, queued traffic, control, and consumed fuel. -/
theorem runToken_reindex_cast {network' : Network Node' boundary result}
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (e : Node' ≃ Node) (h : network.reindex e = network')
    (fuel : ℕ) (state : State network S) :
    runToken (castHandlers h (fun id => impl (e id))) fuel ((state.reindex e).castNetwork h) =
      (fun next => (next.reindex e).castNetwork h) <$> runToken impl fuel state := by
  rw [runToken_castNetwork, runToken_reindex, Functor.map_map]

/-- A proved graph factorization transports complete FIFO prefixes with exactly the same
delivery positions and corresponding component activations. -/
theorem runFIFO_reindex_cast {network' : Network Node' boundary result}
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (e : Node' ≃ Node) (h : network.reindex e = network')
    (schedule : List (Activation Node)) (state : State network S) :
    runFIFO (castHandlers h (fun id => impl (e id)))
        (schedule.map (Activation.reindex e)) ((state.reindex e).castNetwork h) =
      (fun next => (next.reindex e).castNetwork h) <$> runFIFO impl schedule state := by
  rw [runFIFO_castNetwork, runFIFO_reindex, Functor.map_map]

end Interaction.UC.ReactiveNetwork
