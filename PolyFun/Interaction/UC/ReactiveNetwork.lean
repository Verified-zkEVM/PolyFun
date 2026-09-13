/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ReactiveProcess
public import PolyFun.PFunctor.Handler

/-!
# Typed reactive networks with explicit execution disciplines

A static network assigns each stable component identity its own polynomial effect and
packet interfaces. Routes deliver output packets to typed input mailboxes or the external
boundary. All handlers share one service state, but each component has only its declared
effect interface. A handler invocation is atomic; its internal cost is a separate obligation.

Both runners use the same component machines and routing data. Token passing delivers a send
immediately and transfers control to its recipient. FIFO execution enqueues sends and delivers
the oldest pending packet on a delivery activation. Waiting with an empty mailbox consumes an
activation without advancing the component. A non-environment return or yield gives the token
back to the environment. Finite execution retains residual machines and pending packets.

The external output trace is execution data, not a security observation by itself. In
particular, callers must justify their initialization, permitted input, scheduler access,
and output projection when instantiating a security notion.
-/

public section

namespace Interaction.UC.ReactiveNetwork

open PFunctor ReactiveProcess

/-- A static typed routing diagram of reactive machines. -/
structure Network (Node : Type) (boundary : PortBoundary) (result : Type) where
  /-- Each component exposes only its own effect signature. -/
  effect : Node → PFunctor.{0, 0}
  /-- Typed incoming and outgoing packet interfaces of each component. -/
  ports : Node → PortBoundary
  /-- Initialized machines, retaining separate private state carriers. -/
  component : (id : Node) → Process (effect id) (ports id) Unit result
  /-- An output goes to one internal mailbox or to the external output boundary. -/
  route : (id : Node) → Interface.Packet (ports id).Out →
    ((target : Node) × Interface.Packet (ports target).In) ⊕ Interface.Packet boundary.Out
  /-- External input packets have typed internal recipients. -/
  ingress : Interface.Packet boundary.In → (target : Node) × Interface.Packet (ports target).In
  /-- Initial holder of control and recipient of control after yield or termination. -/
  environment : Node

variable {Node result S : Type} {boundary : PortBoundary}

/-- One already-routed packet, including a typed destination for internal traffic. -/
abbrev Destination (network : Network Node boundary result) :=
  ((target : Node) × Interface.Packet (network.ports target).In) ⊕ Interface.Packet boundary.Out

/-- Complete residual state of an execution. Private machine and service states remain
separate from the external output trace. -/
structure State (network : Network Node boundary result) (S : Type) where
  /-- Current private state of every component. -/
  localState : (id : Node) → (network.component id).State
  /-- Delivered input packets, oldest first, for each component. -/
  inbox : (id : Node) → List (Interface.Packet (network.ports id).In)
  /-- Shared state used by the effect handlers. -/
  service : S
  /-- Routed sends awaiting FIFO delivery. -/
  pending : List (Destination network)
  /-- Packets actually delivered to the external boundary, in delivery order. -/
  output : List (Interface.Packet boundary.Out)
  /-- Current token holder; FIFO schedules choose activations independently. -/
  focus : Node
  /-- Number of consumed local or delivery activations, including no-ops. -/
  elapsed : ℕ

/-- Initial state with no traffic and the environment holding control. -/
@[expose] def initial (network : Network Node boundary result) (service : S) : State network S :=
  ⟨fun id => (network.component id).init (), fun _ => [], service, [], [], network.environment, 0⟩

/-- The two execution policies interpret sending differently. -/
inductive Discipline where
  | token
  | fifo
  deriving DecidableEq

/-- An explicit FIFO schedule either advances a component or delivers one queued packet. -/
inductive Activation (Node : Type) where
  | node (id : Node)
  | deliver
  deriving DecidableEq

variable [DecidableEq Node] {network : Network Node boundary result}

/-- Deliver a routed packet and select its recipient as token holder. FIFO execution retains
this field as bookkeeping but does not consult it to choose its next activation. -/
@[expose] def dispatch (packet : Destination network) (state : State network S) : State network S :=
  match packet with
  | .inl ⟨target, packet⟩ =>
      { state with inbox := Function.update state.inbox target (state.inbox target ++ [packet])
                   focus := target }
  | .inr packet => { state with output := state.output ++ [packet], focus := network.environment }

/-- Feed one permitted external input through the diagram's declared ingress route.
Input injection does not consume machine fuel; its cost and admissibility belong to the caller. -/
@[expose] def input (packet : Interface.Packet boundary.In) (state : State network S) :
    State network S := dispatch (.inl (network.ingress packet)) state

/-- Deliver the oldest pending packet. An empty queue still consumes a delivery activation. -/
@[expose] def deliver (state : State network S) : State network S :=
  match state.pending with
  | [] => { state with elapsed := state.elapsed + 1 }
  | packet :: rest => dispatch packet { state with pending := rest, elapsed := state.elapsed + 1 }

variable {m : Type → Type} [Monad m]

/-- Advance one component by one polynomial operation. The effect interpreter is indexed
by the acting component and all invocations thread the same service state. -/
@[expose] def activate
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (discipline : Discipline) (id : Node) (state : State network S) : m (State network S) := do
  let state := { state with elapsed := state.elapsed + 1 }
  match (network.component id).view (state.localState id) with
  | .inl _ => pure { state with focus := network.environment }
  | .inr ⟨.effect operation, next⟩ =>
      let (answer, service) ← (impl id operation).run state.service
      pure { state with localState := Function.update state.localState id (next answer), service }
  | .inr ⟨.receive, next⟩ =>
      match state.inbox id with
      | [] => pure state
      | packet :: rest => pure { state with
          localState := Function.update state.localState id (next packet)
          inbox := Function.update state.inbox id rest }
  | .inr ⟨.send packet, next⟩ =>
      let state := { state with localState := Function.update state.localState id (next ()) }
      match discipline with
      | .token => pure (dispatch (network.route id packet) state)
      | .fifo => pure { state with pending := state.pending ++ [network.route id packet] }
  | .inr ⟨.tick, next⟩ =>
      pure { state with localState := Function.update state.localState id (next ()) }
  | .inr ⟨.yield, next⟩ => pure { state with
      localState := Function.update state.localState id (next ())
      focus := network.environment }

/-- One FIFO activation. A schedule contains identities rather than positions in a binary
composition tree. -/
@[expose] def fifoStep
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (activation : Activation Node) (state : State network S) : m (State network S) :=
  match activation with
  | .node id => activate impl .fifo id state
  | .deliver => pure (deliver state)

/-- Execute a finite FIFO schedule, retaining the complete residual configuration. -/
@[expose] def runFIFO
    (impl : (id : Node) → Handler (StateT S m) (network.effect id)) :
    List (Activation Node) → State network S → m (State network S)
  | [], state => pure state
  | activation :: rest, state => fifoStep impl activation state >>= runFIFO impl rest

/-- Execute a finite token-passing prefix. Only the current holder can be activated. -/
@[expose] def runToken
    (impl : (id : Node) → Handler (StateT S m) (network.effect id)) :
    ℕ → State network S → m (State network S)
  | 0, state => pure state
  | fuel + 1, state => activate impl .token state.focus state >>= runToken impl fuel

/-- A component's terminal outcome, if it has reached one. Absence is a residual computation,
which may be blocked, runnable, or divergent; it is not an abort. -/
@[expose] def outcome (id : Node) (state : State network S) : Option (Outcome result) :=
  match (network.component id).view (state.localState id) with
  | .inl value => some value
  | .inr _ => none

variable [LawfulMonad m]

/-- FIFO execution can be paused and resumed at any schedule prefix. -/
theorem runFIFO_append
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (first rest : List (Activation Node)) (state : State network S) :
    runFIFO impl (first ++ rest) state = (runFIFO impl first state >>= runFIFO impl rest) := by
  induction first generalizing state with
  | nil => simp [runFIFO]
  | cons activation first ih =>
      simp only [List.cons_append, runFIFO, bind_assoc]
      exact bind_congr ih

/-- Token execution can be paused and resumed without resetting control or mailboxes. -/
theorem runToken_add
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (first rest : ℕ) (state : State network S) :
    runToken impl (first + rest) state = (runToken impl first state >>= runToken impl rest) := by
  induction first generalizing state with
  | zero => simp [runToken]
  | succ first ih =>
      simp only [Nat.succ_add, runToken, bind_assoc]
      exact bind_congr ih

end Interaction.UC.ReactiveNetwork
