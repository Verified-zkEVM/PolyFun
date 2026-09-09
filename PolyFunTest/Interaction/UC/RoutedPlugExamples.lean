/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.OpenProcessInterleave

/-!
# Deterministic delivery between message queues

Each queue emits its pending messages in order and clears itself when scheduled.
The route appends that emitted batch to the other queue. These ordinary-import
examples exercise both routing directions, the composed sampler, empty batches,
and the observable difference between delivery and the trivial route.
-/

@[expose] public section

namespace PolyFunTest.Interaction.UC.RoutedPlugExamples

open _root_.Interaction _root_.Interaction.UC

variable {Message : Type}

/- Packet projections and the routed step's dependent path matchers use these
public reducer bodies during implicit unification. -/
attribute [local implicit_reducible] PFunctor.Idx
  PFunctor.DynSystem.expose PFunctor.DynSystem.update PFunctor.DynSystem.mk'

/-- One port carrying values of an arbitrary message type. -/
abbrev messageInterface (Message : Type) : Interface := ⟨PUnit, fun _ => Message⟩

/-- Both endpoints send and receive the same message type. -/
abbrev messageBoundary (Message : Type) : PortBoundary :=
  ⟨messageInterface Message, messageInterface Message⟩

/-- An internal node with an explicit batch of outgoing packets. -/
def silentNode {Γ : PortBoundary} {X : Type} (emit : PFunctor.Trace Γ.Out X) :
    OpenNodeContext.{0, 0} PUnit Γ X where
  controllers := fun _ => []
  views := fun _ => .hidden
  boundary := { isActivated := false, emit := emit }

/-- Encode a message batch as an ordered packet trace. -/
def packets (messages : List Message) : PFunctor.TraceList (messageInterface Message) :=
  FreeMonoid.ofList (messages.map fun message => ⟨PUnit.unit, message⟩)

/-- Emit the queue contents in one deterministic step and clear the queue. -/
abbrev queueStep (messages : List Message) :
    OpenStep.{0, 0} PUnit (messageBoundary Message) (List Message) where
  tree := TypeTree.node PUnit fun _ => TypeTree.done
  semantics := ⟨silentNode (fun _ => packets messages), fun _ => ⟨⟩⟩
  next := fun _ => []

/-- A message queue with a deterministic node sampler. -/
abbrev queue (Message : Type) : OpenProcess.{0, 0, 0, 0} Id PUnit (messageBoundary Message) where
  Proc := List Message
  step := queueStep
  stepSampler _ := ⟨pure PUnit.unit, fun _ => ⟨⟩⟩

/-- Append the emitted packets to the receiving queue, in emission order. -/
def deliver : (queue Message).Route (List Message) := fun messages path pending =>
  pending ++ (FreeMonoid.toList (OpenStep.boundaryTrace (queueStep messages) path)).map
    (fun packet => packet.2)

/-- Close two queues with a selected scheduler branch and explicit packet delivery. -/
def connected (Message : Type) (left : Bool) :
    OpenProcess.{0, 0, 0, 0} Id PUnit PortBoundary.empty :=
  (queue Message).interleaveRouted (queue Message)
    (OpenNodeContext.close PUnit (messageBoundary Message))
    (OpenNodeContext.close PUnit (messageBoundary Message))
    (silentNode 1) (pure ⟨left⟩) deliver deliver

/-- One deterministic sampled transition, using the process's own sampler. -/
def advance {Γ : PortBoundary} (process : OpenProcess.{0, 0, 0, 0} Id PUnit Γ)
    (state : process.Proc) : process.Proc :=
  (process.step state).next
    (Id.run (TypeTree.samplePath (process.step state).tree (process.stepSampler state)))

/-- The route reads the packets emitted by the step, preserving order and the existing queue. -/
theorem deliver_eq (messages pending : List Message)
    (path : (queueStep messages).tree.Path) :
    deliver messages path pending = pending ++ messages := by
  rcases path with ⟨⟨⟩, ⟨⟩⟩
  unfold deliver
  rw [OpenStep.boundaryTrace_eq]
  change pending ++ (FreeMonoid.toList
    (OpenNodeContext.boundaryTrace (Δ := messageBoundary Message)
      (TypeTree.node PUnit fun _ => TypeTree.done)
      ⟨silentNode (fun _ => packets messages), fun _ => ⟨⟩⟩ ⟨PUnit.unit, ⟨⟩⟩)).map
        (fun packet => packet.2) = _
  rw [OpenNodeContext.boundaryTrace_node, OpenNodeContext.boundaryTrace_done]
  simp [silentNode, packets, Function.comp_def]

/-- A sampled left step drains the selected queue into its peer. -/
theorem advance_connected_left (messages pending : List Message) :
    advance (connected Message true) (messages, pending) = ([], pending ++ messages) := by
  simp only [advance, connected, OpenProcess.interleaveRouted,
    Concurrent.ProcessOver.interleaveRouted, OpenProcess.toProcess,
    Concurrent.ProcessOver.ofStep, PFunctor.DynSystem.expose_mk', PFunctor.DynSystem.update_mk']
  rw [TypeTree.Sampler.interleave_eq, TypeTree.samplePath_node]
  simp only [pure_bind]
  rw [TypeTree.samplePath_node]
  simp only [TypeTree.samplePath_done, pure_bind]
  simp [Id.run, pure, deliver_eq]

/-- A sampled right step appends to the left queue in emission order. -/
theorem advance_connected_right (messages pending : List Message) :
    advance (connected Message false) (messages, pending) = (messages ++ pending, []) := by
  simp only [advance, connected, OpenProcess.interleaveRouted,
    Concurrent.ProcessOver.interleaveRouted, OpenProcess.toProcess,
    Concurrent.ProcessOver.ofStep, PFunctor.DynSystem.expose_mk', PFunctor.DynSystem.update_mk']
  rw [TypeTree.Sampler.interleave_eq, TypeTree.samplePath_node]
  simp only [pure_bind]
  rw [TypeTree.samplePath_node]
  simp only [TypeTree.samplePath_done, pure_bind]
  simp [Id.run, pure, deliver_eq]

/-- Closing the queues with ordinary interleaving leaves packet delivery disabled. -/
def disconnected (Message : Type) :
    OpenProcess.{0, 0, 0, 0} Id PUnit PortBoundary.empty :=
  (queue Message).interleave (queue Message)
    (OpenNodeContext.close PUnit (messageBoundary Message))
    (OpenNodeContext.close PUnit (messageBoundary Message))
    (silentNode 1) (pure ⟨true⟩)

/-- Without a route, the selected queue drains but its peer receives nothing. -/
theorem advance_disconnected (messages pending : List Message) :
    advance (disconnected Message) (messages, pending) = ([], pending) := by
  simp only [advance, disconnected, OpenProcess.interleave,
    Concurrent.ProcessOver.interleave, OpenProcess.toProcess,
    Concurrent.ProcessOver.ofStep, PFunctor.DynSystem.expose_mk', PFunctor.DynSystem.update_mk']
  rw [TypeTree.Sampler.interleave_eq, TypeTree.samplePath_node]
  simp only [pure_bind]
  rw [TypeTree.samplePath_node]
  simp only [TypeTree.samplePath_done, pure_bind]
  simp [Id.run, pure]

/-- Empty batches preserve the receiving queue. -/
example (pending : List Message) :
    advance (connected Message true) ([], pending) = ([], pending) := by
  simpa only [List.append_nil] using advance_connected_left ([] : List Message) pending

/-- A concrete batch retains both the receiver's existing contents and emission order. -/
example : advance (connected Nat true) ([2, 3], [1]) = ([], [1, 2, 3]) :=
  advance_connected_left _ _

/-- Removing delivery changes the resulting state for a nonempty emitted batch. -/
example : advance (connected Nat true) ([2, 3], [1]) ≠
    advance (disconnected Nat) ([2, 3], [1]) := by
  rw [advance_connected_left, advance_disconnected]
  change (([] : List Nat), [1, 2, 3]) ≠ ([], [1])
  decide

end PolyFunTest.Interaction.UC.RoutedPlugExamples
