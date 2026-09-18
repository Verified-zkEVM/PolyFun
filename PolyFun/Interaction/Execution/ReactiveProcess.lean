/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Interface
public import PolyFun.PFunctor.Dynamical.DynComputation

/-!
# Reactive polynomial processes

A reactive process is a dynamical computation over the polynomial of local effects,
receiving a typed input packet, sending a typed output packet, local work, and yielding
control. Receiving has the incoming packet type as its directions: the receiver's
continuation can depend on the actual message. Sending carries a concrete packet in its
position and has a single continuation.

`Process` and `Behavior` reuse `DynComputation` and `Resumption`. Boundary adaptation
is an ordinary polynomial lens: input packets pull back, and output packets push forward.
Execution policies interpret these actions separately; in particular, a tick is never
silently identified with doing no work.
-/

public section

namespace Interaction.Execution.ReactiveProcess

open PFunctor

/-- A terminal outcome distinguishes explicit abort from successful return. -/
inductive Outcome (α : Type) where
  | returned (value : α)
  | aborted
  deriving DecidableEq

/-- Positions of a reactive component's operation polynomial. -/
inductive Action (effect : PFunctor.{0, 0}) (boundary : PortBoundary) where
  | effect (operation : effect.A)
  | receive
  | send (packet : Interface.Packet boundary.Out)
  | tick
  | yield

/-- Responses supplied to each operation. Input messages are genuine responses, while
send, tick, and yield each have one continuation. -/
@[expose] def Response {effect : PFunctor.{0, 0}} {boundary : PortBoundary} :
    Action effect boundary → Type
  | .effect operation => effect.B operation
  | .receive => Interface.Packet boundary.In
  | .send _ => Unit
  | .tick => Unit
  | .yield => Unit

/-- The reactive action signature, expressed as a polynomial container. -/
@[expose] def signature (effect : PFunctor.{0, 0}) (boundary : PortBoundary) :
    PFunctor.{0, 0} := ⟨Action effect boundary, Response⟩

/-- A stateful component with explicit initialization and terminal outcomes. -/
abbrev Process (effect : PFunctor.{0, 0}) (boundary : PortBoundary)
    (input result : Type) := DynSystem.DynComputation.{0} (signature effect boundary)
      input (Outcome result)

/-- Exact possibly infinite behavior, retaining every operation and packet. -/
abbrev Behavior (effect : PFunctor.{0, 0}) (boundary : PortBoundary)
    (result : Type) := Resumption (signature effect boundary) (Outcome result)

variable {effect : PFunctor.{0, 0}} {Δ Γ : PortBoundary}

/-- Adapt a component's boundary using the input/output variance of a polynomial lens. -/
@[expose] def boundaryLens (f : PortBoundary.Hom Δ Γ) :
    Lens (signature effect Δ) (signature effect Γ) where
  toFunA
    | .effect operation => .effect operation
    | .receive => .receive
    | .send packet => .send (f.onOut.mapPacket packet)
    | .tick => .tick
    | .yield => .yield
  toFunB
    | .effect _, response => response
    | .receive, packet => f.onIn.mapPacket packet
    | .send _, response => response
    | .tick, response => response
    | .yield, response => response

/-- Boundary adaptation retains the private state carrier and changes only the interface. -/
abbrev mapBoundary {input result : Type} (f : PortBoundary.Hom Δ Γ)
    (process : Process effect Δ input result) : Process effect Γ input result :=
  process.wrap (boundaryLens f)

/-- The exact semantics of boundary adaptation is the existing resumption lens action. -/
theorem denote_mapBoundary {input result : Type} (f : PortBoundary.Hom Δ Γ)
    (process : Process effect Δ input result) (value : input) :
    (mapBoundary f process).denote value =
      Resumption.mapLens (boundaryLens f) (process.denote value) :=
  DynSystem.DynComputation.wrap_denote _ _ _

end Interaction.Execution.ReactiveProcess
