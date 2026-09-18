/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveProcess

/-!
# Open routing diagrams of reactive polynomial machines

A diagram contains typed components and routes without selecting a global environment.
Parallel composition and wiring preserve the components themselves. Boundary maps translate
only external traffic, and wiring resolves an outgoing shared-boundary packet to the receiving
component's ingress. Every component retains its own polynomial effect and private state.

The designated environment and execution policy are supplied when a diagram is run. In
particular, composing two fragments does not choose two competing recipients of yielded control.
Boundary functions are structural semantic data; their executable cost is a separate obligation.
-/

public section

namespace Interaction.Execution.ReactiveNetwork

open PFunctor ReactiveProcess

/-- Typed open components and their internal and external packet routes. -/
structure Diagram (Node : Type) (boundary : PortBoundary) (result : Type) where
  /-- Each component's declared local operations. -/
  effect : Node → PFunctor.{0, 0}
  /-- Each component's incoming and outgoing packet types. -/
  ports : Node → PortBoundary
  /-- Initialized component machines with private state carriers. -/
  component : (id : Node) → Process (effect id) (ports id) Unit result
  /-- Internal recipients or exposed outputs for every component send. -/
  route : (id : Node) → Interface.Packet (ports id).Out →
    ((target : Node) × Interface.Packet (ports target).In) ⊕ Interface.Packet boundary.Out
  /-- Component recipients of exposed input packets. -/
  ingress : Interface.Packet boundary.In → (target : Node) × Interface.Packet (ports target).In

namespace Diagram

variable {Node Node₁ Node₂ result : Type} {Δ Δ₁ Δ₂ Γ : PortBoundary}

/-- Diagrams agree when their interfaces, initialized machines, and typed routes agree. -/
@[ext] theorem ext {left right : Diagram Node Δ result}
    (heffect : left.effect = right.effect) (hports : left.ports = right.ports)
    (hcomponent : HEq left.component right.component)
    (hroute : HEq left.route right.route) (hingress : HEq left.ingress right.ingress) :
    left = right := by
  cases left
  cases right
  cases heffect
  cases hports
  cases hcomponent
  cases hroute
  cases hingress
  rfl

/-- Relabel components and dependent packet recipients along an identity bijection. -/
@[expose] def reindex (diagram : Diagram Node Δ result) (e : Node₁ ≃ Node) :
    Diagram Node₁ Δ result where
  effect node := diagram.effect (e node)
  ports node := diagram.ports (e node)
  component node := diagram.component (e node)
  route node packet := (diagram.route (e node) packet).map (Equiv.sigmaCongrLeft e).symm id
  ingress packet := (Equiv.sigmaCongrLeft e).symm (diagram.ingress packet)

/-- Place one initialized reactive machine at a single node. -/
@[expose] def atom {effect : PFunctor.{0, 0}} (process : Process effect Δ Unit result) :
    Diagram Unit Δ result where
  effect _ := effect
  ports _ := Δ
  component _ := process
  route _ packet := .inr packet
  ingress packet := ⟨(), packet⟩

/-- Adapt the external boundary without changing component interfaces or private states. -/
@[expose] def map (f : PortBoundary.Hom Δ₁ Δ₂) (diagram : Diagram Node Δ₁ result) :
    Diagram Node Δ₂ result where
  effect := diagram.effect
  ports := diagram.ports
  component := diagram.component
  route node packet := (diagram.route node packet).map id (f.onOut.mapPacket)
  ingress packet := diagram.ingress (f.onIn.mapPacket packet)

/-- Parallel composition uses disjoint node identities and retains both external boundaries. -/
@[expose] def par (left : Diagram Node₁ Δ₁ result) (right : Diagram Node₂ Δ₂ result) :
    Diagram (Node₁ ⊕ Node₂) (PortBoundary.tensor Δ₁ Δ₂) result where
  effect
    | .inl node => left.effect node
    | .inr node => right.effect node
  ports
    | .inl node => left.ports node
    | .inr node => right.ports node
  component
    | .inl node => left.component node
    | .inr node => right.component node
  route
    | .inl node, packet => match left.route node packet with
      | .inl ⟨target, packet⟩ => .inl ⟨.inl target, packet⟩
      | .inr ⟨port, message⟩ => .inr ⟨.inl port, message⟩
    | .inr node, packet => match right.route node packet with
      | .inl ⟨target, packet⟩ => .inl ⟨.inr target, packet⟩
      | .inr ⟨port, message⟩ => .inr ⟨.inr port, message⟩
  ingress
    | ⟨.inl port, message⟩ => let ⟨target, packet⟩ := left.ingress ⟨port, message⟩
      ⟨.inl target, packet⟩
    | ⟨.inr port, message⟩ => let ⟨target, packet⟩ := right.ingress ⟨port, message⟩
      ⟨.inr target, packet⟩

/-- Wire a shared boundary directly to the other fragment's ingress. Sends still consume
their ordinary local and delivery activations; no component or shared service is copied. -/
@[expose] def wire (left : Diagram Node₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : Diagram Node₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result) :
    Diagram (Node₁ ⊕ Node₂) (PortBoundary.tensor Δ₁ Δ₂) result where
  effect
    | .inl node => left.effect node
    | .inr node => right.effect node
  ports
    | .inl node => left.ports node
    | .inr node => right.ports node
  component
    | .inl node => left.component node
    | .inr node => right.component node
  route
    | .inl node, packet => match left.route node packet with
      | .inl ⟨target, packet⟩ => .inl ⟨.inl target, packet⟩
      | .inr ⟨.inl port, message⟩ => .inr ⟨.inl port, message⟩
      | .inr ⟨.inr port, message⟩ =>
          let ⟨target, packet⟩ := right.ingress ⟨.inl port, message⟩
          .inl ⟨.inr target, packet⟩
    | .inr node, packet => match right.route node packet with
      | .inl ⟨target, packet⟩ => .inl ⟨.inr target, packet⟩
      | .inr ⟨.inl port, message⟩ =>
          let ⟨target, packet⟩ := left.ingress ⟨.inr port, message⟩
          .inl ⟨.inl target, packet⟩
      | .inr ⟨.inr port, message⟩ => .inr ⟨.inr port, message⟩
  ingress
    | ⟨.inl port, message⟩ => let ⟨target, packet⟩ := left.ingress ⟨.inl port, message⟩
      ⟨.inl target, packet⟩
    | ⟨.inr port, message⟩ => let ⟨target, packet⟩ := right.ingress ⟨.inr port, message⟩
      ⟨.inr target, packet⟩

/-- Close two opposite boundaries while retaining the identities of every component. -/
@[expose] def plug (left : Diagram Node₁ Δ result)
    (right : Diagram Node₂ (PortBoundary.swap Δ) result) :
    Diagram (Node₁ ⊕ Node₂) PortBoundary.empty result :=
  map (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
    (wire (map (PortBoundary.Equiv.tensorEmptyLeft Δ).symm.toHom left)
      (map (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ)).symm.toHom right))

end Diagram

end Interaction.Execution.ReactiveNetwork
