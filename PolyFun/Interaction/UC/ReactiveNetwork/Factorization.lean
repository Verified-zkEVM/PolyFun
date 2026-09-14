/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.Interface
public import PolyFun.Interaction.UC.ReactiveNetwork.Transport

/-!
# Factorization of routed reactive diagrams

Closing a parallel composition can be factored by moving one component into the context.
The result preserves the actual machines and packet routes after the explicit reassociation
of component identities. No scheduler is resampled, no service is duplicated, and no machine
activation is removed. The runtime transport laws consequently preserve complete prefixes.
-/

public section

namespace Interaction.UC.ReactiveNetwork

open PFunctor ReactiveProcess

namespace Diagram

variable {N₁ N₂ K result : Type} {Δ₁ Δ₂ : PortBoundary}

/-- A send from the left of a closed diagram retains internal traffic and directs exposed
traffic to the right fragment's ingress. -/
theorem plug_route_left (left : Diagram N₁ Δ₁ result)
    (right : Diagram N₂ (PortBoundary.swap Δ₁) result) (node : N₁)
    (packet : Interface.Packet (left.ports node).Out) :
    (left.plug right).route (.inl node) packet =
      match left.route node packet with
      | .inl ⟨target, packet⟩ => .inl ⟨.inl target, packet⟩
      | .inr packet => .inl ⟨.inr (right.ingress packet).1, (right.ingress packet).2⟩ := by
  rcases hr : left.route node packet with ⟨target, response⟩ | ⟨port, message⟩
  all_goals simp only [plug, map, wire, hr, Sum.map_inl]
  all_goals rfl

/-- A send from the closing context reaches the left fragment's declared ingress. -/
theorem plug_route_right (left : Diagram N₁ Δ₁ result)
    (right : Diagram N₂ (PortBoundary.swap Δ₁) result) (node : N₂)
    (packet : Interface.Packet (right.ports node).Out) :
    (left.plug right).route (.inr node) packet =
      match right.route node packet with
      | .inl ⟨target, packet⟩ => .inl ⟨.inr target, packet⟩
      | .inr packet => .inl ⟨.inl (left.ingress packet).1, (left.ingress packet).2⟩ := by
  rcases hr : right.route node packet with ⟨target, response⟩ | ⟨port, message⟩
  all_goals simp only [plug, map, wire, hr, Sum.map_inl]
  all_goals rfl

/-- Move the right parallel component into the closing context. -/
@[expose] def parContextLeft (right : Diagram N₂ Δ₂ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    Diagram (K ⊕ N₂) (PortBoundary.swap Δ₁) result :=
  (context.wire (Γ := PortBoundary.swap Δ₂) (Δ₁ := PortBoundary.swap Δ₁)
    (right.map (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm.toHom)).map
      (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁)).toHom

/-- The identity correspondence when the right component becomes part of the context. -/
@[expose] def parContextLeftEquiv (N₁ N₂ K : Type) : (N₁ ⊕ (K ⊕ N₂)) ≃ ((N₁ ⊕ N₂) ⊕ K) :=
  (Equiv.sumCongr (Equiv.refl N₁) (Equiv.sumComm K N₂)).trans
    (Equiv.sumAssoc N₁ N₂ K).symm

@[simp] theorem parContextLeftEquiv_left (node : N₁) :
    parContextLeftEquiv N₁ N₂ K (.inl node) = .inl (.inl node) := rfl

@[simp] theorem parContextLeftEquiv_context (node : K) :
    parContextLeftEquiv N₁ N₂ K (.inr (.inl node)) = .inr node := rfl

@[simp] theorem parContextLeftEquiv_right (node : N₂) :
    parContextLeftEquiv N₁ N₂ K (.inr (.inr node)) = .inl (.inr node) := rfl

private theorem par_route_left (left : Diagram N₁ Δ₁ result) (right : Diagram N₂ Δ₂ result)
    (node : N₁) (packet : Interface.Packet (left.ports node).Out) :
    (left.par right).route (.inl node) packet =
      match left.route node packet with
      | .inl ⟨target, response⟩ => .inl ⟨.inl target, response⟩
      | .inr ⟨port, message⟩ => .inr ⟨.inl port, message⟩ := rfl

private theorem par_route_right (left : Diagram N₁ Δ₁ result) (right : Diagram N₂ Δ₂ result)
    (node : N₂) (packet : Interface.Packet (right.ports node).Out) :
    (left.par right).route (.inr node) packet =
      match right.route node packet with
      | .inl ⟨target, response⟩ => .inl ⟨.inr target, response⟩
      | .inr ⟨port, message⟩ => .inr ⟨.inr port, message⟩ := rfl

private theorem context_route_left (right : Diagram N₂ Δ₂ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (node : K) (packet : Interface.Packet (context.ports node).Out) :
    (right.parContextLeft context).route (.inl node) packet =
      match context.route node packet with
      | .inl ⟨target, response⟩ => .inl ⟨.inl target, response⟩
      | .inr ⟨.inl port, message⟩ => .inr ⟨port, message⟩
      | .inr ⟨.inr port, message⟩ =>
          .inl ⟨.inr (right.ingress ⟨port, message⟩).1, (right.ingress ⟨port, message⟩).2⟩ := by
  rcases hr : context.route node packet with ⟨target, response⟩ | ⟨port, message⟩
  · simp only [parContextLeft, map, wire, hr, Sum.map_inl]
    rfl
  · rcases port with port | port <;>
      simp only [parContextLeft, map, wire, hr] <;> rfl

private theorem context_route_right (right : Diagram N₂ Δ₂ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (node : N₂) (packet : Interface.Packet (right.ports node).Out) :
    (right.parContextLeft context).route (.inr node) packet =
      match right.route node packet with
      | .inl ⟨target, response⟩ => .inl ⟨.inr target, response⟩
      | .inr ⟨port, message⟩ =>
          .inl ⟨.inl (context.ingress ⟨.inr port, message⟩).1,
            (context.ingress ⟨.inr port, message⟩).2⟩ := by
  rcases hr : right.route node packet with ⟨target, response⟩ | ⟨port, message⟩
  all_goals simp only [parContextLeft, map, wire, hr, Sum.map_inl]
  all_goals rfl

private theorem context_ingress (right : Diagram N₂ Δ₂ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (port : Δ₁.Out.A) (message : Δ₁.Out.B port) :
    (right.parContextLeft context).ingress ⟨port, message⟩ =
      ⟨.inl (context.ingress ⟨.inl port, message⟩).1,
        (context.ingress ⟨.inl port, message⟩).2⟩ := rfl

private theorem par_ingress_left (left : Diagram N₁ Δ₁ result)
    (right : Diagram N₂ Δ₂ result) (port : Δ₁.In.A) (message : Δ₁.In.B port) :
    (left.par right).ingress ⟨.inl port, message⟩ =
      ⟨.inl (left.ingress ⟨port, message⟩).1, (left.ingress ⟨port, message⟩).2⟩ := rfl

private theorem par_ingress_right (left : Diagram N₁ Δ₁ result)
    (right : Diagram N₂ Δ₂ result) (port : Δ₂.In.A) (message : Δ₂.In.B port) :
    (left.par right).ingress ⟨.inr port, message⟩ =
      ⟨.inr (right.ingress ⟨port, message⟩).1, (right.ingress ⟨port, message⟩).2⟩ := rfl

private theorem packet_left {β : ((N₁ ⊕ N₂) ⊕ K) → Type}
    (node : N₁) (packet : β (.inl (.inl node))) :
    (Equiv.sigmaCongrLeft (β := β) (parContextLeftEquiv N₁ N₂ K)).symm
      ⟨.inl (.inl node), packet⟩ = ⟨.inl node, packet⟩ :=
  Equiv.symm_apply_apply
    (Equiv.sigmaCongrLeft (β := β) (parContextLeftEquiv N₁ N₂ K)) ⟨.inl node, packet⟩

private theorem packet_right {β : ((N₁ ⊕ N₂) ⊕ K) → Type}
    (node : N₂) (packet : β (.inl (.inr node))) :
    (Equiv.sigmaCongrLeft (β := β) (parContextLeftEquiv N₁ N₂ K)).symm
      ⟨.inl (.inr node), packet⟩ = ⟨.inr (.inr node), packet⟩ :=
  Equiv.symm_apply_apply
    (Equiv.sigmaCongrLeft (β := β) (parContextLeftEquiv N₁ N₂ K)) ⟨.inr (.inr node), packet⟩

private theorem packet_context {β : ((N₁ ⊕ N₂) ⊕ K) → Type}
    (node : K) (packet : β (.inr node)) :
    (Equiv.sigmaCongrLeft (β := β) (parContextLeftEquiv N₁ N₂ K)).symm
      ⟨.inr node, packet⟩ = ⟨.inr (.inl node), packet⟩ :=
  Equiv.symm_apply_apply
    (Equiv.sigmaCongrLeft (β := β) (parContextLeftEquiv N₁ N₂ K)) ⟨.inr (.inl node), packet⟩

private theorem routed_packet_heq {α δ : Type} {β γ : α → Type} (hfamily : β = γ)
    (node : α) (packet : β node) (packet' : γ node) (hpacket : HEq packet packet') :
    HEq (Sum.inl ⟨node, packet⟩ : (Sigma β) ⊕ δ)
      (Sum.inl ⟨node, packet'⟩ : (Sigma γ) ⊕ δ) := by
  cases hfamily
  cases hpacket
  rfl

attribute [local implicit_reducible] plug map wire par reindex parContextLeft parContextLeftEquiv
  Equiv.sumComm

/-- Parallel closure and its residual context have the same component interfaces and routes
under the explicit identity correspondence. -/
theorem close_par_left (left : Diagram N₁ Δ₁ result) (right : Diagram N₂ Δ₂ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    ((left.par right).plug context).reindex (parContextLeftEquiv N₁ N₂ K) =
      left.plug (right.parContextLeft context) := by
  apply Diagram.ext
  · funext node
    rcases node with node | node | node <;> rfl
  · funext node
    rcases node with node | node | node <;> rfl
  · apply Function.hfunext rfl
    intro node node' hnode
    cases hnode
    rcases node with node | node | node <;> rfl
  · apply Function.hfunext rfl
    intro node node' hnode
    cases hnode
    rcases node with node | node | node
    all_goals
      apply Function.hfunext rfl
      intro packet packet' hpacket
      cases hpacket
    case' inl.refl =>
      change Interface.Packet (left.ports node).Out at packet
      rcases hr : left.route node packet with ⟨target, response⟩ | ⟨port, message⟩
    case' inr.inl.refl =>
      change Interface.Packet (context.ports node).Out at packet
      rcases hr : context.route node packet with ⟨target, response⟩ | ⟨port, message⟩
      case' inr => rcases port with port | port
    case' inr.inr.refl =>
      change Interface.Packet (right.ports node).Out at packet
      rcases hr : right.route node packet with ⟨target, response⟩ | ⟨port, message⟩
    all_goals
      simp only [reindex, parContextLeftEquiv_left, parContextLeftEquiv_context,
        parContextLeftEquiv_right]
      simp only [plug_route_left (left.par right) context,
        plug_route_right (left.par right) context,
        plug_route_left left (right.parContextLeft context),
        plug_route_right left (right.parContextLeft context),
        par_route_left left right, par_route_right left right,
        context_route_left right context, context_route_right right context,
        hr, Sum.map_inl, context_ingress right context,
        par_ingress_left left right, par_ingress_right left right,
        packet_left, packet_right, packet_context]
      apply routed_packet_heq
      · funext target
        rcases target with target | target | target <;> rfl
      · rfl
  · apply Function.hfunext rfl
    intro packet _ _
    exact packet.1.elim

private theorem swap_node_left (node : N₁) :
    Equiv.sumComm N₂ N₁ (.inr node) = .inl node := rfl

private theorem swap_node_right (node : N₂) :
    Equiv.sumComm N₂ N₁ (.inl node) = .inr node := rfl

private theorem swap_packet_left {β : (N₁ ⊕ N₂) → Type}
    (node : N₁) (packet : β (.inl node)) :
    (Equiv.sigmaCongrLeft (β := β) (Equiv.sumComm N₂ N₁)).symm
      ⟨.inl node, packet⟩ = ⟨.inr node, packet⟩ :=
  Equiv.symm_apply_apply
    (Equiv.sigmaCongrLeft (β := β) (Equiv.sumComm N₂ N₁)) ⟨.inr node, packet⟩

private theorem swap_packet_right {β : (N₁ ⊕ N₂) → Type}
    (node : N₂) (packet : β (.inr node)) :
    (Equiv.sigmaCongrLeft (β := β) (Equiv.sumComm N₂ N₁)).symm
      ⟨.inr node, packet⟩ = ⟨.inl node, packet⟩ :=
  Equiv.symm_apply_apply
    (Equiv.sigmaCongrLeft (β := β) (Equiv.sumComm N₂ N₁)) ⟨.inl node, packet⟩

/-- Interchanging the two sides of closure relabels components but does not change traffic. -/
theorem plug_comm (left : Diagram N₁ Δ₁ result)
    (right : Diagram N₂ (PortBoundary.swap Δ₁) result) :
    (left.plug right).reindex (Equiv.sumComm N₂ N₁) = right.plug left := by
  apply Diagram.ext
  · funext node
    rcases node with node | node <;> rfl
  · funext node
    rcases node with node | node <;> rfl
  · apply Function.hfunext rfl
    intro node node' hnode
    cases hnode
    rcases node with node | node <;> rfl
  · apply Function.hfunext rfl
    intro node node' hnode
    cases hnode
    rcases node with node | node
    all_goals
      apply Function.hfunext rfl
      intro packet packet' hpacket
      cases hpacket
    case' inl.refl =>
      change Interface.Packet (right.ports node).Out at packet
      rcases hr : right.route node packet with ⟨target, response⟩ | response
    case' inr.refl =>
      change Interface.Packet (left.ports node).Out at packet
      rcases hr : left.route node packet with ⟨target, response⟩ | response
    all_goals
      simp only [reindex, swap_node_left, swap_node_right]
      simp only [plug_route_left left right, plug_route_right left right,
        plug_route_left right left, plug_route_right right left, hr, Sum.map_inl,
        swap_packet_left, swap_packet_right]
      apply routed_packet_heq
      · funext target
        rcases target with target | target <;> rfl
      · rfl
  · apply Function.hfunext rfl
    intro packet _ _
    exact packet.1.elim

/-- Boundary adaptation can be moved into the closing context without changing any machine. -/
theorem map_plug (f : PortBoundary.Hom Δ₁ Δ₂) (left : Diagram N₁ Δ₁ result)
    (context : Diagram K (PortBoundary.swap Δ₂) result) :
    (left.map f).plug context = left.plug (context.map f.swap) := by
  apply Diagram.ext
  · rfl
  · rfl
  · rfl
  · apply heq_of_eq
    funext node packet
    rcases node with node | node
    · rw [plug_route_left, plug_route_left]
      rcases hr : left.route node packet with ⟨target, response⟩ | response <;>
        simp only [map, hr, Sum.map_inl, Sum.map_inr] <;> rfl
    · rw [plug_route_right, plug_route_right]
      rcases hr : context.route node packet with ⟨target, response⟩ | response <;>
        simp only [map, hr, Sum.map_inl, Sum.map_inr] <;> rfl
  · apply Function.hfunext rfl
    intro packet _ _
    exact packet.1.elim

variable {Γ : PortBoundary}

/-- Move the right wired component into the context, preserving the shared ports. -/
@[expose] def wireContextLeft
    (right : Diagram N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    Diagram (K ⊕ N₂) (PortBoundary.swap (PortBoundary.tensor Δ₁ Γ)) result :=
  context.wire (Δ₁ := PortBoundary.swap Δ₁) (Γ := PortBoundary.swap Δ₂)
    (Δ₂ := PortBoundary.swap Γ)
    (right.map (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom)

private theorem wire_context_route_left
    (right : Diagram N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (node : K) (packet : Interface.Packet (context.ports node).Out) :
    (right.wireContextLeft context).route (.inl node) packet =
      match context.route node packet with
      | .inl ⟨target, response⟩ => .inl ⟨.inl target, response⟩
      | .inr ⟨.inl port, message⟩ => .inr ⟨.inl port, message⟩
      | .inr ⟨.inr port, message⟩ =>
          .inl ⟨.inr (right.ingress ⟨.inr port, message⟩).1,
            (right.ingress ⟨.inr port, message⟩).2⟩ := by
  rcases hr : context.route node packet with ⟨target, response⟩ | ⟨port, message⟩
  · simp only [wireContextLeft, wire, hr]
  · rcases port with port | port <;> simp only [wireContextLeft, wire, hr]
    rfl

private theorem wire_context_route_right
    (right : Diagram N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (node : N₂) (packet : Interface.Packet (right.ports node).Out) :
    (right.wireContextLeft context).route (.inr node) packet =
      match right.route node packet with
      | .inl ⟨target, response⟩ => .inl ⟨.inr target, response⟩
      | .inr ⟨.inl port, message⟩ => .inr ⟨.inr port, message⟩
      | .inr ⟨.inr port, message⟩ =>
          .inl ⟨.inl (context.ingress ⟨.inr port, message⟩).1,
            (context.ingress ⟨.inr port, message⟩).2⟩ := by
  rcases hr : right.route node packet with ⟨target, response⟩ | ⟨port, message⟩
  · simp only [wireContextLeft, wire, map, hr, Sum.map_inl]
    rfl
  · rcases port with port | port <;>
      simp only [wireContextLeft, wire, map, hr] <;> rfl

private theorem wire_context_ingress_left
    (right : Diagram N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (port : Δ₁.Out.A) (message : Δ₁.Out.B port) :
    (right.wireContextLeft context).ingress ⟨.inl port, message⟩ =
      ⟨.inl (context.ingress ⟨.inl port, message⟩).1,
        (context.ingress ⟨.inl port, message⟩).2⟩ := rfl

private theorem wire_context_ingress_right
    (right : Diagram N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (port : Γ.Out.A) (message : Γ.Out.B port) :
    (right.wireContextLeft context).ingress ⟨.inr port, message⟩ =
      ⟨.inr (right.ingress ⟨.inl port, message⟩).1,
        (right.ingress ⟨.inl port, message⟩).2⟩ := rfl

attribute [local implicit_reducible] wireContextLeft

/-- Wired closure has exactly the same routes and machines after moving its right component
into the context. The common boundary is still delivered to the same receiving component. -/
theorem close_wire_left
    (left : Diagram N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : Diagram N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    ((left.wire right).plug context).reindex (parContextLeftEquiv N₁ N₂ K) =
      left.plug (right.wireContextLeft context) := by
  apply Diagram.ext
  · funext node
    rcases node with node | node | node <;> rfl
  · funext node
    rcases node with node | node | node <;> rfl
  · apply Function.hfunext rfl
    intro node node' hnode
    cases hnode
    rcases node with node | node | node <;> rfl
  · apply Function.hfunext rfl
    intro node node' hnode
    cases hnode
    rcases node with node | node | node
    all_goals
      apply Function.hfunext rfl
      intro packet packet' hpacket
      cases hpacket
    case' inl.refl =>
      change Interface.Packet (left.ports node).Out at packet
      rcases hr : left.route node packet with ⟨target, response⟩ | ⟨port, message⟩
      case' inr => rcases port with port | port
    case' inr.inl.refl =>
      change Interface.Packet (context.ports node).Out at packet
      rcases hr : context.route node packet with ⟨target, response⟩ | ⟨port, message⟩
      case' inr => rcases port with port | port
    case' inr.inr.refl =>
      change Interface.Packet (right.ports node).Out at packet
      rcases hr : right.route node packet with ⟨target, response⟩ | ⟨port, message⟩
      case' inr => rcases port with port | port
    all_goals
      simp only [reindex, parContextLeftEquiv_left, parContextLeftEquiv_context,
        parContextLeftEquiv_right]
      simp only [plug_route_left (left.wire right) context,
        plug_route_right (left.wire right) context,
        plug_route_left left (right.wireContextLeft context),
        plug_route_right left (right.wireContextLeft context)]
      simp only [wire_context_route_left right context, wire_context_route_right right context,
        wire_context_ingress_left right context, wire_context_ingress_right right context,
        wire, hr, Sum.map_inl, packet_left, packet_right, packet_context]
      apply routed_packet_heq
      · funext target
        rcases target with target | target | target <;> rfl
      · rfl
  · apply Function.hfunext rfl
    intro packet _ _
    exact packet.1.elim

end Diagram

namespace Network

variable {N₁ N₂ K result : Type} {Δ₁ Δ₂ : PortBoundary}

/-- Factoring parallel closure retains the single designated environment in the context. -/
theorem close_par_left (left : Diagram N₁ Δ₁ result) (right : Diagram N₂ Δ₂ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) :
    (((left.par right).plug context).withEnvironment (.inr environment)).reindex
        (Diagram.parContextLeftEquiv N₁ N₂ K) =
      (left.plug (right.parContextLeft context)).withEnvironment (.inr (.inl environment)) := by
  change (((left.par right).plug context).reindex
      (Diagram.parContextLeftEquiv N₁ N₂ K)).withEnvironment (.inr (.inl environment)) = _
  rw [Diagram.close_par_left]

/-- Wired factorization preserves the single environment selected in the closing context. -/
theorem close_wire_left {Γ : PortBoundary}
    (left : Diagram N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : Diagram N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) :
    (((left.wire right).plug context).withEnvironment (.inr environment)).reindex
        (Diagram.parContextLeftEquiv N₁ N₂ K) =
      (left.plug (right.wireContextLeft context)).withEnvironment (.inr (.inl environment)) := by
  change (((left.wire right).plug context).reindex
      (Diagram.parContextLeftEquiv N₁ N₂ K)).withEnvironment (.inr (.inl environment)) = _
  rw [Diagram.close_wire_left]

end Network

end Interaction.UC.ReactiveNetwork
