/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

-- import all: unfolds `PortBoundary.swap`, `PortBoundary.tensor`, `tensorComm`, `sumCongr`
import all PolyFun.Interaction.Interface
-- import all: opens the private theorems `par_route_left`, `par_route_right`,
--   `par_ingress_left`, `par_ingress_right`, `routed_packet_heq`
import all PolyFun.Interaction.Execution.ReactiveNetwork.Factorization
public import PolyFun.Interaction.Execution.ReactiveNetwork.Factorization

/-!
# Right-component factorization of reactive closure

The explicit component bijection moves the left fragment into the closing context.
The resulting equalities retain all machines and routes and are consumed by the same
complete-state execution transport as the left-component laws.
-/

public section

namespace Interaction.Execution.ReactiveNetwork

open PFunctor ReactiveProcess

namespace Diagram

variable {N₁ N₂ K result : Type} {Δ₁ Δ₂ Γ : PortBoundary}

/-- The component correspondence when the left fragment becomes part of the context. -/
@[expose] def parContextRightEquiv (N₁ N₂ K : Type) : (N₂ ⊕ (K ⊕ N₁)) ≃ ((N₁ ⊕ N₂) ⊕ K) :=
  (parContextLeftEquiv N₂ N₁ K).trans
    (Equiv.sumCongr (Equiv.sumComm N₂ N₁) (Equiv.refl K))

@[simp] theorem parContextRightEquiv_left (node : N₁) :
    parContextRightEquiv N₁ N₂ K (.inr (.inr node)) = .inl (.inl node) := rfl

@[simp] theorem parContextRightEquiv_context (node : K) :
    parContextRightEquiv N₁ N₂ K (.inr (.inl node)) = .inr node := rfl

@[simp] theorem parContextRightEquiv_right (node : N₂) :
    parContextRightEquiv N₁ N₂ K (.inl node) = .inl (.inr node) := rfl

private theorem right_packet_left {β : ((N₁ ⊕ N₂) ⊕ K) → Type}
    (node : N₁) (packet : β (.inl (.inl node))) :
    (Equiv.sigmaCongrLeft (β := β) (parContextRightEquiv N₁ N₂ K)).symm
      ⟨.inl (.inl node), packet⟩ = ⟨.inr (.inr node), packet⟩ :=
  Equiv.symm_apply_apply
    (Equiv.sigmaCongrLeft (β := β) (parContextRightEquiv N₁ N₂ K)) ⟨.inr (.inr node), packet⟩

private theorem right_packet_right {β : ((N₁ ⊕ N₂) ⊕ K) → Type}
    (node : N₂) (packet : β (.inl (.inr node))) :
    (Equiv.sigmaCongrLeft (β := β) (parContextRightEquiv N₁ N₂ K)).symm
      ⟨.inl (.inr node), packet⟩ = ⟨.inl node, packet⟩ :=
  Equiv.symm_apply_apply
    (Equiv.sigmaCongrLeft (β := β) (parContextRightEquiv N₁ N₂ K)) ⟨.inl node, packet⟩

private theorem right_packet_context {β : ((N₁ ⊕ N₂) ⊕ K) → Type}
    (node : K) (packet : β (.inr node)) :
    (Equiv.sigmaCongrLeft (β := β) (parContextRightEquiv N₁ N₂ K)).symm
      ⟨.inr node, packet⟩ = ⟨.inr (.inl node), packet⟩ :=
  Equiv.symm_apply_apply
    (Equiv.sigmaCongrLeft (β := β) (parContextRightEquiv N₁ N₂ K)) ⟨.inr (.inl node), packet⟩

/-- Move the left parallel component into the context and expose the right boundary. -/
@[expose] def parContextRight (left : Diagram N₁ Δ₁ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    Diagram (K ⊕ N₁) (PortBoundary.swap Δ₂) result :=
  left.parContextLeft (context.map
    (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)).toHom)

private theorem right_context_route_context (left : Diagram N₁ Δ₁ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (node : K) (packet : Interface.Packet (context.ports node).Out) :
    (left.parContextRight context).route (.inl node) packet =
      match context.route node packet with
      | .inl ⟨target, response⟩ => .inl ⟨.inl target, response⟩
      | .inr ⟨.inl port, message⟩ =>
          .inl ⟨.inr (left.ingress ⟨port, message⟩).1, (left.ingress ⟨port, message⟩).2⟩
      | .inr ⟨.inr port, message⟩ => .inr ⟨port, message⟩ := by
  rcases hr : context.route node packet with ⟨target, response⟩ | ⟨port, message⟩
  · simp only [parContextRight, parContextLeft, map, wire, hr, Sum.map_inl]
    rfl
  · rcases port with port | port <;>
      simp only [parContextRight, parContextLeft, map, wire, hr] <;> rfl

private theorem right_context_route_component (left : Diagram N₁ Δ₁ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (node : N₁) (packet : Interface.Packet (left.ports node).Out) :
    (left.parContextRight context).route (.inr node) packet =
      match left.route node packet with
      | .inl ⟨target, response⟩ => .inl ⟨.inr target, response⟩
      | .inr ⟨port, message⟩ =>
          .inl ⟨.inl (context.ingress ⟨.inl port, message⟩).1,
            (context.ingress ⟨.inl port, message⟩).2⟩ := by
  rcases hr : left.route node packet with ⟨target, response⟩ | ⟨port, message⟩
  all_goals simp only [parContextRight, parContextLeft, map, wire, hr, Sum.map_inl]
  all_goals rfl

private theorem right_context_ingress (left : Diagram N₁ Δ₁ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (port : Δ₂.Out.A) (message : Δ₂.Out.B port) :
    (left.parContextRight context).ingress ⟨port, message⟩ =
      ⟨.inl (context.ingress ⟨.inr port, message⟩).1,
        (context.ingress ⟨.inr port, message⟩).2⟩ := rfl

attribute [local implicit_reducible] plug map wire par reindex parContextLeft parContextRight
  parContextRightEquiv

/-- Parallel closure factors through its right component under the explicit identity map. -/
theorem close_par_right (left : Diagram N₁ Δ₁ result) (right : Diagram N₂ Δ₂ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    ((left.par right).plug context).reindex (parContextRightEquiv N₁ N₂ K) =
      right.plug (left.parContextRight context) := by
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
      change Interface.Packet (right.ports node).Out at packet
      rcases hr : right.route node packet with ⟨target, response⟩ | ⟨port, message⟩
    case' inr.inl.refl =>
      change Interface.Packet (context.ports node).Out at packet
      rcases hr : context.route node packet with ⟨target, response⟩ | ⟨port, message⟩
      case' inr => rcases port with port | port
    case' inr.inr.refl =>
      change Interface.Packet (left.ports node).Out at packet
      rcases hr : left.route node packet with ⟨target, response⟩ | ⟨port, message⟩
    all_goals
      simp only [reindex, parContextRightEquiv_left, parContextRightEquiv_context,
        parContextRightEquiv_right]
      simp only [plug_route_left (left.par right) context,
        plug_route_right (left.par right) context,
        plug_route_left right (left.parContextRight context),
        plug_route_right right (left.parContextRight context),
        par_route_left left right, par_route_right left right,
        right_context_route_context left context, right_context_route_component left context,
        hr, Sum.map_inl, right_context_ingress left context,
        par_ingress_left left right, par_ingress_right left right,
        right_packet_left, right_packet_right, right_packet_context]
      apply routed_packet_heq
      · funext target
        rcases target with target | target | target <;> rfl
      · rfl
  · apply Function.hfunext rfl
    intro packet _ _
    exact packet.1.elim

/-- Move the left wired component into the context, exposing the right component's boundary. -/
@[expose] def wireContextRight (left : Diagram N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    Diagram (K ⊕ N₁) (PortBoundary.swap (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) result :=
  ((context.map
      (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)).toHom).wire
    (Δ₁ := PortBoundary.swap Δ₂) (Γ := PortBoundary.swap Δ₁) (Δ₂ := Γ) left).map
      (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₂) Γ).toHom

private theorem right_wire_context_route_context
    (left : Diagram N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (node : K) (packet : Interface.Packet (context.ports node).Out) :
    (left.wireContextRight context).route (.inl node) packet =
      match context.route node packet with
      | .inl ⟨target, response⟩ => .inl ⟨.inl target, response⟩
      | .inr ⟨.inl port, message⟩ =>
          .inl ⟨.inr (left.ingress ⟨.inl port, message⟩).1,
            (left.ingress ⟨.inl port, message⟩).2⟩
      | .inr ⟨.inr port, message⟩ => .inr ⟨.inr port, message⟩ := by
  rcases hr : context.route node packet with ⟨target, response⟩ | ⟨port, message⟩
  · simp only [wireContextRight, map, wire, hr, Sum.map_inl]
    rfl
  · rcases port with port | port <;> simp only [wireContextRight, map, wire, hr] <;> rfl

private theorem right_wire_context_route_component
    (left : Diagram N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (node : N₁) (packet : Interface.Packet (left.ports node).Out) :
    (left.wireContextRight context).route (.inr node) packet =
      match left.route node packet with
      | .inl ⟨target, response⟩ => .inl ⟨.inr target, response⟩
      | .inr ⟨.inl port, message⟩ =>
          .inl ⟨.inl (context.ingress ⟨.inl port, message⟩).1,
            (context.ingress ⟨.inl port, message⟩).2⟩
      | .inr ⟨.inr port, message⟩ => .inr ⟨.inl port, message⟩ := by
  rcases hr : left.route node packet with ⟨target, response⟩ | ⟨port, message⟩
  · simp only [wireContextRight, map, wire, hr, Sum.map_inl]
    rfl
  · rcases port with port | port <;> simp only [wireContextRight, map, wire, hr] <;> rfl

private theorem right_wire_context_ingress_left
    (left : Diagram N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (port : Γ.In.A) (message : Γ.In.B port) :
    (left.wireContextRight context).ingress ⟨.inl port, message⟩ =
      ⟨.inr (left.ingress ⟨.inr port, message⟩).1,
        (left.ingress ⟨.inr port, message⟩).2⟩ := rfl

private theorem right_wire_context_ingress_right
    (left : Diagram N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (port : Δ₂.Out.A) (message : Δ₂.Out.B port) :
    (left.wireContextRight context).ingress ⟨.inr port, message⟩ =
      ⟨.inl (context.ingress ⟨.inr port, message⟩).1,
        (context.ingress ⟨.inr port, message⟩).2⟩ := rfl

attribute [local implicit_reducible] wireContextRight

/-- Wired closure factors through its right component, preserving shared-boundary traffic. -/
theorem close_wire_right
    (left : Diagram N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : Diagram N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result) :
    ((left.wire right).plug context).reindex (parContextRightEquiv N₁ N₂ K) =
      right.plug (left.wireContextRight context) := by
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
      change Interface.Packet (right.ports node).Out at packet
      rcases hr : right.route node packet with ⟨target, response⟩ | ⟨port, message⟩
      case' inr => rcases port with port | port
    case' inr.inl.refl =>
      change Interface.Packet (context.ports node).Out at packet
      rcases hr : context.route node packet with ⟨target, response⟩ | ⟨port, message⟩
      case' inr => rcases port with port | port
    case' inr.inr.refl =>
      change Interface.Packet (left.ports node).Out at packet
      rcases hr : left.route node packet with ⟨target, response⟩ | ⟨port, message⟩
      case' inr => rcases port with port | port
    all_goals
      simp only [reindex, parContextRightEquiv_left, parContextRightEquiv_context,
        parContextRightEquiv_right]
      simp only [plug_route_left (left.wire right) context,
        plug_route_right (left.wire right) context,
        plug_route_left right (left.wireContextRight context),
        plug_route_right right (left.wireContextRight context)]
      simp only [right_wire_context_route_context left context,
        right_wire_context_route_component left context,
        right_wire_context_ingress_left left context, right_wire_context_ingress_right left context,
        wire, hr, Sum.map_inl, right_packet_left, right_packet_right, right_packet_context]
      apply routed_packet_heq
      · funext target
        rcases target with target | target | target <;> rfl
      · rfl
  · apply Function.hfunext rfl
    intro packet _ _
    exact packet.1.elim

end Diagram

namespace Network

variable {N₁ N₂ K result : Type} {Δ₁ Δ₂ Γ : PortBoundary}

/-- Right parallel factorization retains the context's single designated environment. -/
theorem close_par_right (left : Diagram N₁ Δ₁ result) (right : Diagram N₂ Δ₂ result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) :
    (((left.par right).plug context).withEnvironment (.inr environment)).reindex
        (Diagram.parContextRightEquiv N₁ N₂ K) =
      (right.plug (left.parContextRight context)).withEnvironment (.inr (.inl environment)) := by
  change (((left.par right).plug context).reindex
      (Diagram.parContextRightEquiv N₁ N₂ K)).withEnvironment (.inr (.inl environment)) = _
  rw [Diagram.close_par_right]

/-- Right wired factorization retains the context's single designated environment. -/
theorem close_wire_right (left : Diagram N₁ (PortBoundary.tensor Δ₁ Γ) result)
    (right : Diagram N₂ (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) result)
    (context : Diagram K (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)) result)
    (environment : K) :
    (((left.wire right).plug context).withEnvironment (.inr environment)).reindex
        (Diagram.parContextRightEquiv N₁ N₂ K) =
      (right.plug (left.wireContextRight context)).withEnvironment (.inr (.inl environment)) := by
  change (((left.wire right).plug context).reindex
      (Diagram.parContextRightEquiv N₁ N₂ K)).withEnvironment (.inr (.inl environment)) = _
  rw [Diagram.close_wire_right]

end Network

end Interaction.Execution.ReactiveNetwork
