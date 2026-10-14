/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveNetwork.Charge
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Credit carried by packets

A `CreditModel` attaches natural-number credit to packets:

* `outbound id packet` is what the sender `id` attaches to a packet it sends;
* `inbound id packet` is what a packet in `id`'s mailbox releases when `id` consumes it;
* `exported packet` is what a packet delivered to the external boundary carries out.

Routing never creates credit (`route_le`): a routed packet carries at most what its sender
attached. External input is funded by the caller: `CreditModel.ingress packet` is the inbound
credit of the packet's ingress recipient, and `CreditModel.funded` is the credit an open-execution
event brings in.

`CreditModel.held` is the credit held by packets in mailboxes, in the FIFO queue, and on the
output trace. Its accounting is exact:

* routing a packet adds its destination credit (`held_dispatch`, `held_input`);
* a FIFO delivery moves credit from the queue without changing the total (`held_deliver`);
* an activation changes held credit by at most what the acting node emits minus what it consumes
  (`held_activate`). Both quantities are read from the acting node's local view and mailbox head
  (`emitted`, `consumed`).

Together with `localState_activate_of_ne` (an activation changes only the acting node's local
state), these are the facts about `activate` that conservation arguments use.
-/

public section

namespace Interaction.Execution.ReactiveNetwork

open PFunctor ReactiveProcess MonadAttach

variable {Node result S : Type} {boundary : PortBoundary}
  {network : Network Node boundary result} [DecidableEq Node]

attribute [local implicit_reducible] signature Response

/-- Credit carried by a routed packet: its recipient's inbound credit, or its exported credit. -/
@[expose] def destCredit (inbound : (id : Node) → Interface.Packet (network.ports id).In → ℕ)
    (exported : Interface.Packet boundary.Out → ℕ) : Destination network → ℕ
  | .inl ⟨target, packet⟩ => inbound target packet
  | .inr packet => exported packet

/-- Credit carried by packets. Routing preserves or burns credit, never creates it. -/
structure CreditModel (network : Network Node boundary result) where
  /-- Credit released to `id` when it consumes the packet. -/
  inbound : (id : Node) → Interface.Packet (network.ports id).In → ℕ
  /-- Credit `id` attaches to a packet it sends. -/
  outbound : (id : Node) → Interface.Packet (network.ports id).Out → ℕ
  /-- Credit carried out of the network by an output packet. -/
  exported : Interface.Packet boundary.Out → ℕ
  /-- Routing never creates credit. -/
  route_le : ∀ id packet,
    destCredit (network := network) inbound exported (network.route id packet) ≤ outbound id packet

namespace CreditModel

variable (credit : CreditModel network)

/-- Credit carried by a routed packet. -/
abbrev dest (destination : Destination network) : ℕ :=
  destCredit credit.inbound credit.exported destination

/-- Credit funded by the caller with an external input: its ingress recipient's inbound credit. -/
@[expose] def ingress (packet : Interface.Packet boundary.In) : ℕ :=
  credit.inbound (network.ingress packet).1 (network.ingress packet).2

/-- The credit an open-execution event brings in: an input's ingress credit. -/
@[expose] def funded : TokenEvent boundary → ℕ
  | .input packet => credit.ingress packet
  | .step => 0

/-- Credit held by packets in mailboxes, in the FIFO queue, and on the output trace. -/
@[expose] def held [Fintype Node] (state : State network S) : ℕ :=
  (∑ id, ((state.inbox id).map (credit.inbound id)).sum) +
    (state.pending.map credit.dest).sum + (state.output.map credit.exported).sum

/-- Credit released by activating `id`: the head of its mailbox, if it is ready to receive. -/
@[expose] def consumed (id : Node) (state : State network S) : ℕ :=
  match (network.component id).view (state.localState id) with
  | .inr ⟨.receive, _⟩ =>
    match state.inbox id with
    | [] => 0
    | packet :: _ => credit.inbound id packet
  | _ => 0

/-- Credit attached by activating `id`: the packet it sends, if it is ready to send. -/
@[expose] def emitted (id : Node) (state : State network S) : ℕ :=
  match (network.component id).view (state.localState id) with
  | .inr ⟨.send packet, _⟩ => credit.outbound id packet
  | _ => 0

end CreditModel

/-! ## Sums over one updated coordinate -/

omit [DecidableEq Node] in
/-- Changing a dependent family at one coordinate changes a sum over it by that coordinate. -/
theorem sum_frame [Fintype Node] {β : Node → Type} (F : (i : Node) → β i → ℕ)
    (g g' : (i : Node) → β i) (t : Node) (h : ∀ i, i ≠ t → g' i = g i) :
    (∑ i, F i (g' i)) + F t (g t) = (∑ i, F i (g i)) + F t (g' t) := by
  classical
  rw [← Finset.add_sum_erase _ (fun i => F i (g' i)) (Finset.mem_univ t),
    ← Finset.add_sum_erase _ (fun i => F i (g i)) (Finset.mem_univ t)]
  have hrest : ∑ i ∈ Finset.univ.erase t, F i (g' i) = ∑ i ∈ Finset.univ.erase t, F i (g i) :=
    Finset.sum_congr rfl fun i hi => by rw [h i (Finset.ne_of_mem_erase hi)]
  rw [hrest]
  omega

/-! ## Accounting for held credit -/

namespace CreditModel

variable (credit : CreditModel network) [Fintype Node]

omit [DecidableEq Node] in
/-- Held credit depends only on mailboxes, the FIFO queue, and the output trace. -/
theorem held_congr {state next : State network S} (hinbox : next.inbox = state.inbox)
    (hpending : next.pending = state.pending) (houtput : next.output = state.output) :
    credit.held next = credit.held state := by
  simp only [held, hinbox, hpending, houtput]

/-- Routing a packet adds exactly its destination credit. -/
theorem held_dispatch (destination : Destination network) (state : State network S) :
    credit.held (dispatch destination state) = credit.held state + credit.dest destination := by
  rcases destination with ⟨target, packet⟩ | packet
  · have hframe := sum_frame (fun i (l : List (Interface.Packet (network.ports i).In)) =>
        (l.map (credit.inbound i)).sum) state.inbox
        (Function.update state.inbox target (state.inbox target ++ [packet])) target
        (fun i hi => Function.update_of_ne hi _ _)
    simp only [Function.update_self, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hframe
    simp only [held, dispatch, dest, destCredit]
    omega
  · simp only [held, dispatch, dest, destCredit, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    omega

/-- An external input adds exactly the credit the caller funds. -/
theorem held_input (packet : Interface.Packet boundary.In) (state : State network S) :
    credit.held (input packet state) = credit.held state + credit.ingress packet := by
  rw [input, held_dispatch]
  rfl

/-- A FIFO delivery moves credit from the queue to a mailbox or the output trace. -/
theorem held_deliver (state : State network S) :
    credit.held (deliver state) = credit.held state := by
  cases hp : state.pending with
  | nil => simp [deliver, hp, held]
  | cons destination rest =>
    simp only [deliver, hp]
    rw [held_dispatch]
    simp only [held, hp, List.map_cons, List.sum_cons]
    omega

omit [DecidableEq Node] in
/-- No credit is held initially. -/
theorem held_initial (service : S) : credit.held (initial network service) = 0 := by
  simp [held, initial]

end CreditModel

/-! ## What one activation changes -/

section Activate

variable {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

/-- An activation changes only the acting node's local state. -/
theorem localState_activate_of_ne
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (discipline : Discipline) (id i : Node) (state next : State network S)
    (h : CanReturn (activate impl discipline id state) next) (hi : i ≠ id) :
    next.localState i = state.localState i := by
  rcases hv : (network.component id).view (state.localState id) with value | ⟨action, cont⟩
  · simp only [activate, hv, canReturn_pure_iff] at h
    subst next
    rfl
  · cases action with
    | effect operation =>
      simp only [activate, hv, canReturn_bind_iff, canReturn_pure_iff] at h
      obtain ⟨⟨answer, service⟩, _, rfl⟩ := h
      exact Function.update_of_ne hi _ _
    | receive =>
      cases hq : state.inbox id <;>
        simp only [activate, hv, hq, canReturn_pure_iff] at h <;> subst next
      · rfl
      · exact Function.update_of_ne hi _ _
    | send packet =>
      cases discipline <;> cases hr : network.route id packet <;>
        simp only [activate, hv, hr, dispatch, canReturn_pure_iff] at h <;> subst next <;>
        exact Function.update_of_ne hi _ _
    | tick =>
      simp only [activate, hv, canReturn_pure_iff] at h
      subst next
      exact Function.update_of_ne hi _ _
    | yield =>
      simp only [activate, hv, canReturn_pure_iff] at h
      subst next
      exact Function.update_of_ne hi _ _

/-- Activating a finished node returns control to the environment and changes no local state,
mailbox, queue, or output. -/
theorem activate_of_finished
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (discipline : Discipline) (id : Node) (state next : State network S)
    (value : Outcome result) (hout : outcome id state = some value)
    (h : CanReturn (activate impl discipline id state) next) :
    next.focus = network.environment ∧ next.localState = state.localState ∧
      next.inbox = state.inbox ∧ next.pending = state.pending ∧ next.output = state.output := by
  unfold outcome at hout
  rcases hv : (network.component id).view (state.localState id) with result | ⟨action, cont⟩
  · simp only [activate, hv, canReturn_pure_iff] at h
    subst next
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp [hv] at hout

/-- Held credit changes by at most what the acting node emits minus what it consumes. -/
theorem CreditModel.held_activate [Fintype Node] (credit : CreditModel network)
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (discipline : Discipline) (id : Node) (state next : State network S)
    (h : CanReturn (activate impl discipline id state) next) :
    credit.held next + credit.consumed id state ≤
      credit.held state + credit.emitted id state := by
  rcases hv : (network.component id).view (state.localState id) with value | ⟨action, cont⟩
  · simp only [activate, hv, canReturn_pure_iff] at h
    subst next
    simp only [CreditModel.consumed, CreditModel.emitted, hv]
    simp [CreditModel.held]
  · cases action with
    | effect operation =>
      simp only [activate, hv, canReturn_bind_iff, canReturn_pure_iff] at h
      obtain ⟨⟨answer, service⟩, _, rfl⟩ := h
      simp only [CreditModel.consumed, CreditModel.emitted, hv]
      simp [CreditModel.held]
    | receive =>
      rcases hq : state.inbox id with _ | ⟨packet, rest⟩
      · simp only [activate, hv, hq, canReturn_pure_iff] at h
        subst next
        simp only [CreditModel.consumed, CreditModel.emitted, hv, hq]
        simp [CreditModel.held]
      · simp only [activate, hv, hq, canReturn_pure_iff] at h
        subst next
        have hframe := sum_frame (fun i (l : List (Interface.Packet (network.ports i).In)) =>
            (l.map (credit.inbound i)).sum) state.inbox
            (Function.update state.inbox id rest) id
            (fun i hi => Function.update_of_ne hi _ _)
        simp only [Function.update_self, hq, List.map_cons, List.sum_cons] at hframe
        simp only [CreditModel.consumed, CreditModel.emitted, hv, hq, CreditModel.held]
        omega
    | send packet =>
      have hroute : credit.dest (network.route id packet) ≤ credit.outbound id packet :=
        credit.route_le id packet
      have hemit : credit.emitted id state = credit.outbound id packet := by
        simp only [CreditModel.emitted, hv]
      have hcons : credit.consumed id state = 0 := by
        simp only [CreditModel.consumed, hv]
      rw [hemit, hcons]
      cases discipline
      · simp only [activate, hv, canReturn_pure_iff] at h
        subst next
        rw [credit.held_dispatch]
        simp only [CreditModel.held]
        omega
      · simp only [activate, hv, canReturn_pure_iff] at h
        subst next
        simp only [CreditModel.held, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil, add_zero]
        omega
    | tick =>
      simp only [activate, hv, canReturn_pure_iff] at h
      subst next
      simp only [CreditModel.consumed, CreditModel.emitted, hv]
      simp [CreditModel.held]
    | yield =>
      simp only [activate, hv, canReturn_pure_iff] at h
      subst next
      simp only [CreditModel.consumed, CreditModel.emitted, hv]
      simp [CreditModel.held]

end Activate

end Interaction.Execution.ReactiveNetwork
