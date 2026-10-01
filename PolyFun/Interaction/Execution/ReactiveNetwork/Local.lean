/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveNetwork.Conserving
public import PolyFun.Interaction.Execution.ReactiveProcess.Conserving

/-!
# Network certificates from process certificates

The obligation of a `Conserving` certificate is local to the acting node, but it is stated over
network states. A `ReactiveProcess.ProcessConserving` certificate states it about one process
alone. This file places process certificates at the nodes of a network.

`Charge.ofLocal κ` is the network charge of component charges: a component's charge on its
productive activations, and zero on administrative ones (`Charge.ofLocal_one` identifies unit
component charges with `Charge.productive`). A family of process certificates, at the nodes of a
network whose credit model gives each node the same port credits, is a conserving certificate for
every discipline and every invariant (`ProcessConserving.toConserving`).

Diagram operations keep component machines unchanged, so process certificates are reused
verbatim. The only network-level obligation left is the credit model's `route_le`: wiring must not
create credit.
-/

public section

namespace Interaction.Execution.ReactiveNetwork

open PFunctor ReactiveProcess MonadAttach

attribute [local implicit_reducible] signature Response

variable {Node result S : Type} {boundary : PortBoundary}
  {network : Network Node boundary result} [DecidableEq Node]

/-- The network charge of component charges: a component's charge on its productive activations,
and zero on administrative ones (finished no-ops, blocked receives, deliveries). -/
@[expose] def Charge.ofLocal (κ : (id : Node) → (network.component id).State → ℕ) :
    Charge network S
  | .node id, state => if isProductive id state then κ id (state.localState id) else 0
  | .deliver, _ => 0

omit [DecidableEq Node] in
/-- Unit component charges give the productive unit charge. -/
theorem Charge.ofLocal_one :
    Charge.ofLocal (network := network) (S := S) (fun _ _ => 1) = Charge.productive := by
  funext activation state
  cases activation <;> rfl

variable {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

/-- **Locality.** Process certificates, placed at the nodes of a network whose credit model agrees
with their port credits, form a conserving certificate for every discipline and invariant. -/
@[expose] def _root_.Interaction.Execution.ReactiveProcess.ProcessConserving.toConserving
    {impl : (id : Node) → Handler (StateT S m) (network.effect id)}
    {credit : CreditModel network} {κ : (id : Node) → (network.component id).State → ℕ}
    (certs : ∀ id, ProcessConserving (network.component id) (impl id) (κ id)
      (credit.inbound id) (credit.outbound id))
    (discipline : Discipline) (invariant : State network S → Prop) :
    Conserving impl discipline (Charge.ofLocal κ) credit invariant where
  pot id := (certs id).pot
  step id state next _ _ h := by
    rcases hv : (network.component id).view (state.localState id) with value | ⟨action, cont⟩
    · simp only [activate, hv, canReturn_pure_iff] at h
      subst next
      simp [Charge.ofLocal, isProductive, hv, CreditModel.emitted, CreditModel.consumed]
    · cases action with
      | effect operation =>
        simp only [activate, hv, canReturn_bind_iff, canReturn_pure_iff] at h
        obtain ⟨⟨answer, service'⟩, hans, rfl⟩ := h
        have := (certs id).onEffect _ operation cont _ answer service' hv hans
        simp [Charge.ofLocal, isProductive, hv, CreditModel.emitted, CreditModel.consumed]
        omega
      | receive =>
        cases hq : state.inbox id with
        | nil =>
          simp only [activate, hv, hq, canReturn_pure_iff] at h
          subst next
          simp [Charge.ofLocal, isProductive, hv, hq, CreditModel.emitted, CreditModel.consumed]
        | cons packet rest =>
          simp only [activate, hv, hq, canReturn_pure_iff] at h
          subst next
          have := (certs id).onReceive _ cont packet hv
          simp [Charge.ofLocal, isProductive, hv, hq, CreditModel.emitted, CreditModel.consumed]
          omega
      | send packet =>
        have := (certs id).onSend _ packet cont hv
        have hloc : next.localState id = cont () := by
          cases discipline <;> cases hr : network.route id packet <;>
            simp only [activate, hv, hr, dispatch, canReturn_pure_iff] at h <;> subst next <;>
            simp
        rw [hloc]
        simp [Charge.ofLocal, isProductive, hv, CreditModel.emitted, CreditModel.consumed]
        omega
      | tick =>
        simp only [activate, hv, canReturn_pure_iff] at h
        subst next
        have := (certs id).onTick _ cont hv
        simp [Charge.ofLocal, isProductive, hv, CreditModel.emitted, CreditModel.consumed]
        omega
      | yield =>
        simp only [activate, hv, canReturn_pure_iff] at h
        subst next
        have := (certs id).onYield _ cont hv
        simp [Charge.ofLocal, isProductive, hv, CreditModel.emitted, CreditModel.consumed]
        omega

end Interaction.Execution.ReactiveNetwork
