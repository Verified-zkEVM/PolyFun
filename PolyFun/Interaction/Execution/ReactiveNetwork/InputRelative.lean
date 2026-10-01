/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveNetwork.Conserving
public import Mathlib.Tactic.Ring

/-!
# Input-relative certificates compose only through an exchange rate

An `InputRelative` certificate pays a node's charge out of its potential and the credit it
consumes, with no obligation for what it emits:

  `pot id next + charge ≤ pot id before + consumed`.

This is the amortization behind input-relative runtime notions (`HUM13`). Such certificates do not
compose across feedback: two nodes, each certified, can exchange packets forever. They do compose
under a *gain* law, and the gain law is conservation in a re-denominated currency:

* give each node an exchange rate `w id`;
* value a packet for node `t` at `w t` times its credit (`CreditModel.reweight`);
* scale each potential by its node's rate.

If at every send the weighted credit of the routed packet plus the step's charge is at most `w id`
times the charge (`SmallGain`), the scaled certificate is conserving (`InputRelative.toConserving`).
Every conservation bound then applies (`work_le_initial_of_smallGain`).

* Uniform rates `2` cover emissions that credit their recipient at most half the sender's charge:
  work is then at most twice the initial potentials (`smallGain_two`).
* Take an acyclic network whose sends go to strictly lower levels and emit at most `g` times their
  charge. There the rates `(g + 1) ^ level` satisfy the law (`Acyclic.smallGain`), so work is
  bounded by potentials weighted by `(g + 1) ^ depth`.
-/

public section

namespace Interaction.Execution.ReactiveNetwork

open PFunctor ReactiveProcess MonadAttach

variable {Node result S : Type} {boundary : PortBoundary}
  {network : Network Node boundary result} [DecidableEq Node]
  {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

attribute [local implicit_reducible] signature Response

/-- **An input-relative certificate.** Each node's charge is paid by its potential and the credit
it consumes; what it emits is unconstrained. -/
structure InputRelative (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (discipline : Discipline) (charge : Charge network S) (credit : CreditModel network)
    (invariant : State network S → Prop) where
  /-- Each node's potential on its own local states. -/
  pot : (id : Node) → (network.component id).State → ℕ
  /-- The local obligation at every activation the discipline can perform. -/
  step : ∀ id state next, invariant state → Schedulable discipline id state →
    CanReturn (activate impl discipline id state) next →
      pot id (next.localState id) + charge (.node id) state ≤
        pot id (state.localState id) + credit.consumed id state

/-- Conservation is the stronger local notion: dropping the emission term leaves an input-relative
certificate. -/
@[expose] def Conserving.toInputRelative
    {impl : (id : Node) → Handler (StateT S m) (network.effect id)} {discipline : Discipline}
    {charge : Charge network S} {credit : CreditModel network}
    {invariant : State network S → Prop}
    (c : Conserving impl discipline charge credit invariant) :
    InputRelative impl discipline charge credit invariant where
  pot := c.pot
  step id state next hinv hsched h := by
    have := c.step id state next hinv hsched h
    omega

/-! ## Exchange rates -/

/-- The credit of a routed packet in its recipient's currency; exports are dropped. -/
@[expose] def weightedDest (credit : CreditModel network) (w : Node → ℕ) :
    Destination network → ℕ
  | .inl ⟨target, packet⟩ => w target * credit.inbound target packet
  | .inr _ => 0

/-- Re-denominate credit with node exchange rates. A sent packet is valued at its routed
destination, so routing preserves credit exactly. -/
@[expose] def CreditModel.reweight (credit : CreditModel network) (w : Node → ℕ) :
    CreditModel network where
  inbound id packet := w id * credit.inbound id packet
  outbound id packet := weightedDest credit w (network.route id packet)
  exported _ := 0
  route_le id packet := by
    rcases network.route id packet with ⟨target, q⟩ | q <;> simp [destCredit, weightedDest]

omit [DecidableEq Node] in
/-- Re-denominated credit releases the consumed credit at the receiver's rate. -/
theorem CreditModel.consumed_reweight (credit : CreditModel network) (w : Node → ℕ) (id : Node)
    (state : State network S) :
    (credit.reweight w).consumed id state = w id * credit.consumed id state := by
  unfold CreditModel.consumed
  rcases (network.component id).view (state.localState id) with value | ⟨action, cont⟩
  · simp
  · cases action with
    | receive =>
      cases state.inbox id with
      | nil => simp
      | cons packet rest => rfl
    | _ => simp

/-- **The gain law** with exchange rates `w`: every rate is at least one, and at every send the
recipient-valued credit of the routed packet plus the step's charge is at most `w id` times the
charge. -/
@[expose] def SmallGain (discipline : Discipline) (charge : Charge network S)
    (credit : CreditModel network) (invariant : State network S → Prop) (w : Node → ℕ) : Prop :=
  (∀ id, 1 ≤ w id) ∧
    ∀ id (state : State network S) packet
      (cont : Unit → (network.component id).State), invariant state →
      Schedulable discipline id state →
      (network.component id).view (state.localState id) = .inr ⟨.send packet, cont⟩ →
        weightedDest credit w (network.route id packet) + charge (.node id) state ≤
          w id * charge (.node id) state

/-- **Small gain is conservation in a re-denominated currency.** -/
@[expose] def InputRelative.toConserving
    {impl : (id : Node) → Handler (StateT S m) (network.effect id)} {discipline : Discipline}
    {charge : Charge network S} {credit : CreditModel network}
    {invariant : State network S → Prop}
    (r : InputRelative impl discipline charge credit invariant) (w : Node → ℕ)
    (hgain : SmallGain discipline charge credit invariant w) :
    Conserving impl discipline charge (credit.reweight w) invariant where
  pot id s := w id * r.pot id s
  step id state next hinv hsched h := by
    have hir := r.step id state next hinv hsched h
    have hmul := Nat.mul_le_mul_left (w id) hir
    rw [Nat.mul_add, Nat.mul_add] at hmul
    rw [CreditModel.consumed_reweight]
    have hw : charge (.node id) state ≤ w id * charge (.node id) state :=
      Nat.le_mul_of_pos_left _ (hgain.1 id)
    rcases hv : (network.component id).view (state.localState id) with value | ⟨action, cont⟩
    · have he : (credit.reweight w).emitted id state = 0 := by
        simp only [CreditModel.emitted, hv]
      omega
    · cases action with
      | send packet =>
        have he : (credit.reweight w).emitted id state =
            weightedDest credit w (network.route id packet) := by
          simp only [CreditModel.emitted, hv]
          rfl
        have hg := hgain.2 id state packet cont hinv hsched hv
        omega
      | effect operation =>
        have he : (credit.reweight w).emitted id state = 0 := by
          simp only [CreditModel.emitted, hv]
        omega
      | receive =>
        have he : (credit.reweight w).emitted id state = 0 := by
          simp only [CreditModel.emitted, hv]
        omega
      | tick =>
        have he : (credit.reweight w).emitted id state = 0 := by
          simp only [CreditModel.emitted, hv]
        omega
      | yield =>
        have he : (credit.reweight w).emitted id state = 0 := by
          simp only [CreditModel.emitted, hv]
        omega

/-- **Small-gain soundness.** Along any open token execution from the initial state, work is at
most the rate-weighted initial potentials plus the rate-weighted ingress credit. -/
theorem InputRelative.work_le_initial_of_smallGain [Fintype Node]
    {impl : (id : Node) → Handler (StateT S m) (network.effect id)}
    {charge : Charge network S} {credit : CreditModel network}
    {invariant : State network S → Prop}
    (r : InputRelative impl .token charge credit invariant) (w : Node → ℕ)
    (hgain : SmallGain .token charge credit invariant w)
    (preserves : TokenInvariant impl invariant)
    (preserves_input : ∀ packet state, invariant state → invariant (input packet state))
    {service : S} (hinit : invariant (initial network service))
    {events : List (TokenEvent boundary)} {next : State network S} {work : ℕ}
    (h : CanReturn (runTokenOpen impl charge events (initial network service)) (next, work)) :
    work ≤ (∑ id, w id * r.pot id ((network.component id).init ())) +
      (events.map (credit.reweight w).funded).sum :=
  (r.toConserving w hgain).work_le_initial preserves preserves_input hinit h

omit [DecidableEq Node] in
/-- Uniform rates `2` satisfy the gain law when each emission credits its recipient at most half
the sender's charge. -/
theorem smallGain_two {discipline : Discipline} {charge : Charge network S}
    {credit : CreditModel network} {invariant : State network S → Prop}
    (half : ∀ id (state : State network S) packet
      (cont : Unit → (network.component id).State), invariant state →
      Schedulable discipline id state →
      (network.component id).view (state.localState id) = .inr ⟨.send packet, cont⟩ →
        2 * destCredit credit.inbound (fun _ => 0) (network.route id packet) ≤
          charge (.node id) state) :
    SmallGain discipline charge credit invariant (fun _ => 2) := by
  refine ⟨fun _ => Nat.le_succ 1, fun id state packet cont hinv hsched hv => ?_⟩
  have := half id state packet cont hinv hsched hv
  rcases hr : network.route id packet with ⟨target, q⟩ | q
  · rw [hr] at this
    simp only [destCredit] at this
    simp only [weightedDest]
    omega
  · simp only [weightedDest]
    omega

/-! ## Acyclic networks -/

/-- Sends go to strictly lower levels, or out of the network, and each internal emission is at most
`g` times the sending step's charge. -/
@[expose] def Acyclic (discipline : Discipline) (charge : Charge network S)
    (credit : CreditModel network) (invariant : State network S → Prop) (level : Node → ℕ)
    (g : ℕ) : Prop :=
  ∀ id (state : State network S) packet (cont : Unit → (network.component id).State),
    invariant state → Schedulable discipline id state →
    (network.component id).view (state.localState id) = .inr ⟨.send packet, cont⟩ →
      ∀ target q, network.route id packet = .inl ⟨target, q⟩ →
        level target < level id ∧ credit.inbound target q ≤ g * charge (.node id) state

private theorem pow_level_gain (g a b c q : ℕ) (hlt : a < b) (hq : q ≤ g * c) :
    (g + 1) ^ a * q + c ≤ (g + 1) ^ b * c := by
  have hpow : (g + 1) ^ (a + 1) ≤ (g + 1) ^ b := Nat.pow_le_pow_right (by omega) hlt
  have hone : 1 ≤ (g + 1) ^ a := Nat.one_le_pow _ _ (by omega)
  have h1 : (g + 1) ^ a * q ≤ (g + 1) ^ a * (g * c) := Nat.mul_le_mul_left _ hq
  have h2 : (g + 1) ^ a * (g * c) + c ≤ (g + 1) ^ (a + 1) * c := by
    rw [pow_succ]
    have : c ≤ (g + 1) ^ a * c := Nat.le_mul_of_pos_left _ hone
    calc (g + 1) ^ a * (g * c) + c ≤ (g + 1) ^ a * (g * c) + (g + 1) ^ a * c := by omega
      _ = (g + 1) ^ a * (g + 1) * c := by ring
  have h3 : (g + 1) ^ (a + 1) * c ≤ (g + 1) ^ b * c := Nat.mul_le_mul_right _ hpow
  omega

omit [DecidableEq Node] in
/-- **Acyclic composition.** The rates `(g + 1) ^ level` satisfy the gain law. -/
theorem Acyclic.smallGain {discipline : Discipline} {charge : Charge network S}
    {credit : CreditModel network} {invariant : State network S → Prop}
    {level : Node → ℕ} {g : ℕ} (hacyclic : Acyclic discipline charge credit invariant level g) :
    SmallGain discipline charge credit invariant (fun id => (g + 1) ^ level id) := by
  refine ⟨fun _ => Nat.one_le_pow _ _ (by omega), fun id state packet cont hinv hsched hv => ?_⟩
  rcases hr : network.route id packet with ⟨target, q⟩ | q
  · obtain ⟨hlt, hq⟩ := hacyclic id state packet cont hinv hsched hv target q hr
    simp only [weightedDest]
    exact pow_level_gain g _ _ _ _ hlt hq
  · simp only [weightedDest, zero_add]
    exact Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by omega))

end Interaction.Execution.ReactiveNetwork
