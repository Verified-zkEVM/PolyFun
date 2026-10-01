/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Interaction.Execution.ReactiveBudget
public import PolyFun.Interaction.Execution.ReactiveNetwork.Conserving

/-!
# Conservation certificates on reactive networks

* **Countdown.** The counter is a conserving potential under both disciplines.
  `toTokenBudgetOfFocusReady` recovers the countdown's activation budget, with the counter as
  rank, and FIFO work is bounded by the counter for every schedule.
* **Echo countdown.** This is a feedback loop that terminates. Packets carry credit that decreases
  around the cycle, so the productive work of every token prefix is at most `4 N`, and the counter
  finishes within `4 N` activations.
* **Ping-pong.** The network admits no conserving certificate, for any charge positive at the
  focus, any credit model, and any invariant containing the initial state. This follows directly
  from the soundness bound against the lower bound on work, and again through the derived token
  budget.
* **Unit charges.** They recover the activation count retained by `elapsed`. Because conservation
  forces administrative activations to be free, they are not certifiable once a finished node
  can be activated.
-/

public section

namespace Interaction.Execution.ReactiveNetwork.ConservationTests

open PFunctor ReactiveProcess DynSystem MonadAttach BudgetTests

attribute [local implicit_reducible] countdown countdownStep noEffect signature Response feedback
  loopStep loopPorts unitPort

/-! ## Countdown -/

/-- A network without traffic carries no credit. -/
def countdownCredit (n : ℕ) : CreditModel (countdown n) where
  inbound _ _ := 0
  outbound _ _ := 0
  exported _ := 0
  route_le _ packet := packet.1.elim

/-- The counter is the potential: every tick costs one unit and lowers it by one. -/
def countdownConserving (n : ℕ) (discipline : Discipline) :
    Conserving (countdownImpl n) discipline Charge.productive (countdownCredit n)
      (fun _ => True) where
  pot _ s := (s : ℕ)
  step id state next _ _ h := by
    have heq := Id.canReturn_iff.mp h
    subst heq
    cases id
    cases hs : (state.localState () : ℕ) with
    | zero =>
      simp [activate, countdown, DynComputation.view_ofStep, hs, countdownStep, Charge.productive,
        isProductive, CreditModel.emitted, CreditModel.consumed]
    | succ k =>
      simp [activate, countdown, DynComputation.view_ofStep, hs, countdownStep, Charge.productive,
        isProductive, CreditModel.emitted, CreditModel.consumed]

/-- An unfinished countdown is charged at its focus. -/
theorem countdown_positive (n : ℕ) (state : State (countdown n) Unit)
    (hout : outcome state.focus state = none) :
    1 ≤ (Charge.productive (network := countdown n) (S := Unit)) (.node state.focus) state := by
  cases state.focus
  cases hs : (state.localState () : ℕ) with
  | zero =>
    simp [outcome, countdown, DynComputation.view_ofStep, hs, countdownStep] at hout
  | succ k =>
    simp [Charge.productive, isProductive, countdown, DynComputation.view_ofStep, hs,
      countdownStep]

/-- The token budget derived from the conserving certificate. -/
def countdownConservingBudget (n : ℕ) :
    TokenBudgetCertificate (countdownImpl n) (fun _ => True) :=
  (countdownConserving n .token).toTokenBudgetOfFocusReady (fun _ _ _ _ => trivial)
    (fun state _ hout => countdown_positive n state hout)
    (fun _ _ hne => absurd rfl hne)
    (fun _ _ => ⟨_, Id.canReturn_iff.mpr rfl⟩)

/-- Without traffic no credit is ever held: packets of the empty interface do not exist. -/
theorem countdown_held (n : ℕ) (state : State (countdown n) Unit) :
    (countdownCredit n).held state = 0 := by
  have hinbox : state.inbox () = [] := by
    cases h : state.inbox () with
    | nil => rfl
    | cons packet _ => exact packet.1.elim
  have hpending : state.pending = [] := by
    cases h : state.pending with
    | nil => rfl
    | cons destination _ => rcases destination with ⟨_, packet⟩ | packet <;> exact packet.1.elim
  have houtput : state.output = [] := by
    cases h : state.output with
    | nil => rfl
    | cons packet _ => exact packet.1.elim
  simp [CreditModel.held, hinbox, hpending, houtput]

/-- The derived budget's rank is the counter, the countdown's own rank. -/
theorem countdownConservingBudget_rank (n : ℕ) (state : State (countdown n) Unit) :
    (countdownConservingBudget n).rank state = state.localState () := by
  change (countdownConserving n .token).total state = _
  rw [Conserving.total, countdown_held]
  simp [countdownConserving]

/-- The countdown's completion, from the conserving certificate. -/
example (n : ℕ) :
    ∃ value, outcome () (runToken (m := Id) (countdownImpl n) n
      (initial (countdown n) ())).run = some value :=
  (countdownConservingBudget n).runToken_terminal n _ _ trivial
    (by rw [countdownConservingBudget_rank]; exact le_refl _) (Id.canReturn_iff.mpr rfl)

/-- FIFO execution of the countdown does at most `n` units of productive work, whatever the
schedule. -/
example (n : ℕ) (schedule : List (Activation Unit)) :
    (runFIFOCharged (m := Id) (countdownImpl n) Charge.productive schedule
      (initial (countdown n) ())).run.2 ≤ n := by
  obtain ⟨⟨next, work⟩, h⟩ : ∃ r, CanReturn (runFIFOCharged (m := Id) (countdownImpl n)
      Charge.productive schedule (initial (countdown n) ())) r :=
    ⟨_, Id.canReturn_iff.mpr rfl⟩
  rw [Id.canReturn_iff.mp h]
  have := (countdownConserving n .fifo).work_runFIFO_le (fun _ _ _ _ _ => trivial) 0
    (fun _ _ => le_rfl) trivial h
  rw [Conserving.total_initial] at this
  simp [countdownConserving, countdown] at this
  omega

/-- The unit charge cannot be certified: a finished countdown can still be activated. -/
example : IsEmpty (Conserving (countdownImpl 0) .token Charge.one (countdownCredit 0)
    (fun _ => True)) :=
  isEmpty_conserving_one_of_finished (state := initial (countdown 0) ()) (id := ())
    (value := .returned ()) trivial rfl
    (by simp [outcome, countdown, initial, DynComputation.view_ofStep, countdownStep])

/-! ## Echo countdown: a terminating feedback loop -/

/-- Ports carrying one natural number. -/
@[expose] def natPort : Interface := ⟨Unit, fun _ => ℕ⟩

/-- A boundary with one natural-number port in each direction. -/
@[expose] def natPorts : PortBoundary := ⟨natPort, natPort⟩

/-- Waiting for a packet, or holding a counter value. -/
inductive Phase where
  /-- Waiting for a packet. -/
  | wait
  /-- Holding a counter value. -/
  | hold (k : ℕ)

/-- The counter: stop at zero, otherwise send the predecessor and wait for its echo. -/
@[expose] def counterStep : Phase → Outcome Unit ⊕ (signature noEffect natPorts).Obj Phase
  | .wait => .inr ⟨.receive, fun packet => .hold packet.2⟩
  | .hold 0 => .inl (.returned ())
  | .hold (k + 1) => .inr ⟨.send ⟨(), k⟩, fun _ => .wait⟩

/-- The echo: return every value it receives. -/
@[expose] def echoStep : Phase → Outcome Unit ⊕ (signature noEffect natPorts).Obj Phase
  | .wait => .inr ⟨.receive, fun packet => .hold packet.2⟩
  | .hold k => .inr ⟨.send ⟨(), k⟩, fun _ => .wait⟩

/-- Node `false` counts and node `true` echoes. Both share the state type `Phase`. -/
@[expose] def phaseStep : Bool → Phase → Outcome Unit ⊕ (signature noEffect natPorts).Obj Phase
  | false => counterStep
  | true => echoStep

/-- The counter starts holding `N`; the echo waits. -/
@[expose] def phaseInit (N : ℕ) : Bool → Phase
  | false => .hold N
  | true => .wait

/-- The counter (`false`) is the environment. -/
@[expose] def echo (N : ℕ) : Network Bool PortBoundary.empty Unit where
  effect _ := noEffect
  ports _ := natPorts
  component node := DynComputation.ofStep (phaseStep node) (fun _ => phaseInit N node)
  route node packet := .inl ⟨!node, packet⟩
  ingress packet := packet.1.elim
  environment := false

/-- The echo network has no effect operations to interpret. -/
def echoImpl (N : ℕ) : (node : Bool) → Handler (StateT Unit Id) ((echo N).effect node) :=
  fun _ operation => operation.elim

attribute [local implicit_reducible] natPort natPorts echo counterStep echoStep phaseStep
  phaseInit

/-- The counter value carried by a packet. -/
@[expose] def payload (packet : Interface.Packet natPort) : ℕ := packet.2

/-- Credit carried by packets: `4 k + 3` on the way to the echo, `4 k + 1` on the way back. -/
def echoCredit (N : ℕ) : CreditModel (echo N) where
  inbound
    | false => fun packet => 4 * payload packet + 1
    | true => fun packet => 4 * payload packet + 3
  outbound
    | false => fun packet => 4 * payload packet + 3
    | true => fun packet => 4 * payload packet + 1
  exported _ := 0
  route_le id _ := by cases id <;> exact le_refl _

/-- The potential: `4 k` while the counter holds `k`, and `4 k + 2` while the echo holds `k`. -/
@[expose] def echoPot : Bool → Phase → ℕ
  | _, .wait => 0
  | false, .hold k => 4 * k
  | true, .hold k => 4 * k + 2

theorem echo_activate_blocked (N : ℕ) (id : Bool) (state : State (echo N) Unit)
    (hs : state.localState id = Phase.wait) (hq : state.inbox id = []) :
    (activate (echoImpl N) .token id state).run = { state with elapsed := state.elapsed + 1 } := by
  cases id <;>
    simp [activate, echo, DynComputation.view_ofStep, phaseStep, counterStep, echoStep, hs, hq]

theorem echo_activate_receive (N : ℕ) (id : Bool) (state : State (echo N) Unit)
    (hs : state.localState id = Phase.wait) (packet : Interface.Packet natPort)
    (rest : List (Interface.Packet natPort)) (hq : state.inbox id = packet :: rest) :
    (activate (echoImpl N) .token id state).run =
      { state with
        elapsed := state.elapsed + 1
        localState := Function.update state.localState id (Phase.hold (payload packet))
        inbox := Function.update state.inbox id rest } := by
  cases id <;>
    simp [activate, echo, DynComputation.view_ofStep, phaseStep, counterStep, echoStep, hs, hq,
      payload]

theorem echo_activate_send (N : ℕ) (id : Bool) (state : State (echo N) Unit) (j : ℕ)
    (hv : phaseStep id (state.localState id) = .inr ⟨.send ⟨(), j⟩, fun _ => Phase.wait⟩) :
    (activate (echoImpl N) .token id state).run =
      { state with
        elapsed := state.elapsed + 1
        localState := Function.update state.localState id Phase.wait
        inbox := Function.update state.inbox (!id) (state.inbox (!id) ++ [⟨(), j⟩])
        focus := !id } := by
  simp [activate, echo, DynComputation.view_ofStep, hv, dispatch]

theorem echo_activate_finished (N : ℕ) (state : State (echo N) Unit)
    (hs : state.localState false = Phase.hold 0) :
    (activate (echoImpl N) .token false state).run =
      { state with elapsed := state.elapsed + 1, focus := false } := by
  simp [activate, echo, DynComputation.view_ofStep, phaseStep, counterStep, hs]

/-- The network certificate, for any invariant. -/
def echoConserving (N : ℕ) (invariant : State (echo N) Unit → Prop) :
    Conserving (echoImpl N) .token Charge.productive (echoCredit N) invariant where
  pot id s := echoPot id s
  step id state next _ hsched h := by
    have heq := Id.canReturn_iff.mp h
    subst heq
    rcases hloc : (state.localState id : Phase) with _ | k
    · cases hq : state.inbox id with
      | nil =>
        rw [echo_activate_blocked N id state hloc hq]
        cases id <;>
          simp [echoPot, hloc, hq, Charge.productive, isProductive, CreditModel.emitted,
            CreditModel.consumed, echo, DynComputation.view_ofStep, phaseStep, counterStep,
            echoStep]
      | cons packet rest =>
        rw [echo_activate_receive N id state hloc packet rest hq]
        cases id <;>
          simp [echoPot, hloc, hq, Charge.productive, isProductive, CreditModel.emitted,
            CreditModel.consumed, echo, DynComputation.view_ofStep, phaseStep, counterStep,
            echoStep, echoCredit, payload]
    · cases id with
      | false =>
        cases k with
        | zero =>
          rw [echo_activate_finished N state hloc]
          simp [echoPot, hloc, Charge.productive, isProductive, CreditModel.emitted,
            CreditModel.consumed, echo, DynComputation.view_ofStep, phaseStep, counterStep]
        | succ k =>
          rw [echo_activate_send N false state k (by simp [phaseStep, counterStep, hloc])]
          simp [echoPot, hloc, Charge.productive, isProductive, CreditModel.emitted,
            CreditModel.consumed, echo, DynComputation.view_ofStep, phaseStep, counterStep,
            echoCredit, payload]
          omega
      | true =>
        rw [echo_activate_send N true state k (by simp [phaseStep, echoStep, hloc])]
        simp [echoPot, hloc, Charge.productive, isProductive, CreditModel.emitted,
          CreditModel.consumed, echo, DynComputation.view_ofStep, phaseStep, echoStep, echoCredit,
          payload]
        omega

theorem echoConserving_total_initial (N : ℕ) (invariant : State (echo N) Unit → Prop) :
    (echoConserving N invariant).total (initial (echo N) ()) = 4 * N := by
  rw [Conserving.total_initial]
  simp [echoConserving, echoPot, echo, phaseInit]

/-- **Bounded work through feedback.** For every fuel, the productive work of the echo loop is at
most `4 N`, because credit decreases around the cycle. -/
theorem echo_work_le (N fuel : ℕ) :
    (runTokenOpen (m := Id) (echoImpl N) Charge.productive (List.replicate fuel .step)
      (initial (echo N) ())).run.2 ≤ 4 * N := by
  obtain ⟨⟨next, work⟩, h⟩ : ∃ r, CanReturn (runTokenOpen (m := Id) (echoImpl N)
      Charge.productive (List.replicate fuel .step) (initial (echo N) ())) r :=
    ⟨_, Id.canReturn_iff.mpr rfl⟩
  rw [Id.canReturn_iff.mp h]
  have := (echoConserving N fun _ => True).work_runTokenOpen_le (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) trivial h
  rw [echoConserving_total_initial] at this
  simp [CreditModel.funded] at this
  omega

/-- The token holder holds a value or has mail. -/
@[expose] def echoReady (N : ℕ) (state : State (echo N) Unit) : Prop :=
  (∃ k, state.localState state.focus = Phase.hold k) ∨ state.inbox state.focus ≠ []

theorem echoReady_initial (N : ℕ) : echoReady N (initial (echo N) ()) :=
  .inl ⟨N, rfl⟩

theorem echoReady_preserves (N : ℕ) : TokenInvariant (echoImpl N) (echoReady N) := by
  intro state next hready h
  have heq := Id.canReturn_iff.mp h
  subst heq
  unfold echoReady at hready ⊢
  generalize hid : state.focus = id at hready ⊢
  rcases hloc : (state.localState id : Phase) with _ | k
  · have hq : state.inbox id ≠ [] := by
      rcases hready with ⟨k, hk⟩ | hq
      · rw [hloc] at hk
        cases hk
      · exact hq
    obtain ⟨packet, rest, hpr⟩ := List.exists_cons_of_ne_nil hq
    rw [echo_activate_receive N id state hloc packet rest hpr]
    exact .inl ⟨payload packet, by simp [hid]⟩
  · cases id with
    | false =>
      cases k with
      | zero =>
        rw [echo_activate_finished N state hloc]
        exact .inl ⟨0, hloc⟩
      | succ k =>
        rw [echo_activate_send N false state k (by simp [phaseStep, counterStep, hloc])]
        exact .inr (by simp)
    | true =>
      rw [echo_activate_send N true state k (by simp [phaseStep, echoStep, hloc])]
      exact .inr (by simp)

/-- Only the counter can finish. -/
theorem echo_outcome_true (N : ℕ) (state : State (echo N) Unit) : outcome true state = none := by
  rcases hloc : (state.localState true : Phase) with _ | k <;>
    simp [outcome, echo, DynComputation.view_ofStep, phaseStep, echoStep, hloc]

theorem echo_positive (N : ℕ) (state : State (echo N) Unit) (hready : echoReady N state)
    (hout : outcome state.focus state = none) :
    1 ≤ (Charge.productive (network := echo N) (S := Unit)) (.node state.focus) state := by
  unfold echoReady at hready
  generalize hid : state.focus = id at hready hout ⊢
  simp only [Charge.productive]
  rcases hloc : (state.localState id : Phase) with _ | k
  · have hq : state.inbox id ≠ [] := by
      rcases hready with ⟨k, hk⟩ | hq
      · rw [hloc] at hk
        cases hk
      · exact hq
    obtain ⟨packet, rest, hpr⟩ := List.exists_cons_of_ne_nil hq
    cases id <;>
      simp [isProductive, echo, DynComputation.view_ofStep, phaseStep, counterStep, echoStep,
        hloc, hpr]
  · cases id with
    | false =>
      cases k with
      | zero =>
        simp [outcome, echo, DynComputation.view_ofStep, phaseStep, counterStep, hloc] at hout
      | succ k =>
        simp [isProductive, echo, DynComputation.view_ofStep, phaseStep, counterStep, hloc]
    | true =>
      simp [isProductive, echo, DynComputation.view_ofStep, phaseStep, echoStep, hloc]

/-- **A global token budget for a feedback loop, derived from local potentials.** -/
def echoBudget (N : ℕ) : TokenBudgetCertificate (echoImpl N) (echoReady N) :=
  (echoConserving N (echoReady N)).toTokenBudgetOfFocusReady (echoReady_preserves N)
    (fun state hready hout => echo_positive N state hready hout)
    (fun state _ hne => by
      have : state.focus = true := by
        cases h : state.focus
        · exact absurd h hne
        · rfl
      rw [this]
      exact echo_outcome_true N state)
    (fun _ _ => ⟨_, Id.canReturn_iff.mpr rfl⟩)

/-- The counter finishes within `4 N` token activations: `N` rounds of send, receive, echo, and
receive. -/
theorem echo_terminal (N : ℕ) :
    ∃ value, outcome false (runToken (m := Id) (echoImpl N) (4 * N)
      (initial (echo N) ())).run = some value :=
  (echoBudget N).runToken_terminal (4 * N) _ _ (echoReady_initial N)
    (le_of_eq (echoConserving_total_initial N (echoReady N))) (Id.canReturn_iff.mpr rfl)

/-! ## Ping-pong -/

/-- **Ping-pong is not conservation-certifiable.** No charge positive at the focus, credit model,
and invariant containing the initial state admit a conserving certificate: conservation caps the
work of every run by the initial total, while each activation costs at least one. -/
theorem feedback_not_conserving (charge : Charge feedback Unit) (credit : CreditModel feedback)
    (invariant : State feedback Unit → Prop) (hinit : invariant (initial feedback ()))
    (preserves : TokenInvariant feedbackImpl invariant)
    (positive : ∀ state, invariant state → outcome state.focus state = none →
      1 ≤ charge (.node state.focus) state) :
    ¬ Nonempty (Conserving feedbackImpl .token charge credit invariant) := by
  rintro ⟨c⟩
  obtain ⟨⟨next, work⟩, h⟩ : ∃ r, CanReturn (runTokenCharged feedbackImpl charge
      (c.total (initial feedback ()) + 1) (initial feedback ())) r :=
    ⟨_, Id.canReturn_iff.mpr rfl⟩
  have hup := c.work_runToken_le preserves hinit h
  have hlow := le_chargedRun (step := tokenStep feedbackImpl) invariant (fun _ => 1)
    (fun _ s s' hs hstep => ⟨preserves s s' hs hstep, positive s hs (feedback_unfinished _ _)⟩)
    _ _ _ _ hinit h
  simp at hlow
  omega

/-- The same conclusion through the derived token budget and `feedback_has_no_budget`. -/
example (charge : Charge feedback Unit) (credit : CreditModel feedback)
    (invariant : State feedback Unit → Prop) (hinit : invariant (initial feedback ()))
    (preserves : TokenInvariant feedbackImpl invariant)
    (positive : ∀ state, invariant state → outcome state.focus state = none →
      1 ≤ charge (.node state.focus) state) :
    ¬ Nonempty (Conserving feedbackImpl .token charge credit invariant) := by
  rintro ⟨c⟩
  exact feedback_has_no_budget invariant hinit
    ⟨c.toTokenBudget preserves positive fun _ _ => ⟨_, Id.canReturn_iff.mpr rfl⟩⟩

/-- Under the unit charge, the work of a token prefix is its fuel. -/
example (fuel : ℕ) :
    (runTokenCharged (m := Id) feedbackImpl Charge.one fuel (initial feedback ())).run.2 = fuel :=
  (runTokenCharged_one feedbackImpl fuel _ _ _ (Id.canReturn_iff.mpr rfl)).1

end Interaction.Execution.ReactiveNetwork.ConservationTests
