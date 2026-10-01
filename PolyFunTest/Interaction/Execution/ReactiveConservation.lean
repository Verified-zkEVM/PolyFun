/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Interaction.Execution.ReactiveBudget
public import PolyFun.Interaction.Execution.ReactiveNetwork.Import
public import PolyFun.Interaction.Execution.ReactiveNetwork.InputRelative
public import PolyFun.Interaction.Execution.ReactiveNetwork.Local

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
* **Component certificates.** Certificates about the countdown's and the echo loop's processes
  alone, placed at their nodes, give the same network potentials.
* **Import ledgers.** The countdown is an import ledger with endowment `n`. Its work is bounded by
  the endowment, and as a linear ledger it is a conserving certificate.
* **Input-relative certificates.** Both ping-pong nodes are input-relatively certified, yet their
  joint productive work is unbounded, and no exchange rates satisfy the gain law.
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

/-! ## Component certificates -/

/-- The countdown's component certificate: the counter is the potential and each tick costs one. -/
def countdownProcess (n : ℕ) :
    ProcessConserving ((countdown n).component ()) (countdownImpl n ()) (fun _ => 1)
      ((countdownCredit n).inbound ()) ((countdownCredit n).outbound ()) where
  pot s := (s : ℕ)
  onEffect _ operation := operation.elim
  onReceive s _ _ hv := by
    simp only [countdown, DynComputation.view_ofStep] at hv
    cases s <;> simp only [countdownStep] at hv <;> cases hv
  onSend s _ _ hv := by
    simp only [countdown, DynComputation.view_ofStep] at hv
    cases s <;> simp only [countdownStep] at hv <;> cases hv
  onTick s cont hv := by
    simp only [countdown, DynComputation.view_ofStep] at hv
    cases s with
    | zero => simp only [countdownStep] at hv; cases hv
    | succ k =>
      simp only [countdownStep] at hv
      cases hv
      exact le_refl _
  onYield s _ hv := by
    simp only [countdown, DynComputation.view_ofStep] at hv
    cases s <;> simp only [countdownStep] at hv <;> cases hv

/-- Placed at the countdown's only node, the component certificate has the counter as network
potential, and its unit component charge is the productive charge. -/
example (n : ℕ) :
    (ProcessConserving.toConserving (fun _ => countdownProcess n) .token (fun _ => True)).total
      (initial (countdown n) ()) = n ∧
    Charge.ofLocal (network := countdown n) (S := Unit) (fun _ _ => 1) = Charge.productive := by
  refine ⟨?_, Charge.ofLocal_one⟩
  rw [Conserving.total_initial]
  simp [ProcessConserving.toConserving, countdownProcess, countdown]

/-- The counter's component certificate: potential `4 k` while holding `k`. -/
def counterProcess (N : ℕ) :
    ProcessConserving ((echo N).component false) (echoImpl N false) (fun _ => 1)
      ((echoCredit N).inbound false) ((echoCredit N).outbound false) where
  pot
    | .wait => 0
    | .hold k => 4 * k
  onEffect _ operation := operation.elim
  onReceive s cont packet hv := by
    simp only [echo, DynComputation.view_ofStep, phaseStep] at hv
    rcases s with _ | _ | k <;> simp only [counterStep] at hv <;> cases hv
    simp [echoCredit, payload]
  onSend s packet cont hv := by
    simp only [echo, DynComputation.view_ofStep, phaseStep] at hv
    rcases s with _ | _ | k <;> simp only [counterStep] at hv <;> cases hv
    simp [echoCredit, payload]
    omega
  onTick s cont hv := by
    simp only [echo, DynComputation.view_ofStep, phaseStep] at hv
    rcases s with _ | _ | k <;> simp only [counterStep] at hv <;> cases hv
  onYield s cont hv := by
    simp only [echo, DynComputation.view_ofStep, phaseStep] at hv
    rcases s with _ | _ | k <;> simp only [counterStep] at hv <;> cases hv

/-- The echo's component certificate: potential `4 k + 2` while holding `k`. -/
def echoProcess (N : ℕ) :
    ProcessConserving ((echo N).component true) (echoImpl N true) (fun _ => 1)
      ((echoCredit N).inbound true) ((echoCredit N).outbound true) where
  pot
    | .wait => 0
    | .hold k => 4 * k + 2
  onEffect _ operation := operation.elim
  onReceive s cont packet hv := by
    simp only [echo, DynComputation.view_ofStep, phaseStep] at hv
    rcases s with _ | k <;> simp only [echoStep] at hv <;> cases hv
    simp [echoCredit, payload]
  onSend s packet cont hv := by
    simp only [echo, DynComputation.view_ofStep, phaseStep] at hv
    rcases s with _ | k <;> simp only [echoStep] at hv <;> cases hv
    simp [echoCredit, payload]
    omega
  onTick s cont hv := by
    simp only [echo, DynComputation.view_ofStep, phaseStep] at hv
    rcases s with _ | k <;> simp only [echoStep] at hv <;> cases hv
  onYield s cont hv := by
    simp only [echo, DynComputation.view_ofStep, phaseStep] at hv
    rcases s with _ | k <;> simp only [echoStep] at hv <;> cases hv

/-- The echo loop's network certificate from its two component certificates. -/
def echoConservingOfProcesses (N : ℕ) :
    Conserving (echoImpl N) .token (Charge.ofLocal fun _ _ => 1) (echoCredit N) (fun _ => True) :=
  ProcessConserving.toConserving
    (fun id => match id with
      | false => counterProcess N
      | true => echoProcess N) .token _

/-- The component certificates give the same initial network potential, `4 N`. -/
example (N : ℕ) : (echoConservingOfProcesses N).total (initial (echo N) ()) = 4 * N := by
  rw [Conserving.total_initial]
  simp [echoConservingOfProcesses, ProcessConserving.toConserving, counterProcess, echoProcess,
    echo, phaseInit]

/-! ## Import ledgers -/

/-- The counter value of a countdown state. -/
@[expose] def counter {n : ℕ} (s : ((countdown n).component ()).State) : ℕ := s

/-- The countdown as an import ledger: an endowment of `n`, and `n - s` steps taken at counter
`s`. -/
def countdownLedger (n : ℕ) :
    ImportBounded (countdownImpl n) .token Charge.productive (countdownCredit n)
      (fun state => counter (state.localState ()) ≤ n) id where
  net _ _ := n
  steps _ s := n - counter s
  bounded _ _ := Nat.sub_le _ _
  ledger id state next hinv _ h := by
    have heq := Id.canReturn_iff.mp h
    subst heq
    cases id
    cases hs : (state.localState () : ℕ) with
    | zero =>
      simp [activate, countdown, DynComputation.view_ofStep, hs, countdownStep,
        Charge.productive, isProductive, CreditModel.emitted, CreditModel.consumed]
    | succ k =>
      simp only [counter, hs] at hinv
      simp [activate, countdown, DynComputation.view_ofStep, hs, countdownStep, counter,
        Charge.productive, isProductive, CreditModel.emitted, CreditModel.consumed]
      omega

/-- The countdown never raises its counter. -/
theorem countdown_preserves (n : ℕ) :
    TokenInvariant (countdownImpl n) (fun state => counter (state.localState ()) ≤ n) := by
  intro state next hinv h
  have heq := Id.canReturn_iff.mp h
  subst heq
  cases hfocus : state.focus
  cases hs : (state.localState () : ℕ) with
  | zero =>
    simp [activate, countdown, DynComputation.view_ofStep, hs, countdownStep, counter]
  | succ k =>
    simp only [counter, hs] at hinv
    simp [activate, countdown, DynComputation.view_ofStep, hs, countdownStep, hfocus, counter]
    omega

/-- The ledger bounds the countdown's work by its endowment, for every fuel. -/
example (n fuel : ℕ) :
    (runTokenOpen (m := Id) (countdownImpl n) Charge.productive (List.replicate fuel .step)
      (initial (countdown n) ())).run.2 ≤ n := by
  obtain ⟨⟨next, work⟩, h⟩ : ∃ r, CanReturn (runTokenOpen (m := Id) (countdownImpl n)
      Charge.productive (List.replicate fuel .step) (initial (countdown n) ())) r :=
    ⟨_, Id.canReturn_iff.mpr rfl⟩
  rw [Id.canReturn_iff.mp h]
  have := (countdownLedger n).work_runTokenOpen_le (fun _ _ => le_rfl) monotone_id
    (countdown_preserves n) (fun packet _ _ => packet.1.elim) (by exact le_rfl) h
  simp [ImportBounded.imported, ImportBounded.stepsTotal, countdownLedger, countdown_held,
    CreditModel.funded] at this
  omega

/-- A linear ledger is a conserving certificate. -/
example (n : ℕ) :
    Conserving (countdownImpl n) .token Charge.productive (countdownCredit n)
      (fun state => counter (state.localState ()) ≤ n) :=
  (countdownLedger n).toConserving

/-! ## Input-relative certificates across feedback -/

/-- Two units of credit per packet: one per activation of the receive and send it causes. -/
def credit2 : CreditModel feedback where
  inbound _ _ := 2
  outbound _ _ := 2
  exported _ := 0
  route_le _ _ := le_refl _

/-- A node's potential: one unit while it still has to send. -/
@[expose] def loopPot (s : Bool) : ℕ := if s then 1 else 0

/-- Both ping-pong nodes are input-relatively certified, under any invariant. -/
def feedbackInputRelative (invariant : State feedback Unit → Prop) :
    InputRelative feedbackImpl .token Charge.productive credit2 invariant where
  pot _ s := loopPot s
  step id state next _ _ h := by
    have heq := Id.canReturn_iff.mp h
    subst heq
    cases hs : (state.localState id : Bool) with
    | true =>
      simp [activate, feedback, DynComputation.view_ofStep, hs, loopStep, dispatch,
        Charge.productive, isProductive, CreditModel.consumed, loopPot]
    | false =>
      cases hq : state.inbox id with
      | nil =>
        simp [activate, feedback, DynComputation.view_ofStep, hs, hq, loopStep,
          Charge.productive, isProductive, CreditModel.consumed, loopPot]
      | cons packet rest =>
        simp [activate, feedback, DynComputation.view_ofStep, hs, hq, loopStep,
          Charge.productive, isProductive, CreditModel.consumed, loopPot, credit2]

/-- The token holder can always act: it is about to send, or it has mail. -/
@[expose] def feedbackReady (state : State feedback Unit) : Prop :=
  (state.localState state.focus : Bool) = true ∨ state.inbox state.focus ≠ []

theorem feedbackReady_initial : feedbackReady (initial feedback ()) := by
  left
  rfl

/-- A node about to send hands its packet and the token to the other node. -/
theorem feedback_activate_send (id : Bool) (state : State feedback Unit)
    (hs : (state.localState id : Bool) = true) :
    (activate feedbackImpl .token id state).run =
      { state with
        elapsed := state.elapsed + 1
        localState := Function.update state.localState id (false : Bool)
        inbox := Function.update state.inbox (!id) (state.inbox (!id) ++ [⟨(), ()⟩])
        focus := !id } := by
  simp [activate, feedback, DynComputation.view_ofStep, hs, loopStep, dispatch]

/-- A node with mail consumes it and becomes ready to send. -/
theorem feedback_activate_receive (id : Bool) (state : State feedback Unit)
    (hs : (state.localState id : Bool) = false) (packet : Interface.Packet unitPort)
    (rest : List (Interface.Packet unitPort)) (hq : state.inbox id = packet :: rest) :
    (activate feedbackImpl .token id state).run =
      { state with
        elapsed := state.elapsed + 1
        localState := Function.update state.localState id (true : Bool)
        inbox := Function.update state.inbox id rest } := by
  simp [activate, feedback, DynComputation.view_ofStep, hs, hq, loopStep]

theorem feedbackReady_preserves : TokenInvariant feedbackImpl feedbackReady := by
  intro state next hready h
  have heq := Id.canReturn_iff.mp h
  subst heq
  cases hs : (state.localState state.focus : Bool) with
  | true =>
    rw [feedback_activate_send _ _ hs]
    right
    simp
  | false =>
    have hq : state.inbox state.focus ≠ [] := by
      rcases hready with h' | h'
      · rw [hs] at h'
        cases h'
      · exact h'
    obtain ⟨packet, rest, hpr⟩ := List.exists_cons_of_ne_nil hq
    rw [feedback_activate_receive _ _ hs packet rest hpr]
    left
    simp

theorem productive_of_ready (state : State feedback Unit) (hready : feedbackReady state) :
    Charge.productive (.node state.focus) state = 1 := by
  rcases hready with hs | hq
  · simp [Charge.productive, isProductive, feedback, DynComputation.view_ofStep, hs, loopStep]
  · cases hs : (state.localState state.focus : Bool) with
    | true =>
      simp [Charge.productive, isProductive, feedback, DynComputation.view_ofStep, hs, loopStep]
    | false =>
      simp [Charge.productive, isProductive, feedback, DynComputation.view_ofStep, hs, loopStep,
        hq]

theorem productive_le_one (activation : Activation Bool) (state : State feedback Unit) :
    Charge.productive activation state ≤ 1 := by
  cases activation with
  | node id => simp only [Charge.productive]; split_ifs <;> omega
  | deliver => simp [Charge.productive]

/-- The productive work of `fuel` token activations from the initial state is exactly `fuel`. -/
theorem feedback_productive_work (fuel : ℕ) :
    (runTokenCharged (m := Id) feedbackImpl Charge.productive fuel
      (initial feedback ())).run.2 = fuel := by
  obtain ⟨⟨next, work⟩, h⟩ : ∃ r, CanReturn (runTokenCharged (m := Id) feedbackImpl
      Charge.productive fuel (initial feedback ())) r := ⟨_, Id.canReturn_iff.mpr rfl⟩
  rw [Id.canReturn_iff.mp h]
  have hlow := le_chargedRun (step := tokenStep feedbackImpl) feedbackReady (fun _ => 1)
    (fun _ s s' hs hstep => ⟨feedbackReady_preserves s s' hs hstep,
      (productive_of_ready s hs).ge⟩) _ _ _ _ feedbackReady_initial h
  have hup := (chargedRun_le (step := tokenStep feedbackImpl) (fun _ => True) (fun _ => 0)
    (fun _ => 1) (fun _ s _ _ _ => ⟨trivial, by simpa using productive_le_one _ s⟩) _ _ _ _
    trivial h).2
  simp at hlow hup
  omega

/-- **Input-relative certificates do not compose across feedback.** Both nodes are certified
(`feedbackInputRelative`), yet their joint work is unbounded. -/
theorem feedback_work_unbounded :
    ¬ ∃ bound, ∀ fuel, (runTokenCharged (m := Id) feedbackImpl Charge.productive fuel
      (initial feedback ())).run.2 ≤ bound := by
  rintro ⟨bound, hbound⟩
  have := hbound (bound + 1)
  rw [feedback_productive_work] at this
  omega

/-- **No exchange rates make the certified ping-pong nodes satisfy the gain law**; otherwise the
re-denominated certificate would be conserving. -/
theorem feedback_no_smallGain (w : Bool → ℕ) :
    ¬ SmallGain .token Charge.productive credit2 feedbackReady w := by
  intro hgain
  exact feedback_not_conserving Charge.productive (credit2.reweight w) feedbackReady
    feedbackReady_initial feedbackReady_preserves
    (fun state hready _ => (productive_of_ready state hready).ge)
    ⟨(feedbackInputRelative feedbackReady).toConserving w hgain⟩

end Interaction.Execution.ReactiveNetwork.ConservationTests
