/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveNetwork.Credit

/-!
# Local conservation certificates on reactive networks

A `Conserving` certificate gives every node a potential on its *own* local states. Its
obligation at each activation the discipline can perform (`Schedulable`) mentions only the acting
node's potential, its charge, the credit it attaches to a sent packet (`emitted`), and the credit
of the packet it consumes (`consumed`):

  `pot id next + charge + emitted ≤ pot id before + consumed`.

Credit moves with packets and routing never creates it, so the network total
`Conserving.total`, node potentials plus credit held by packets, pays for every charge
(`total_activate`). Deliveries and inputs only move or add credit (`total_deliver`,
`total_input`). Soundness follows by the potential method `MonadAttach.chargedRun_le`:

* `work_runToken_le`: token work plus the final total is at most the initial total, for every
  fuel;
* `work_runFIFO_le`: FIFO work is at most the initial total plus an exogenous allowance per
  delivery;
* `work_runTokenOpen_le`, `work_le_initial`: along any interleaving of external inputs and token
  activations from the initial state, work is at most the initial potentials plus the funded
  ingress credit.

Conservation forces administrative activations, finished no-ops and blocked receives, to be free
(`charge_eq_zero_of_finished`, `charge_eq_zero_of_blocked`). The unit count of `State.elapsed` is
therefore not certifiable (`isEmpty_one_of_finished`); `Charge.productive` is the unit charge that
is.

The global `TokenBudgetCertificate` is a corollary (`Conserving.toTokenBudget`). Given positive
charges at unfinished focus activations and progress, its rank is twice the total, plus one while
a finished non-environment node holds the focus: that node's no-op hands control back for free.
When only the environment can hold the focus while finished, the rank is the total itself
(`toTokenBudgetOfFocusReady`).
-/

public section

namespace Interaction.Execution.ReactiveNetwork

open PFunctor ReactiveProcess MonadAttach

variable {Node result S : Type} {boundary : PortBoundary}
  {network : Network Node boundary result} [DecidableEq Node]
  {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

attribute [local implicit_reducible] signature Response

/-- The activations a discipline can perform: token passing activates only the focus. -/
@[expose] def Schedulable (discipline : Discipline) (id : Node) (state : State network S) : Prop :=
  match discipline with
  | .token => id = state.focus
  | .fifo => True

/-- **Local conservation.** Each node's potential, on its own local states, pays for its charge
and for the credit it attaches to a sent packet, out of its decrease plus the credit of the packet
it consumes. -/
structure Conserving (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (discipline : Discipline) (charge : Charge network S) (credit : CreditModel network)
    (invariant : State network S → Prop) where
  /-- Each node's potential on its own local states. -/
  pot : (id : Node) → (network.component id).State → ℕ
  /-- The local obligation at every activation the discipline can perform. -/
  step : ∀ id state next, invariant state → Schedulable discipline id state →
    CanReturn (activate impl discipline id state) next →
      pot id (next.localState id) + charge (.node id) state + credit.emitted id state ≤
        pot id (state.localState id) + credit.consumed id state

namespace Conserving

variable {impl : (id : Node) → Handler (StateT S m) (network.effect id)}
  {discipline : Discipline} {charge : Charge network S} {credit : CreditModel network}
  {invariant : State network S → Prop}

/-- The network potential: node potentials plus credit held by packets. -/
@[expose] def total [Fintype Node] (c : Conserving impl discipline charge credit invariant)
    (state : State network S) : ℕ :=
  (∑ id, c.pot id (state.localState id)) + credit.held state

variable [Fintype Node]

/-- **One activation.** The network potential pays the acting node's charge. -/
theorem total_activate (c : Conserving impl discipline charge credit invariant) {id : Node}
    {state next : State network S} (hinv : invariant state)
    (hsched : Schedulable discipline id state)
    (h : CanReturn (activate impl discipline id state) next) :
    c.total next + charge (.node id) state ≤ c.total state := by
  have hstep := c.step id state next hinv hsched h
  have hheld := credit.held_activate impl discipline id state next h
  have hframe := sum_frame (fun i s => c.pot i s) state.localState next.localState id
    (fun i hi => localState_activate_of_ne impl discipline id i state next h hi)
  simp only [total]
  omega

omit [LawfulMonad m] [ExactMonadAttach m] in
/-- An external input raises the network potential by exactly the credit it is funded with. -/
theorem total_input (c : Conserving impl discipline charge credit invariant)
    (packet : Interface.Packet boundary.In) (state : State network S) :
    c.total (input packet state) = c.total state + credit.ingress packet := by
  have hloc : (input packet state).localState = state.localState := by
    simp only [input, dispatch]
  simp only [total, hloc, credit.held_input]
  omega

omit [LawfulMonad m] [ExactMonadAttach m] in
/-- A FIFO delivery moves credit without changing the network potential. -/
theorem total_deliver (c : Conserving impl discipline charge credit invariant)
    (state : State network S) : c.total (deliver state) = c.total state := by
  have hloc : (deliver state).localState = state.localState := by
    unfold deliver
    cases state.pending with
    | nil => rfl
    | cons destination rest => cases destination <;> rfl
  simp only [total, hloc, credit.held_deliver]

omit [LawfulMonad m] [ExactMonadAttach m] in
/-- The initial network potential is the sum of the initial node potentials. -/
theorem total_initial (c : Conserving impl discipline charge credit invariant) (service : S) :
    c.total (initial network service) = ∑ id, c.pot id ((network.component id).init ()) := by
  simp only [total, credit.held_initial, add_zero]
  rfl

/-! ## Administrative activations are free -/

omit [LawfulMonad m] [Fintype Node] in
/-- Conservation forces activations of finished nodes to be free. -/
theorem charge_eq_zero_of_finished (c : Conserving impl discipline charge credit invariant)
    {id : Node} {state : State network S} {value : Outcome result}
    (hinv : invariant state) (hsched : Schedulable discipline id state)
    (hout : outcome id state = some value) : charge (.node id) state = 0 := by
  unfold outcome at hout
  rcases hv : (network.component id).view (state.localState id) with result | ⟨action, cont⟩
  · have h : CanReturn (activate impl discipline id state)
        { state with elapsed := state.elapsed + 1, focus := network.environment } := by
      simp only [activate, hv]
      exact ExactMonadAttach.canReturn_pure _
    have hstep := c.step id state _ hinv hsched h
    simp only [CreditModel.emitted, CreditModel.consumed, hv] at hstep
    omega
  · simp [hv] at hout

omit [LawfulMonad m] [Fintype Node] in
/-- Conservation forces blocked receives, which change nothing, to be free. -/
theorem charge_eq_zero_of_blocked (c : Conserving impl discipline charge credit invariant)
    {id : Node} {state : State network S}
    {cont : Interface.Packet (network.ports id).In → (network.component id).State}
    (hinv : invariant state) (hsched : Schedulable discipline id state)
    (hv : (network.component id).view (state.localState id) = .inr ⟨.receive, cont⟩)
    (hq : state.inbox id = []) : charge (.node id) state = 0 := by
  have h : CanReturn (activate impl discipline id state)
      { state with elapsed := state.elapsed + 1 } := by
    simp only [activate, hv, hq]
    exact ExactMonadAttach.canReturn_pure _
  have hstep := c.step id state _ hinv hsched h
  simp only [CreditModel.emitted, CreditModel.consumed, hv, hq] at hstep
  omega

end Conserving

omit [LawfulMonad m] in
/-- The unit charge counted by `State.elapsed` is not conservation-certifiable once an invariant
state lets the discipline activate a finished node: conservation makes that activation free. -/
theorem isEmpty_conserving_one_of_finished
    {impl : (id : Node) → Handler (StateT S m) (network.effect id)} {discipline : Discipline}
    {credit : CreditModel network} {invariant : State network S → Prop} {id : Node}
    {state : State network S} {value : Outcome result} (hinv : invariant state)
    (hsched : Schedulable discipline id state) (hout : outcome id state = some value) :
    IsEmpty (Conserving impl discipline Charge.one credit invariant) :=
  ⟨fun c => by simpa [Charge.one] using c.charge_eq_zero_of_finished hinv hsched hout⟩

/-! ## Executions -/

section Executions

/-- Token passing keeps the invariant. -/
@[expose] def TokenInvariant (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (invariant : State network S → Prop) : Prop :=
  ∀ state next, invariant state →
    CanReturn (activate impl .token state.focus state) next → invariant next

/-- FIFO execution keeps the invariant. -/
@[expose] def FIFOInvariant (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (invariant : State network S → Prop) : Prop :=
  ∀ activation state next, invariant state →
    CanReturn (fifoStep impl activation state) next → invariant next

/-- The exogenous allowance of a FIFO activation: deliveries are paid by the scheduler. -/
private def deliveryAllowance (δ : ℕ) : Activation Node → ℕ
  | .node _ => 0
  | .deliver => δ

private theorem sum_deliveryAllowance (δ : ℕ) (schedule : List (Activation Node)) :
    (schedule.map (deliveryAllowance δ)).sum = δ * schedule.count .deliver := by
  induction schedule with
  | nil => simp
  | cons activation rest ih =>
    cases activation with
    | node id => simp [deliveryAllowance, ih]
    | deliver =>
      simp only [List.map_cons, deliveryAllowance, List.sum_cons, ih, List.count_cons_self,
        Nat.mul_succ]
      omega

end Executions

/-! ## Soundness along executions -/

namespace Conserving

variable {impl : (id : Node) → Handler (StateT S m) (network.effect id)}
  {charge : Charge network S} {credit : CreditModel network}
  {invariant : State network S → Prop} [Fintype Node]

/-- **Token soundness.** The weighted work of every token result, plus the final network
potential, is at most the initial network potential, whatever the fuel. -/
theorem work_runToken_le (c : Conserving impl .token charge credit invariant)
    (preserves : TokenInvariant impl invariant) {fuel : ℕ} {state next : State network S}
    {work : ℕ} (hinv : invariant state)
    (h : CanReturn (runTokenCharged impl charge fuel state) (next, work)) :
    work + c.total next ≤ c.total state := by
  have := chargedRun_le invariant c.total (fun _ => 0)
    (fun _ s s' hs hstep => ⟨preserves s s' hs hstep, by
      simpa using c.total_activate hs rfl hstep⟩) _ state next work hinv h
  simpa using this.2

/-- **FIFO soundness.** Node work is paid by the network potential. Deliveries move credit without
changing it, so their charges are an exogenous allowance of the scheduler. -/
theorem work_runFIFO_le (c : Conserving impl .fifo charge credit invariant)
    (preserves : FIFOInvariant impl invariant) (δ : ℕ)
    (hdeliver : ∀ state, invariant state → charge .deliver state ≤ δ)
    {schedule : List (Activation Node)} {state next : State network S} {work : ℕ}
    (hinv : invariant state)
    (h : CanReturn (runFIFOCharged impl charge schedule state) (next, work)) :
    work + c.total next ≤ c.total state + δ * schedule.count .deliver := by
  have := chargedRun_le invariant c.total (deliveryAllowance δ)
    (fun activation s s' hs hstep => ⟨preserves activation s s' hs hstep, by
      cases activation with
      | node id => simpa [deliveryAllowance] using c.total_activate hs trivial hstep
      | deliver =>
        have heq : s' = deliver s := canReturn_pure_iff.mp hstep
        subst heq
        rw [c.total_deliver]
        simpa [deliveryAllowance] using hdeliver s hs⟩) _ state next work hinv h
  rw [← sum_deliveryAllowance]
  exact this.2

/-- **Open soundness.** Along any interleaving of inputs and token activations, work plus the
final network potential is at most the initial potential plus the funded ingress credit. -/
theorem work_runTokenOpen_le (c : Conserving impl .token charge credit invariant)
    (preserves : TokenInvariant impl invariant)
    (preserves_input : ∀ packet state, invariant state → invariant (input packet state))
    {events : List (TokenEvent boundary)} {state next : State network S} {work : ℕ}
    (hinv : invariant state)
    (h : CanReturn (runTokenOpen impl charge events state) (next, work)) :
    work + c.total next ≤ c.total state + (events.map credit.funded).sum := by
  refine (chargedRun_le invariant c.total credit.funded
    (fun event s s' hs hstep => ?_) _ state next work hinv h).2
  cases event with
  | input packet =>
    have heq : s' = input packet s := canReturn_pure_iff.mp hstep
    subst heq
    refine ⟨preserves_input packet s hs, ?_⟩
    simp [tokenEventCharge, CreditModel.funded, c.total_input]
  | step =>
    exact ⟨preserves s s' hs hstep, by
      simpa [tokenEventCharge, CreditModel.funded] using c.total_activate hs rfl hstep⟩

/-- **The headline bound.** From the initial state, the total weighted work of any open token
execution is at most the sum of the nodes' initial potentials plus the funded ingress credit. -/
theorem work_le_initial (c : Conserving impl .token charge credit invariant)
    (preserves : TokenInvariant impl invariant)
    (preserves_input : ∀ packet state, invariant state → invariant (input packet state))
    {service : S} (hinit : invariant (initial network service))
    {events : List (TokenEvent boundary)} {next : State network S} {work : ℕ}
    (h : CanReturn (runTokenOpen impl charge events (initial network service)) (next, work)) :
    work ≤ (∑ id, c.pot id ((network.component id).init ())) +
      (events.map credit.funded).sum := by
  have := c.work_runTokenOpen_le preserves preserves_input hinit h
  rw [c.total_initial] at this
  omega

/-! ## The global certificate as a corollary -/

/-- A conserving certificate with positive charges at unfinished focus activations, and progress,
yields a global token budget. The rank is twice the network potential, plus one while a finished
non-environment node holds the focus: its no-op activation is free under conservation, and the
extra unit pays for handing control back. -/
@[expose] def toTokenBudget (c : Conserving impl .token charge credit invariant)
    (preserves : TokenInvariant impl invariant)
    (positive : ∀ state, invariant state → outcome state.focus state = none →
      1 ≤ charge (.node state.focus) state)
    (progress : ∀ state, invariant state →
      ∃ next, CanReturn (activate impl .token state.focus state) next) :
    TokenBudgetCertificate impl invariant where
  rank state := 2 * c.total state +
    if state.focus ≠ network.environment ∧ (outcome state.focus state).isSome then 1 else 0
  zero state hinv hz := by
    cases henv : outcome network.environment state with
    | some value => exact ⟨value, rfl⟩
    | none =>
      exfalso
      have hf : outcome state.focus state = none := by
        by_cases heq : state.focus = network.environment
        · rw [heq]
          exact henv
        · cases hfo : outcome state.focus state with
          | none => rfl
          | some value =>
            rw [hfo] at hz
            simp [heq] at hz
      obtain ⟨next, h⟩ := progress state hinv
      have htot := c.total_activate hinv rfl h
      have hpos := positive state hinv hf
      have hbonus : (if state.focus ≠ network.environment ∧ (outcome state.focus state).isSome
          then 1 else 0) = 0 := by simp [hf]
      omega
  preserves := preserves
  decreases state next hinv henv h := by
    have hle : (if next.focus ≠ network.environment ∧ (outcome next.focus next).isSome
        then 1 else 0) ≤ 1 := by split_ifs <;> omega
    obtain hf | ⟨value, hf⟩ : outcome state.focus state = none ∨
        ∃ value, outcome state.focus state = some value := by
      cases outcome state.focus state
      · exact .inl rfl
      · exact .inr ⟨_, rfl⟩
    · have htot := c.total_activate hinv rfl h
      have hpos := positive state hinv hf
      have hbonus : (if state.focus ≠ network.environment ∧ (outcome state.focus state).isSome
          then 1 else 0) = 0 := by simp [hf]
      omega
    · have hne : state.focus ≠ network.environment := by
        intro heq
        rw [heq, henv] at hf
        cases hf
      obtain ⟨hfocus, hloc, hinbox, hpend, hout⟩ :=
        activate_of_finished impl .token state.focus state next value hf h
      have htot : c.total next = c.total state := by
        simp only [total, hloc, credit.held_congr hinbox hpend hout]
      have hbonus : (if state.focus ≠ network.environment ∧ (outcome state.focus state).isSome
          then 1 else 0) = 1 := by simp [hf, hne]
      have hbonus' : (if next.focus ≠ network.environment ∧ (outcome next.focus next).isSome
          then 1 else 0) = 0 := by simp [hfocus]
      omega
  progress := progress

/-- When only the environment can hold the focus while finished, the network potential itself is
a global token rank. -/
@[expose] def toTokenBudgetOfFocusReady (c : Conserving impl .token charge credit invariant)
    (preserves : TokenInvariant impl invariant)
    (positive : ∀ state, invariant state → outcome state.focus state = none →
      1 ≤ charge (.node state.focus) state)
    (ready : ∀ state, invariant state → state.focus ≠ network.environment →
      outcome state.focus state = none)
    (progress : ∀ state, invariant state →
      ∃ next, CanReturn (activate impl .token state.focus state) next) :
    TokenBudgetCertificate impl invariant where
  rank := c.total
  zero state hinv hz := by
    cases henv : outcome network.environment state with
    | some value => exact ⟨value, rfl⟩
    | none =>
      exfalso
      have hf : outcome state.focus state = none := by
        by_cases heq : state.focus = network.environment
        · rw [heq]
          exact henv
        · exact ready state hinv heq
      obtain ⟨next, h⟩ := progress state hinv
      have htot := c.total_activate hinv rfl h
      have hpos := positive state hinv hf
      omega
  preserves := preserves
  decreases state next hinv henv h := by
    have hf : outcome state.focus state = none := by
      by_cases heq : state.focus = network.environment
      · rw [heq]
        exact henv
      · exact ready state hinv heq
    have htot := c.total_activate hinv rfl h
    have hpos := positive state hinv hf
    omega
  progress := progress

/-- Conservation with positive charges and progress proves completion within
`2 · total + 1` token activations. -/
theorem runToken_terminal (c : Conserving impl .token charge credit invariant)
    (preserves : TokenInvariant impl invariant)
    (positive : ∀ state, invariant state → outcome state.focus state = none →
      1 ≤ charge (.node state.focus) state)
    (progress : ∀ state, invariant state →
      ∃ next, CanReturn (activate impl .token state.focus state) next)
    {fuel : ℕ} {state next : State network S} (hinv : invariant state)
    (hfuel : 2 * c.total state + 1 ≤ fuel) (h : CanReturn (runToken impl fuel state) next) :
    ∃ value, outcome network.environment next = some value := by
  refine (c.toTokenBudget preserves positive progress).runToken_terminal fuel state next hinv
    ?_ h
  change 2 * c.total state + _ ≤ fuel
  split_ifs <;> omega

end Conserving

end Interaction.Execution.ReactiveNetwork
