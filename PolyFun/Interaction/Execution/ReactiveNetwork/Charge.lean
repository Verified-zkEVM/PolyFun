/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support.Charged
public import PolyFun.Interaction.Execution.ReactiveNetwork.Budget

/-!
# Weighted charges along reactive executions

`State.elapsed` counts activations with unit weight. A `Charge` assigns each activation a weight
read at the state where it fires. Through the acting node's local view it can charge per action
kind; through the mailbox it can tell a blocked receive from a productive one; through the
service state it can charge state-dependent handler costs.

`runTokenCharged` and `runFIFOCharged` run exactly the activations of `runToken` and `runFIFO`
(`map_fst_runTokenCharged`, `map_fst_runFIFOCharged`) and return the weighted work of each
possible result. Under the unit charge `Charge.one` the work is the activation count that
`elapsed` retains (`runTokenCharged_one`, `runFIFOCharged_one`). `Charge.productive` charges one
unit only for activations that advance a local machine: an unfinished node that is not blocked on
an empty mailbox.

`runTokenOpen` interleaves external inputs with token activations. Inputs are uncharged; their
admissibility belongs to the caller. All three runners are `MonadAttach.chargedRun` folds, so
the potential method `MonadAttach.chargedRun_le` bounds their work.
-/

public section

namespace Interaction.Execution.ReactiveNetwork

open PFunctor ReactiveProcess MonadAttach

variable {Node result S : Type} {boundary : PortBoundary}
  {network : Network Node boundary result} [DecidableEq Node] {m : Type → Type} [Monad m]

/-- A weight for each activation, read at the state where it fires. -/
abbrev Charge (network : Network Node boundary result) (S : Type) :=
  Activation Node → State network S → ℕ

/-- The unit charge: every activation costs one, including no-ops and empty deliveries, exactly
as counted by `State.elapsed`. -/
@[expose] def Charge.one : Charge network S := fun _ _ => 1

section Productive

attribute [local implicit_reducible] signature Response

/-- Whether activating `id` advances its local machine: the node is unfinished and, when it is
receiving, has mail. Finished no-ops and blocked receives are administrative. -/
@[expose] def isProductive (id : Node) (state : State network S) : Bool :=
  match (network.component id).view (state.localState id) with
  | .inl _ => false
  | .inr ⟨.receive, _⟩ => !(state.inbox id).isEmpty
  | .inr _ => true

/-- One unit per productive node activation, and nothing for administrative activations or
deliveries. -/
@[expose] def Charge.productive : Charge network S
  | .node id, state => if isProductive id state then 1 else 0
  | .deliver, _ => 0

end Productive

/-! ## Charged runners -/

/-- One token activation, as a step of an event-indexed fold. -/
@[expose] def tokenStep (impl : (id : Node) → Handler (StateT S m) (network.effect id)) :
    Unit → State network S → m (State network S) :=
  fun _ state => activate impl .token state.focus state

/-- A token prefix that also returns its weighted work. -/
@[expose] def runTokenCharged (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (charge : Charge network S) (fuel : ℕ) (state : State network S) :
    m (State network S × ℕ) :=
  chargedRun (tokenStep impl) (fun _ state => charge (.node state.focus) state)
    (List.replicate fuel ()) state

/-- A FIFO schedule that also returns its weighted work. -/
@[expose] def runFIFOCharged (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (charge : Charge network S) (schedule : List (Activation Node)) (state : State network S) :
    m (State network S × ℕ) :=
  chargedRun (fifoStep impl) charge schedule state

/-- An event of an open token execution: a funded external input or one token activation. -/
inductive TokenEvent (boundary : PortBoundary) where
  /-- Inject an external input packet. -/
  | input (packet : Interface.Packet boundary.In)
  /-- Activate the current token holder. -/
  | step

/-- The transition of an open token execution. -/
@[expose] def tokenEventStep (impl : (id : Node) → Handler (StateT S m) (network.effect id)) :
    TokenEvent boundary → State network S → m (State network S)
  | .input packet, state => pure (input packet state)
  | .step, state => activate impl .token state.focus state

/-- Inputs are uncharged; token activations are charged at the focus. -/
@[expose] def tokenEventCharge (charge : Charge network S) :
    TokenEvent boundary → State network S → ℕ
  | .input _, _ => 0
  | .step, state => charge (.node state.focus) state

/-- An open token execution, interleaving inputs with activations, that also returns its weighted
work. -/
@[expose] def runTokenOpen (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (charge : Charge network S) (events : List (TokenEvent boundary))
    (state : State network S) : m (State network S × ℕ) :=
  chargedRun (tokenEventStep impl) (tokenEventCharge charge) events state

/-- An open execution without inputs is the charged token run. -/
theorem runTokenOpen_replicate_step
    (impl : (id : Node) → Handler (StateT S m) (network.effect id)) (charge : Charge network S)
    (fuel : ℕ) (state : State network S) :
    runTokenOpen impl charge (List.replicate fuel .step) state =
      runTokenCharged impl charge fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [runTokenOpen, runTokenCharged, List.replicate_succ, chargedRun] at ih ⊢
    exact bind_congr fun s => by rw [ih]; rfl

/-- The token runner is the fold of `tokenStep` over its fuel. -/
theorem runToken_eq_foldlM (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (fuel : ℕ) (state : State network S) :
    runToken impl fuel state =
      (List.replicate fuel ()).foldlM (fun s e => tokenStep impl e s) state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    rw [List.replicate_succ, List.foldlM_cons, runToken]
    exact bind_congr fun s => ih s

/-- The FIFO runner is the fold of `fifoStep` over its schedule. -/
theorem runFIFO_eq_foldlM (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (schedule : List (Activation Node)) (state : State network S) :
    runFIFO impl schedule state = schedule.foldlM (fun s a => fifoStep impl a s) state := by
  induction schedule generalizing state with
  | nil => rfl
  | cons a rest ih =>
    rw [List.foldlM_cons, runFIFO]
    exact bind_congr fun s => ih s

variable [LawfulMonad m]

/-- The charged token run executes exactly the activations of `runToken`. -/
theorem map_fst_runTokenCharged
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (charge : Charge network S) (fuel : ℕ) (state : State network S) :
    Prod.fst <$> runTokenCharged impl charge fuel state = runToken impl fuel state := by
  rw [runTokenCharged, map_fst_chargedRun, runToken_eq_foldlM]

/-- The charged FIFO run executes exactly the activations of `runFIFO`. -/
theorem map_fst_runFIFOCharged
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (charge : Charge network S) (schedule : List (Activation Node)) (state : State network S) :
    Prod.fst <$> runFIFOCharged impl charge schedule state = runFIFO impl schedule state := by
  rw [runFIFOCharged, map_fst_chargedRun, runFIFO_eq_foldlM]

section Exact

variable [MonadAttach m] [ExactMonadAttach m]

/-- Every token result carries a weighted work, for any charge. -/
theorem canReturn_runToken_iff_runTokenCharged
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (charge : Charge network S) (fuel : ℕ) (state next : State network S) :
    CanReturn (runToken impl fuel state) next ↔
      ∃ work, CanReturn (runTokenCharged impl charge fuel state) (next, work) := by
  rw [runToken_eq_foldlM]
  exact canReturn_foldlM_iff_chargedRun _ _ _ _ _

/-- Every FIFO result carries a weighted work, for any charge. -/
theorem canReturn_runFIFO_iff_runFIFOCharged
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (charge : Charge network S) (schedule : List (Activation Node)) (state next : State network S) :
    CanReturn (runFIFO impl schedule state) next ↔
      ∃ work, CanReturn (runFIFOCharged impl charge schedule state) (next, work) := by
  rw [runFIFO_eq_foldlM]
  exact canReturn_foldlM_iff_chargedRun _ _ _ _ _

/-- Under the unit charge, the work of a token result is its fuel, which is also its `elapsed`
increment. -/
theorem runTokenCharged_one (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (fuel : ℕ) (state next : State network S) (work : ℕ)
    (h : CanReturn (runTokenCharged impl Charge.one fuel state) (next, work)) :
    work = fuel ∧ next.elapsed = state.elapsed + work := by
  have hw : work = fuel := by
    simpa using chargedRun_const (step := tokenStep impl) 1 _ state next work h
  refine ⟨hw, ?_⟩
  have hrun : CanReturn (runToken impl fuel state) next :=
    (canReturn_runToken_iff_runTokenCharged impl Charge.one fuel state next).2 ⟨work, h⟩
  rw [elapsed_runToken impl fuel state next hrun, hw]

/-- Under the unit charge, the work of a FIFO result is its schedule length, deliveries included,
which is also its `elapsed` increment. -/
theorem runFIFOCharged_one (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (schedule : List (Activation Node)) (state next : State network S) (work : ℕ)
    (h : CanReturn (runFIFOCharged impl Charge.one schedule state) (next, work)) :
    work = schedule.length ∧ next.elapsed = state.elapsed + work := by
  have hw : work = schedule.length := by
    simpa using chargedRun_const (step := fifoStep impl) 1 _ state next work h
  refine ⟨hw, ?_⟩
  have hrun : CanReturn (runFIFO impl schedule state) next :=
    (canReturn_runFIFO_iff_runFIFOCharged impl Charge.one schedule state next).2 ⟨work, h⟩
  rw [elapsed_runFIFO impl schedule state next hrun, hw]

end Exact

end Interaction.Execution.ReactiveNetwork
