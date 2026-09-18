/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveNetwork

/-!
# Serial comparison of token passing and FIFO delivery

With no outstanding FIFO traffic, a local activation followed by a delivery activation
has the same residual machines, mailboxes, shared state, output, and control holder as one
token activation. The FIFO round consumes one additional activation, including when there
is nothing to deliver. This comparison names a serialized policy; it does not identify
arbitrary FIFO schedules with token passing.
-/

public section

namespace Interaction.Execution.ReactiveNetwork

open PFunctor ReactiveProcess

attribute [local implicit_reducible] signature Response

variable {Node result S : Type} {boundary : PortBoundary}
  {network : Network Node boundary result} [DecidableEq Node]
  {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Add explicitly accounted administrative work without changing the residual execution. -/
@[expose] def State.addElapsed (extra : ℕ) (state : State network S) : State network S :=
  { state with elapsed := state.elapsed + extra }

/-- A serial FIFO round spends a local activation and one delivery activation. -/
@[expose] def serialRound
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (state : State network S) : m (State network S) :=
  deliver <$> activate impl .fifo state.focus state

/-- A serial FIFO round agrees with one token activation, retaining its extra delivery cost. -/
theorem serialRound_eq_token
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (state : State network S) (hqueue : state.pending = []) :
    serialRound impl state = State.addElapsed 1 <$> activate impl .token state.focus state := by
  cases h : (network.component state.focus).view (state.localState state.focus) with
  | inl value => simp [serialRound, activate, h, deliver, hqueue, State.addElapsed]
  | inr action =>
      rcases action with ⟨action, next⟩
      cases action with
      | effect operation => simp [serialRound, activate, h, deliver, hqueue, State.addElapsed]
      | receive =>
          cases hin : state.inbox state.focus <;>
            simp [serialRound, activate, h, hin, deliver, hqueue, State.addElapsed]
      | send packet =>
          cases hr : network.route state.focus packet <;>
            simp [serialRound, activate, h, deliver, hqueue, hr, dispatch, State.addElapsed]
      | tick => simp [serialRound, activate, h, deliver, hqueue, State.addElapsed]
      | yield => simp [serialRound, activate, h, deliver, hqueue, State.addElapsed]

/-- The round is an actual two-activation FIFO execution. -/
theorem serialRound_eq_runFIFO
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (state : State network S) :
    serialRound impl state = runFIFO impl [.node state.focus, .deliver] state := by
  simp [serialRound, runFIFO, fifoStep, bind_pure_comp]

/-- Accounting for prior work does not change which local operation is executed. -/
theorem activate_addElapsed
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (discipline : Discipline) (id : Node) (extra : ℕ) (state : State network S) :
    activate impl discipline id (state.addElapsed extra) =
      State.addElapsed extra <$> activate impl discipline id state := by
  cases h : (network.component id).view (state.localState id) with
  | inl value => simp [activate, h, State.addElapsed, Nat.add_right_comm]
  | inr action =>
      rcases action with ⟨action, next⟩
      cases action with
      | effect operation => simp [activate, h, State.addElapsed, Nat.add_right_comm]
      | receive =>
          cases hin : state.inbox id <;>
            simp [activate, h, hin, State.addElapsed, Nat.add_right_comm]
      | send packet =>
          cases discipline <;> cases hr : network.route id packet <;>
            simp [activate, h, hr, dispatch, State.addElapsed, Nat.add_right_comm]
      | tick => simp [activate, h, State.addElapsed, Nat.add_right_comm]
      | yield => simp [activate, h, State.addElapsed, Nat.add_right_comm]

/-- Execute a finite serial FIFO policy. Each round activates the current control holder
and then delivers one packet. The policy reads only `focus`, never private component or
service state, and charges a delivery even when the queue is empty. -/
@[expose] def runSerial
    (impl : (id : Node) → Handler (StateT S m) (network.effect id)) :
    ℕ → State network S → m (State network S)
  | 0, state => pure state
  | rounds + 1, state => serialRound impl state >>= runSerial impl rounds

/-- Serial execution can be paused and resumed without resetting its queues or control. -/
theorem runSerial_add
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (first rest : ℕ) (state : State network S) :
    runSerial impl (first + rest) state =
      (runSerial impl first state >>= runSerial impl rest) := by
  induction first generalizing state with
  | zero => simp [runSerial]
  | succ first ih =>
      simp only [Nat.succ_add, runSerial, bind_assoc]
      exact bind_congr ih

/-- Prior administrative work does not affect a token-passing prefix. -/
theorem runToken_addElapsed
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (fuel extra : ℕ) (state : State network S) :
    runToken impl fuel (state.addElapsed extra) =
      State.addElapsed extra <$> runToken impl fuel state := by
  induction fuel generalizing state with
  | zero => simp [runToken]
  | succ fuel ih =>
      simp only [runToken]
      rw [activate_addElapsed, bind_map_left, map_bind]
      exact bind_congr ih

/-- Continuations after a token activation need agree only on states with the unchanged
pending FIFO queue. This law works for any lawful monad without a support operation. -/
theorem activate_token_bind_congr {α : Type}
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (id : Node) (state : State network S) (left right : State network S → m α)
    (h : ∀ next, next.pending = state.pending → left next = right next) :
    (activate impl .token id state >>= left) =
      (activate impl .token id state >>= right) := by
  cases hv : (network.component id).view (state.localState id) with
  | inl value => simp only [activate, hv, pure_bind]; exact h _ rfl
  | inr action =>
      rcases action with ⟨action, next⟩
      cases action with
      | effect operation =>
          simp only [activate, hv, bind_assoc, pure_bind]
          exact bind_congr fun _ => h _ rfl
      | receive =>
          cases hin : state.inbox id <;>
            simp only [activate, hv, hin, pure_bind] <;> exact h _ rfl
      | send packet =>
          cases hr : network.route id packet <;>
            simp only [activate, hv, hr, dispatch, pure_bind] <;> exact h _ rfl
      | tick => simp only [activate, hv, pure_bind]; exact h _ rfl
      | yield => simp only [activate, hv, pure_bind]; exact h _ rfl

/-- From an empty pending queue, any finite serial FIFO execution agrees with token
passing on the complete residual state, with one extra charged delivery per round. -/
theorem runSerial_eq_runToken
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (rounds : ℕ) (state : State network S) (hqueue : state.pending = []) :
    runSerial impl rounds state = State.addElapsed rounds <$> runToken impl rounds state := by
  induction rounds generalizing state with
  | zero => simp [runSerial, runToken, State.addElapsed]
  | succ rounds ih =>
      rw [runSerial, serialRound_eq_token impl state hqueue, bind_map_left, runToken, map_bind]
      apply activate_token_bind_congr
      intro next hpending
      rw [ih (next.addElapsed 1) (hpending.trans hqueue), runToken_addElapsed]
      rw [Functor.map_map]
      congr 1
      funext finalState
      simp only [State.addElapsed]
      congr 1
      omega

omit [DecidableEq Node] in
/-- Terminal observations ignore the accumulated administrative counter. -/
@[simp] theorem outcome_addElapsed (id : Node) (extra : ℕ) (state : State network S) :
    outcome id (state.addElapsed extra) = outcome id state := rfl

/-- The serial FIFO policy and token passing have equal terminal observations at
corresponding horizons, including explicit abort and unfinished execution. -/
theorem outcome_runSerial
    (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (id : Node) (rounds : ℕ) (state : State network S) (hqueue : state.pending = []) :
    outcome id <$> runSerial impl rounds state = outcome id <$> runToken impl rounds state := by
  rw [runSerial_eq_runToken impl rounds state hqueue]
  simp [Functor.map_map]

end Interaction.Execution.ReactiveNetwork
