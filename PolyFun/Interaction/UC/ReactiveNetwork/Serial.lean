/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ReactiveNetwork

/-!
# Serial comparison of token passing and FIFO delivery

With no outstanding FIFO traffic, a local activation followed by a delivery activation
has the same residual machines, mailboxes, shared state, output, and control holder as one
token activation. The FIFO round consumes one additional activation, including when there
is nothing to deliver. This comparison names a serialized policy; it does not identify
arbitrary FIFO schedules with token passing.
-/

public section

namespace Interaction.UC.ReactiveNetwork

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

end Interaction.UC.ReactiveNetwork
