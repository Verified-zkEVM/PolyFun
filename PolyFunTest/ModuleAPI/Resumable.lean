/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.PFunctor.Dynamical.DynComputation.History

/-! # Ordinary-import canaries for resumable execution across independent universes -/

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation

universe uA uB uState uInput uResult

example {p : PFunctor.{uA, uB}} {α : Type uInput} {β : Type uB}
    (machine : DynComputation.{uB} p α β) (handler : Handler Id p) (input : α) :
    machine.startChunk handler 0 input = pure (match machine.view (machine.init input) with
      | .inl value => .done value
      | .inr _ => .paused (machine.init input)) := machine.startChunk_zero handler input

example {p : PFunctor.{uA, uB}} {α : Type uInput} {β : Type uB}
    (machine : DynComputation.{uB} p α β) (handler : Handler Id p) (fuel : Nat) (value : β) :
    machine.continueChunk handler fuel (.done value) = pure (.done value) := by simp

example {p : PFunctor.{uA, uB}} {α : Type uInput} {β : Type uB} {m : Type uB → Type uResult}
    [Monad m] (machine : DynComputation.{uB} p α β) (handler : Handler m p) (fuel : Nat)
    (state : machine.State) :
    machine.continueChunk handler fuel (.paused state) = machine.runChunk handler fuel state := by
  simp

example {p : PFunctor.{uA, uB}} {α : Type uInput} {β : Type uB} {m : Type uB → Type uResult}
    [Monad m] (machine : DynComputation.{uB} p α β) (handler : Handler m p) (fuel : Nat)
    (input : α) :
    machine.startChunk handler fuel input = machine.runChunk handler fuel (machine.init input) := by
  simp

/-- Starting and continuing never reinitializes the machine or repeats an interpreted prefix. -/
example {p : PFunctor.{uA, uB}} {α : Type uInput} {β : Type uB} {m : Type uB → Type uResult}
    [Monad m] [LawfulMonad m] (machine : DynComputation.{uB} p α β) (handler : Handler m p)
    (first second : Nat) (input : α) :
    (machine.startChunk handler first input >>= machine.continueChunk handler second) =
      machine.startChunk handler (first + second) input :=
  machine.startChunk_continueChunk handler first second input

/-- Histories retain the runner's actual last chunk at independent syntax universes. -/
example {p : PFunctor.{uA, uB}} {α : Type uInput} {β : Type uResult}
    (machine : DynComputation.{uState} p α β) (fuel : Nat) (state : machine.State) :
    FreeM.map (fun history => history (Fin.last fuel)) (machine.unrollHistory fuel state) =
      machine.unrollChunk fuel state := machine.map_unrollHistory_last fuel state

example {p : PFunctor.{uA, uB}} {α : Type uInput} {β : Type uResult}
    (machine : DynComputation.{uState} p α β) {state : machine.State} {value : β}
    (h : machine.view state = .inl value) (fuel : Nat) :
    machine.unrollHistory fuel state = .pure (fun _ => .done value) :=
  machine.unrollHistory_of_view_return h fuel

example {p : PFunctor.{uA, uB}} {α : Type uInput} {β : Type uResult}
    (machine : DynComputation.{uState} p α β) (fuel : Nat) (state : machine.State) :
    FreeM.map Chunk.result (machine.unrollChunk fuel state) = machine.unroll fuel state :=
  machine.unrollChunk_result fuel state

example {p : PFunctor.{uA, uB}} {α : Type uInput} {β : Type uResult}
    (machine : DynComputation.{uState} p α β) (fuel : Nat) (value : β) :
    machine.resumeChunk fuel (.done value) = .pure (.done value) := by simp

example {p : PFunctor.{uA, uB}} {α : Type uInput} {β : Type uResult}
    (machine : DynComputation.{uState} p α β) (state : machine.State) :
    machine.unrollChunk 0 state = match machine.view state with
      | .inl value => .pure (.done value)
      | .inr _ => .pure (.paused state) := machine.unrollChunk_zero state

example {p : PFunctor.{uA, uB}} {α : Type uInput} {β : Type uResult}
    (machine : DynComputation.{uState} p α β) (first second : Nat) (state : machine.State) :
    (machine.unrollChunk first state >>= machine.resumeChunk second) =
      machine.unrollChunk (first + second) state := machine.unrollChunk_add first second state
