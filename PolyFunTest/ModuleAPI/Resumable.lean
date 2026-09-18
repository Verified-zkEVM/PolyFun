/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.PFunctor.Dynamical.DynComputation.Resumable

/-! # Ordinary-import canaries for resumable execution across independent universes -/

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation

universe uA uB uState uInput uResult

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
