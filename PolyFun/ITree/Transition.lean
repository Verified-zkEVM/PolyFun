/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Transition
public import PolyFun.ITree.Basic
-- The adapter proof interprets the underlying finite free program.
import all PolyFun.PFunctor.Dynamical.DynComputation.Resumable
public import PolyFun.PFunctor.Dynamical.DynComputation.Resumable

/-!
# Deterministic evaluators as trees and returning machines

The tree exposes one silent step for each continuing transition. The machine
exposes one unit query for every transition, including the terminal observation,
so its chunk runner agrees exactly with `Control.Transition.run`. A completed
result occupies a separate state and is observed without further fuel.
-/

public section

namespace Control.Transition

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation

universe u

variable {S R : Type u}

/-- The empty event signature of a pure deterministic evaluator. -/
@[expose] def events : PFunctor.{0, 0} := ⟨Empty, Empty.elim⟩

/-- Unbounded behavior, with no external requests and one silent continuing step. -/
@[expose] def tree (next : Transition S R) : S → ITree events R :=
  ITree.corec fun state => match next state with
    | .inl result => .mk (.pure result) PEmpty.elim
    | .inr state' => .mk .step (fun _ => state')

/-- A unit query charges each transition, including the transition reporting a result. -/
@[expose] def toMachine (next : Transition S R) : DynComputation PFunctor.y.{u, u} S R :=
  DynComputation.ofStep (fun state : R ⊕ S => match state with
    | .inl result => .inl result
    | .inr state' => .inr ⟨PUnit.unit, fun _ => next state'⟩) Sum.inr

/-- Convert a transition result to the corresponding machine chunk. -/
@[expose] def toChunk : R ⊕ S → Chunk (R ⊕ S) R
  | .inl result => .done result
  | .inr state => .paused (.inr state)

/-- Unit transitions have a unique answer and introduce no external effect. -/
@[expose] def tickHandler : Handler Id PFunctor.y.{u, u} := fun _ => PUnit.unit

/-- The machine runner preserves the exact transition result or residual at every budget. -/
theorem runChunk_toMachine (next : Transition S R) (fuel : Nat) (state : S) :
    (toMachine next).runChunk tickHandler fuel (.inr state) = toChunk (run next fuel state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ n ih =>
      change (toMachine next).runChunk tickHandler n (next state) = _
      cases hs : next state with
      | inl result => simp only [run, hs]; cases n <;> rfl
      | inr state' => simpa only [run, hs] using ih state'

end Control.Transition
