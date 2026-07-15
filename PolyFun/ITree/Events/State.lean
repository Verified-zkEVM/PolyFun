/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Sim.Defs

/-! # State events

A standard event signature for stateful computations. The polynomial functor
`StateE σ` has two events:

* `get` — returns the current state of type `σ`.
* `put s` — replaces the current state with `s`, returning `PUnit`.

`interpState` eliminates state events from a tree over `StateE σ + E`,
threading an initial state through the computation and leaving every external
`E`-event visible. `runState` is its conventional runner alias. Both use a
direct productive corecursor, so their computation rules are exact equalities
rather than merely weak bisimulations.

Coq references:

* `Events/State.v` — `stateE`, `interp_state`, `run_state`.
-/

@[expose] public section

universe uσ uEA uα

namespace ITree

/-- The two state events. `Shape.get` returns the current state, `Shape.put`
replaces it. -/
inductive StateE.Shape (σ : Type uσ) : Type uσ where
  /-- Read the current state. -/
  | get : StateE.Shape σ
  /-- Overwrite the current state with `s : σ`. -/
  | put (s : σ) : StateE.Shape σ

/-- State events over a state space `σ : Type u`. The answer types are:

* for `get` — `σ` (the value read);
* for `put _` — `PUnit` (the unit return of an assignment).
-/
def StateE (σ : Type uσ) : PFunctor.{uσ, uσ} where
  A := StateE.Shape σ
  B
    | .get => σ
    | .put _ => PUnit.{uσ + 1}

namespace StateE

variable {σ : Type uσ}

/-- Issue a `get` event, returning the current state. -/
def get : ITree (StateE σ) σ := lift (F := StateE σ) Shape.get

/-- Issue a `put` event, returning `PUnit`. -/
def put (s : σ) : ITree (StateE σ) PUnit.{uσ + 1} :=
  lift (F := StateE σ) (Shape.put s)

end StateE

/-! ## State interpretation -/

/-- One productive layer of state interpretation. The corecursor state stores
the current state together with the source tree. State operations become
silent steps, while external events remain visible. -/
def interpStateStep {σ : Type uσ} {E : PFunctor.{uEA, uσ}}
    {α : Type uα}
    (st : σ × ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α) :
    (Poly E (σ × α)).Obj
      (σ × ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α) :=
  match shape' st.2 with
  | ⟨.pure r, _⟩ => ⟨.pure (st.1, r), PEmpty.elim⟩
  | ⟨.step, c⟩ => ⟨.step, fun _ => (st.1, c PUnit.unit)⟩
  | ⟨.query (.inl .get), c⟩ =>
      ⟨.step, fun _ => (st.1, c st.1)⟩
  | ⟨.query (.inl (.put s')), c⟩ =>
      ⟨.step, fun _ => (s', c PUnit.unit)⟩
  | ⟨.query (.inr e), c⟩ =>
      ⟨.query e, fun b => (st.1, c b)⟩

/-- Interpret state operations in `t`, starting from `s`, and return the final
state together with the computation result. External events remain visible.

The direction universe of `E` agrees with that of `σ` only because the source
signature uses the current homogeneous `PFunctor.sum`. The final result
universe is independent. -/
def interpState {σ : Type uσ} {E : PFunctor.{uEA, uσ}}
    {α : Type uα}
    (t : ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α)
    (s : σ) : ITree E (σ × α) :=
  PFunctor.M.corec interpStateStep (s, t)

/-- Conventional runner name for `interpState`. -/
def runState {σ : Type uσ} {E : PFunctor.{uEA, uσ}}
    {α : Type uα}
    (t : ITree (StateE σ + E : PFunctor.{max uσ uEA, uσ}) α)
    (s : σ) : ITree E (σ × α) :=
  interpState t s

end ITree
