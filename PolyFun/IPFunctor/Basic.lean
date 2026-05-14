/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Basic

/-!
# Indexed (State-Dependent) Polynomial Functors

This file defines `IPFunctor I`, a generalization of `PFunctor` parameterized by an ambient
state type `I`. The available head shapes and the resulting child types are both gated on the
current state `s : I`, and a `st` function specifies how the state evolves after a step.

This is useful for modelling protocols whose available actions depend on a phase or session
type — for example, a multi-phase game where the oracles change after the adversary calls a
challenge oracle, or two parties handing off control during execution.

The state-indexed free monad on an `IPFunctor` is defined in
[`PolyFun/IPFunctor/Free/Basic.lean`](Free/Basic.lean), and the two-indexed variant tracking
both pre- and post-state — which carries an `IndexedMonad` instance — lives in
[`PolyFun/IPFunctor/Free/Indexed.lean`](Free/Indexed.lean).

When `I` has at most one element, `IPFunctor I` reduces to an ordinary `PFunctor` via
`IPFunctor.toPFunctor`, and the indexed free monad collapses to `PFunctor.FreeM`; the
forgetful direction is `IPFunctor.FreeM.erase`.
-/

@[expose] public section

universe uI uA uB

/-- Indexed version of `PFunctor`, with some global state of type `I` gating the available shapes.
Given a state `s : I`, `A s` are the available shapes and `B s` maps `A s` to output types.
The function `st` specifies how the state transitions on an input/output pair. -/
structure IPFunctor (I : Type uI) where
  /-- The head type at each state. -/
  A : I → Type uA
  /-- The child family of types, dependent on the current state and chosen shape. -/
  B : (s : I) → A s → Type uB
  /-- State transition function: given the current state, the chosen shape, and the response,
  return the new state. -/
  st : (s : I) → (a : A s) → B s a → I

namespace IPFunctor

variable {I : Type uI}

/-- Applying `P` to an object of `Type` at state `s`. -/
@[coe]
def Obj (P : IPFunctor I) (α : Type*) (s : I) : Type _ :=
  Σ x : P.A s, P.B s x → α

instance : CoeFun (IPFunctor I) (fun _ => Type* → I → Type _) where
  coe := Obj

/-- The zero `IPFunctor`: no shapes are available at any state. -/
instance (I : Type uI) : Zero (IPFunctor.{uI, uA, uB} I) where
  zero := { A _ := PEmpty, B _ _ := PEmpty, st _ _ := PEmpty.elim }

/-- The unit `IPFunctor`: a single trivial shape at each state, with no continuation. -/
instance (I : Type uI) : One (IPFunctor.{uI, uA, uB} I) where
  one := { A _ := PUnit, B _ _ := PEmpty, st _ _ := PEmpty.elim }

instance : Inhabited (IPFunctor I) := ⟨0⟩

/-- View an `IPFunctor` as a `PFunctor` by fixing the state to `default`. The `st` transition
information is discarded. -/
@[reducible, inline]
def toPFunctor [Inhabited I] (P : IPFunctor I) : PFunctor where
  A := P.A default
  B := P.B default

@[simp] lemma toPFunctor_zero [Inhabited I] : (0 : IPFunctor I).toPFunctor = 0 := rfl

@[simp] lemma toPFunctor_one [Inhabited I] : (1 : IPFunctor I).toPFunctor = 1 := rfl

end IPFunctor

/-- An `IPFunctor` has *deterministic transitions* when `P.st s a b` is
independent of the response `b`. Equivalently, `(fun b => P.st s a b)`
is a constant function for every shape `a`.

This is the structural condition that lets `liftA`-style steps of the
single-index free monad `IPFunctor.FreeM` land at a uniquely determined
post-state — see [`PolyFun/IPFunctor/Notation/Deterministic.lean`](Notation/Deterministic.lean)
for `do`-notation that takes advantage of it. -/
class IPFunctor.DeterministicTransitions {I : Type uI}
    (P : IPFunctor.{uI, uA, uB} I) where
  /-- The (unique) post-state after taking shape `a` at state `s`. -/
  next : (s : I) → P.A s → I
  /-- `P.st s a b` agrees with `next s a` for every response `b`. -/
  spec : ∀ s a b, P.st s a b = next s a
