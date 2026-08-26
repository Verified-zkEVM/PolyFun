/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Basic

/-!
# Monadic Handlers for Polynomial Functors

A `PFunctor.Handler m q` chooses a direction of `q` at each position, with the
choice interpreted in the type constructor `m`. This is the generic interface
consumed by `FreeM.liftM`; it does not depend on machines or dynamical systems.
In particular, taking `m := StateT σ n` threads one shared runtime state through
every handled position. That ambient state is distinct from a dynamical
system's private operational state.
-/

@[expose] public section

universe u v w uA uI

namespace PFunctor

/-- A **handler** for the interface `q`: a monadic choice of direction at each
position (a Kleisli section of `q`). With `m := Id` this is an ordinary
dependent choice of one direction at every position, while a probabilistic
monad gives a randomized choice. -/
abbrev Handler (m : Type u → Type v) (q : PFunctor.{uA, u}) :=
  (a : q.A) → m (q.B a)

namespace Handler

/-- Postcompose every answer computation of a handler by a polymorphic map
between target type constructors. No monad laws are needed for this basic
change-of-target operation. -/
def mapTarget {m : Type u → Type v} {n : Type u → Type w}
    {q : PFunctor.{uA, u}} (transform : ∀ {α : Type u}, m α → n α)
    (handler : PFunctor.Handler m q) : PFunctor.Handler n q :=
  fun position => transform (handler position)

@[simp] theorem mapTarget_apply {m : Type u → Type v} {n : Type u → Type w}
    {q : PFunctor.{uA, u}} (transform : ∀ {α : Type u}, m α → n α)
    (handler : PFunctor.Handler m q) (position : q.A) :
    mapTarget transform handler position = transform (handler position) :=
  rfl

@[simp] theorem mapTarget_id {m : Type u → Type v}
    {q : PFunctor.{uA, u}} (handler : PFunctor.Handler m q) :
    mapTarget (fun computation => computation) handler = handler :=
  rfl

theorem mapTarget_comp {m : Type u → Type v} {n : Type u → Type w}
    {o : Type u → Type uI} {q : PFunctor.{uA, u}}
    (second : ∀ {α : Type u}, n α → o α)
    (first : ∀ {α : Type u}, m α → n α)
    (handler : PFunctor.Handler m q) :
    mapTarget second (mapTarget first handler) =
      mapTarget (fun computation => second (first computation)) handler :=
  rfl

/-- An effectful stateful handler for `q`: on each position it reads a state,
performs effects in `m`, and returns a direction together with the next state.

This is a transparent name for `Handler (StateT S m) q`, so it introduces no
new data or laws. At `m := Id` it is the pure Kleisli--Mealy presentation used
by `Responder.equivStateHandler`. -/
abbrev Stateful (m : Type u → Type v) (S : Type u)
    (q : PFunctor.{uA, u}) :=
  Handler (StateT S m) q

/-- Combine monadic handlers for an indexed family into a handler for its
indexed coproduct. -/
def sigma {I : Type uI} {P : I → PFunctor.{uA, u}} {m : Type u → Type v}
    (f : (i : I) → PFunctor.Handler m (P i)) : PFunctor.Handler m (PFunctor.sigma P) :=
  fun a => f a.1 a.2

@[simp]
theorem sigma_apply {I : Type uI} {P : I → PFunctor.{uA, u}} {m : Type u → Type v}
    (f : (i : I) → PFunctor.Handler m (P i)) (i : I) (a : (P i).A) : sigma f ⟨i, a⟩ = f i a :=
  rfl

end Handler

end PFunctor
