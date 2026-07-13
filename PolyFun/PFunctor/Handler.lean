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

universe u v uA

namespace PFunctor

/-- A **handler** for the interface `q`: a monadic choice of direction at each
position (a Kleisli section of `q`). With `m := Id` this is an ordinary
dependent choice of one direction at every position, while a probabilistic
monad gives a randomized choice. -/
abbrev Handler (m : Type u → Type v) (q : PFunctor.{uA, u}) :=
  (a : q.A) → m (q.B a)

end PFunctor
