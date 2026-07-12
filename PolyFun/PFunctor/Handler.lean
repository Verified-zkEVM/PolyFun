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
consumed by `FreeM.mapM`; it does not depend on machines or dynamical systems.
-/

@[expose] public section

universe u v uA

namespace PFunctor

/-- A **handler** for the interface `q`: a monadic choice of direction at each
position (a Kleisli section of `q`). The deterministic case is a plain section
of the polynomial — `Handler Id q` is `Section q` unbundled — while a
probabilistic monad gives a randomized choice. -/
abbrev Handler (m : Type u → Type v) (q : PFunctor.{uA, u}) :=
  (a : q.A) → m (q.B a)

end PFunctor
