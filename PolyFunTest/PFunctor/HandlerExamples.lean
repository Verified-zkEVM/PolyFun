/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Handler

/-!
# Examples for Monadic Polynomial-Functor Handlers

Regression tests for the lightweight, universe-polymorphic handler interface.
-/

@[expose] public section

universe u v w

namespace PFunctor

/-- Position, direction, and effect universes remain independent. -/
example {q : PFunctor.{u, v}} {m : Type v → Type w}
    (h : (a : q.A) → m (q.B a)) : Handler m q := h

end PFunctor
