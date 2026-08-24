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

/-! ## Coproduct transparency -/

set_option linter.tacticCheckInstances true

#guard_msgs in
example {P Q R : PFunctor.{u, v}} (h : Handler Id ((P + Q) + R)) (q : Q.A)
    (consume : Q.B q → Nat) :
    consume (h (.inl (.inr q))) = consume (h (.inl (.inr q))) := by
  rfl

#guard_msgs in
example {P Q R : PFunctor.{u, v}} (h : Handler Id ((P + Q) + R)) (r : R.A)
    (consume : R.B r → Nat) :
    consume (h (.inr r)) = consume (h (.inr r)) := by
  rfl

end PFunctor
