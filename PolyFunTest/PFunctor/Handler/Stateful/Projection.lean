/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support.Instances
public import PolyFun.PFunctor.Handler.Stateful.Projection

/-!
# Projections of stateful handlers

Regression checks for `Handler.Stateful.IsProjection`. The decorated handler keeps a redundant
state component and answers from it; the answers agree with the base handler only on states
satisfying the invariant, so the examples include a state outside the invariant on which the two
runs differ.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.Handler.Stateful.Projection

open _root_.PFunctor

/-- One request, answered by a number. -/
abbrev counter : PFunctor.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- The base handler: answer with the count and increment it. -/
def counting : Handler.Stateful Option Nat counter :=
  fun _ n => some (n, n + 1)

/-- The decorated handler keeps `(n, d)` with `d` meant to be `2 * n`, answers `d / 2`, and
advances both components. -/
def halving : Handler.Stateful Option (Nat × Nat) counter :=
  fun _ s => some (s.2 / 2, (s.1 + 1, s.2 + 2))

/-- Forgetting the redundant component projects `halving` onto `counting` on the states where
`d = 2 * n`. -/
theorem halving_isProjection :
    Handler.Stateful.IsProjection halving counting (fun s => s.2 = 2 * s.1) Prod.fst where
  preserves_inv a s hs r hr := by
    have hr' : r = (s.2 / 2, (s.1 + 1, s.2 + 2)) := by
      simpa [halving, StateT.run] using (MonadAttach.mem_support_pure (m := Option)).1 hr
    subst hr'
    simp only
    omega
  map_run a s hs := by
    simp [halving, counting, StateT.run, hs]

/-- Ask for two answers and return both, in order. -/
def twoQueries : FreeM counter (Nat × Nat) :=
  FreeM.liftBind () fun a => FreeM.liftBind () fun b => pure (a, b)

/-- From a state in the invariant, the whole run projects onto the base run. -/
example : Prod.map id Prod.fst <$> halving.run twoQueries (3, 6) = counting.run twoQueries 3 :=
  halving_isProjection.run_eq twoQueries (3, 6) rfl

/-- The returned values agree from a state in the invariant. -/
example : Prod.fst <$> halving.run twoQueries (3, 6) = Prod.fst <$> counting.run twoQueries 3 :=
  halving_isProjection.fst_map_run_eq twoQueries (3, 6) rfl

example : counting.run twoQueries 3 = some ((3, 4), 5) := rfl

example : halving.run twoQueries (3, 6) = some ((3, 4), (5, 10)) := rfl

/-- Outside the invariant the decorated handler answers differently, so the invariant is
needed. -/
example : halving.run twoQueries (3, 9) = some ((4, 5), (5, 13)) := rfl

/-- Every handler projects onto itself along the identity. -/
example : Handler.Stateful.IsProjection counting counting (fun _ => True) id :=
  Handler.Stateful.IsProjection.refl counting

end PolyFunTest.PFunctor.Handler.Stateful.Projection
