/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support
public import PolyFun.PFunctor.Handler.Stateful

/-!
# Projections of stateful handlers

`Stateful.IsProjection decorated base inv proj` says that the state map
`proj : S → T` projects the stateful handler `decorated` onto `base` on the
states satisfying `inv`. From an `inv` state, every possible next state of a
`decorated` step satisfies `inv` again, and projecting the step's state gives
the step of `base` from the projected state. Possible results are read through
`MonadAttach.support` in the base monad `m`.

`IsProjection.run_eq` lifts the one-step condition to every finite program.
`Stateful.run_map_eq_of_apply_map_eq` is the special case with the trivial
invariant, which needs no `MonadAttach` structure.

A typical use adds bookkeeping to a handler, such as a log or a counter, and
recovers the original handler by forgetting the bookkeeping. The invariant
records how the bookkeeping relates to the original state.
-/

public section

universe u v uA

namespace PFunctor
namespace Handler
namespace Stateful

open MonadAttach

variable {m : Type u → Type v} [Monad m] [MonadAttach m] {S T : Type u}
variable {P : PFunctor.{uA, u}}

/-- The state map `proj` projects `decorated` onto `base` on the states
satisfying `inv`. Every possible step of `decorated` from an `inv` state stays in
`inv`, and projecting its state gives the step of `base` from the projected
state. -/
structure IsProjection (decorated : Stateful m S P) (base : Stateful m T P)
    (inv : S → Prop) (proj : S → T) : Prop where
  /-- Every possible next state of a step from an `inv` state satisfies `inv`. -/
  preserves_inv : ∀ a s, inv s → ∀ r ∈ support ((decorated a).run s), inv r.2
  /-- Projecting the state of a step from an `inv` state gives the step of `base`. -/
  map_run : ∀ a s, inv s →
    Prod.map _root_.id proj <$> (decorated a).run s = (base a).run (proj s)

namespace IsProjection

variable {decorated : Stateful m S P} {base : Stateful m T P}
variable {inv : S → Prop} {proj : S → T}

/-- A projection of one step is a projection of every finite program: running
from an `inv` state and projecting the final state is running `base` from the
projected state. -/
theorem run_eq [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    (h : IsProjection decorated base inv proj) {α : Type u} :
    ∀ (x : FreeM P α) (s : S), inv s →
      Prod.map _root_.id proj <$> decorated.run x s = base.run x (proj s)
  | .pure a, s, _ => by simp
  | .liftBind a k, s, hs => by
    rw [run_liftBind, run_liftBind, map_bind, ← h.map_run a s hs, bind_map_left]
    exact bind_congr_of_forall_mem_support _ fun r hr =>
      run_eq h (k r.1) r.2 (h.preserves_inv a s hs r hr)

/-- The value-only form of `run_eq`: from an `inv` state, `decorated` and `base`
return the same values. -/
theorem fst_map_run_eq [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    (h : IsProjection decorated base inv proj) {α : Type u} (x : FreeM P α) (s : S)
    (hs : inv s) :
    Prod.fst <$> decorated.run x s = Prod.fst <$> base.run x (proj s) := by
  rw [← h.run_eq x s hs, Functor.map_map]
  rfl

/-- With the trivial invariant, a projection is a state map commuting with every
step. -/
theorem of_map_run
    (hproj : ∀ a s, Prod.map _root_.id proj <$> (decorated a).run s = (base a).run (proj s)) :
    IsProjection decorated base (fun _ => True) proj where
  preserves_inv _ _ _ _ _ := trivial
  map_run a s _ := hproj a s

/-- The identity state map projects every handler onto itself. -/
theorem refl [LawfulMonad m] (h : Stateful m S P) :
    IsProjection h h (fun _ => True) _root_.id :=
  of_map_run fun a s => by simp [Prod.map_id]

end IsProjection

end Stateful
end Handler
end PFunctor
