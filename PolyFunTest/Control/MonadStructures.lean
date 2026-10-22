/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Dijkstra
public import PolyFun.Control.Monad.Graded
public import PolyFun.Control.Monad.Relative
public import PolyFun.Control.Monad.AlternativeLift
public import PolyFun.Control.Lawful.MonadControl
public import PolyFun.Control.Lawful.MonadFunctor
public import PolyFun.Control.Lawful.MonadState

/-!
# Ordered, graded, Dijkstra and relative monads, and lawful lifting classes

Smoke tests for the structures of `PolyFun.Control.Monad.{Ordered, Dijkstra, Graded, Relative,
Relation, AlternativeLift}` and `PolyFun.Control.Lawful`: the trivial grading and the group
grading as an indexed monad, the graph of a lift as a monad relation and the Dijkstra monad it
presents, the free Dijkstra monad, the discrete ordered monad, the lifts of `guard` and
`MonadState.set`, and the reflexive lawful monad functor.
-/

@[expose] public section

namespace PolyFunTest.MonadStructures

open scoped OrderedMonad

/- The trivial grading of `Option` binds as `Option` does. -/
example : (gbind (M := Unit) (F := fun _ => Option) (i := ()) (j := ()) (some 1)
    (fun n => some (n + 1)) : Option Nat) = some 2 := rfl

/- A graded monad over a group is an indexed monad. -/
example {G : Type} [Group G] {F : G → Type → Type} [GradedMonad G F] :
    IndexedMonad G (GradedMonad.IxF F) :=
  inferInstance

/- The graph of the reflexive lift relates a computation to itself. -/
example : monadRel (pure 1 : Option Nat) (some 1) := rfl

/- A lawful lift presents a Dijkstra monad whose computations at `na` lift to `na`. -/
example : (dPure (w := Option) (d := fun na => { ma : Option _ // monadLift ma = na }) 3).1 =
    some 3 := rfl

/- A free Dijkstra computation spells its specification as binds ending in `pure`. -/
example : FreeDijkstra Option (some 1 >>= fun n => pure (n + 1)) :=
  .roll (some 1) fun n => .pure (n + 1)

/- Free Dijkstra computations sequence through the Dijkstra monad structure. -/
example : FreeDijkstra Option ((pure 1 : Option Nat) >>= fun n => pure (n + 1)) :=
  FreeDijkstra.pure 1 >>=ᵈ fun n => FreeDijkstra.pure (n + 1)

open OrderedMonad.Discrete in
/- The discrete order makes every monad ordered. -/
example : (pure 1 : Option Nat) ≤ₘ pure 1 := le_refl _

/- `guard` lifts along a lawful alternative lift. -/
example (p : Prop) [Decidable p] :
    (monadLift (guard p : Option Unit) : StateT Nat Option Unit) = guard p := by
  simp

/- `MonadState.set` rewrites to `MonadStateOf.set`. -/
example : (MonadState.set 3 : StateT Nat Id PUnit) = MonadStateOf.set 3 := by
  simp

/- The reflexive closure of `MonadFunctor` is lawful. -/
example : LawfulMonadFunctorT Option Option := inferInstance

end PolyFunTest.MonadStructures
