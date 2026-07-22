/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder.Reindex

/-!
# Stateful handler examples

Regression canaries for effectful execution and free-handler reindexing. The
examples use distinguishable answers and state updates, and include a failing
effect, so swapping answer/state components or dropping the base effect changes
an observed result.
-/

@[expose] public section

namespace PFunctor.Handler.Stateful.Examples

/-- Two query positions, both answered by natural numbers. -/
abbrev Q : PFunctor.{0, 0} := monomial Bool Nat

/-- On `true`, answer with `state + 10` and advance by one; on `false`, answer
with `state + 20` and advance by two. -/
def answerAndAdvance : Handler.Stateful Option Nat Q :=
  fun query state =>
    Bool.rec (some (state + 20, state + 2))
      (some (state + 10, state + 1)) query

/-- Query both branches and return both distinguishable answers. -/
def twoQueries : FreeM Q (Nat × Nat) :=
  FreeM.liftBind true fun first =>
    FreeM.liftBind false fun second =>
      pure (first, second)

example : answerAndAdvance.run twoQueries 3 = some ((13, 24), 6) := by
  rfl

/-- A handler whose `false` branch fails in the base effect. -/
def failOnFalse : Handler.Stateful Option Nat Q :=
  fun query state =>
    Bool.rec none (some (state + 10, state + 1)) query

example : failOnFalse.run twoQueries 3 = none := by
  rfl

/-- A stateless effectful handler for the lifting canary. -/
def constantAnswer : Handler Option Q :=
  fun query => Prod.fst <$> (answerAndAdvance query).run 0

/-- Lifting preserves both the base effect and the state. -/
example : ((Handler.Stateful.lift constantAnswer :
    Handler.Stateful Option Nat Q) true).run 7 = some ((10 : Nat), 7) := by
  rfl

/-- A source query implemented by the two-query target program. -/
abbrev P : PFunctor.{0, 0} := monomial PUnit (Nat × Nat)

def implementP : Handler (FreeM Q) P :=
  fun _ => twoQueries

/-- Reindexing exposes the same effectful answer and final state as running the
implementing target program directly. -/
example : (answerAndAdvance.reindex implementP) PUnit.unit 3 =
    some ((13, 24), 6) := by
  rfl

/-- The execution-fusion law is usable through the public API. -/
example (program : FreeM P Nat) (state : Nat) :
    (answerAndAdvance.reindex implementP).run program state =
      answerAndAdvance.run (program.liftM implementP) state := by
  rw [run_reindex]

example : answerAndAdvance.reindex (Handler.id Q) = answerAndAdvance := by
  rw [reindex_id]

/-- The composition theorem uses categorical order: `implementP` runs first,
then the identity implementation of `Q`. -/
example :
    (answerAndAdvance.reindex (Handler.id Q)).reindex implementP =
      answerAndAdvance.reindex ((Handler.id Q).comp implementP) := by
  rw [reindex_comp]

/-- Pure responders inhabit exactly the `Id` specialization of the generalized
effectful stateful-handler interface. -/
example (R : Responder Nat Q) : Handler.Stateful Id Nat Q :=
  R.toStateHandler

example (R : Responder Nat Q) (program : FreeM Q Nat) (state : Nat) :
    R.runFree program state = R.toStateHandler.run program state := by
  rw [Responder.runFree_eq_statefulRun]

/-- Query positions may live in a higher universe than directions and state. -/
example : Handler.Stateful Option Nat (monomial (Type 0) Nat) :=
  fun _ state => some (state, state + 1)

end PFunctor.Handler.Stateful.Examples
