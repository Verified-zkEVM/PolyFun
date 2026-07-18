/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder.Parallel.Behavior
public import PolyFun.PFunctor.Free.Parallel

/-!
# Execution and reindexing laws for parallel responders

These laws identify the operational parallel constructions: executing a
one-sided embedding freezes the inactive responder state, while executing
`FreeM.parallel` is exactly the pair of the two component executions.
Consequently, responder reindexing commutes with parallel handlers.
-/

@[expose] public section

universe uA₁ uA₂ uA₃ uA₄ uB uS₁ uS₂ uE uF

namespace PFunctor
namespace Responder

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
  {State₁ : Type uS₁} {State₂ : Type uS₂}

/-- Coproduct composition is the one-sided restriction of parallel
composition along the canonical lens from `P + Q` to `P ∥ Q`. -/
theorem sum_eq_reindex_parallel
    (left : Responder State₁ P) (right : Responder State₂ Q) :
    sum left right =
      reindex (Handler.ofLens (Lens.sumToParallel P Q))
        (parallel left right) := by
  apply Responder.ext
  · intro state query
    cases query <;> rfl
  · intro state query
    cases query <;> rfl

/-- Running a left-embedded program advances only the left responder. -/
theorem runFree_left (left : Responder State₁ P)
    (right : Responder State₂ Q) {E : Type uE}
    (program : FreeM P E) (leftState : State₁) (rightState : State₂) :
    (parallel left right).runFree (FreeM.left (Q := Q) program)
        (leftState, rightState) =
      let result := left.runFree program leftState
      (result.1, (result.2, rightState)) := by
  induction program generalizing leftState with
  | pure value => rfl
  | lift_bind query next ih =>
      exact ih (left.answer leftState query) (left.next leftState query)

/-- Running a right-embedded program advances only the right responder. -/
theorem runFree_right (left : Responder State₁ P)
    (right : Responder State₂ Q) {E : Type uE}
    (program : FreeM Q E) (leftState : State₁) (rightState : State₂) :
    (parallel left right).runFree (FreeM.right (P := P) program)
        (leftState, rightState) =
      let result := right.runFree program rightState
      (result.1, (leftState, result.2)) := by
  induction program generalizing rightState with
  | pure value => rfl
  | lift_bind query next ih =>
      exact ih (right.answer rightState query) (right.next rightState query)

/-- Running lockstep free programs against parallel responders equals the pair
of the component runs, including their final states. -/
theorem runFree_parallel (left : Responder State₁ P)
    (right : Responder State₂ Q) {E : Type uE} {F : Type uF}
    (leftProgram : FreeM P E) (rightProgram : FreeM Q F)
    (leftState : State₁) (rightState : State₂) :
    (parallel left right).runFree
        (FreeM.parallel leftProgram rightProgram) (leftState, rightState) =
      let leftResult := left.runFree leftProgram leftState
      let rightResult := right.runFree rightProgram rightState
      ((leftResult.1, rightResult.1), (leftResult.2, rightResult.2)) := by
  induction leftProgram generalizing leftState rightState rightProgram with
  | pure leftValue =>
      induction rightProgram generalizing rightState with
      | pure rightValue => rfl
      | lift_bind query next ih =>
          exact ih (right.answer rightState query) (right.next rightState query)
  | lift_bind query next ih =>
      cases rightProgram with
      | pure rightValue =>
          exact ih (left.answer leftState query) (FreeM.pure rightValue)
            (left.next leftState query) rightState
      | liftBind rightQuery rightNext =>
          exact ih (left.answer leftState query)
            (rightNext (right.answer rightState rightQuery))
            (left.next leftState query) (right.next rightState rightQuery)

/-- Reindexing parallel responders by parallel handlers is componentwise. -/
theorem reindex_parallel
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (leftHandler : Handler (FreeM P) R)
    (rightHandler : Handler (FreeM Q) V)
    (left : Responder State₁ P) (right : Responder State₂ Q) :
    reindex (Handler.parallel leftHandler rightHandler)
        (parallel left right) =
      parallel (reindex leftHandler left) (reindex rightHandler right) := by
  apply Responder.ext
  · intro state query
    cases query with
    | left operation =>
        exact congrArg Prod.fst
          (runFree_left left right (leftHandler operation) state.1 state.2)
    | right operation =>
        exact congrArg Prod.fst
          (runFree_right left right (rightHandler operation) state.1 state.2)
    | both leftOperation rightOperation =>
        exact congrArg Prod.fst
          (runFree_parallel left right (leftHandler leftOperation)
            (rightHandler rightOperation) state.1 state.2)
  · intro state query
    cases query with
    | left operation =>
        exact congrArg Prod.snd
          (runFree_left left right (leftHandler operation) state.1 state.2)
    | right operation =>
        exact congrArg Prod.snd
          (runFree_right left right (rightHandler operation) state.1 state.2)
    | both leftOperation rightOperation =>
        exact congrArg Prod.snd
          (runFree_parallel left right (leftHandler leftOperation)
            (rightHandler rightOperation) state.1 state.2)

end Responder
end PFunctor
