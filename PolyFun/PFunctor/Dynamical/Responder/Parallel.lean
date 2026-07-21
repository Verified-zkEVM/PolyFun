/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder
public import PolyFun.PFunctor.Parallel

/-!
# Parallel responders

The product of two responder states answers the one-or-both interface.  A
left-only query advances only the left state, a right-only query advances only
the right state, and a joint query advances both.  Thus `Responder.parallel`
is operationally different from the existing `DynSystem.tensor`, whose
interface admits only simultaneous operations.

The proof-relevant coalgebra lift lives in the display-owned sibling module
`PolyFun.PFunctor.Dynamical.Responder.Parallel.Display`.
-/

@[expose] public section

universe uA₁ uA₂ uA₃ uB uS₁ uS₂ uS₃

namespace PFunctor
namespace Responder

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
  {State₁ : Type uS₁} {State₂ : Type uS₂}

/-- Coproduct composition of responders.  Each query selects exactly one
responder, and the unselected state is frozen. -/
def sum (left : Responder State₁ P) (right : Responder State₂ Q) :
    Responder.{max uS₁ uS₂, max uA₁ uA₂, uB}
      (State₁ × State₂) (P + Q) :=
  Responder.mk'
    (fun state query => match query with
      | .inl a => left.answer state.1 a
      | .inr b => right.answer state.2 b)
    (fun state query => match query with
      | .inl a => (left.next state.1 a, state.2)
      | .inr b => (state.1, right.next state.2 b))

@[simp]
theorem sum_answer_inl (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂) (a : P.A) :
    (sum left right).answer state (.inl a) = left.answer state.1 a :=
  rfl

@[simp]
theorem sum_answer_inr (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂) (b : Q.A) :
    (sum left right).answer state (.inr b) = right.answer state.2 b :=
  rfl

@[simp]
theorem sum_next_inl (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂) (a : P.A) :
    (sum left right).next state (.inl a) =
      (left.next state.1 a, state.2) :=
  rfl

@[simp]
theorem sum_next_inr (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂) (b : Q.A) :
    (sum left right).next state (.inr b) =
      (state.1, right.next state.2 b) :=
  rfl

/-- Parallel composition of responders.  The inactive state is frozen in a
one-sided branch and both states advance in a joint branch. -/
def parallel (left : Responder State₁ P) (right : Responder State₂ Q) :
    Responder (State₁ × State₂) (P ∥ Q) :=
  Responder.mk'
    (fun state query => match query with
      | .left a => left.answer state.1 a
      | .right b => right.answer state.2 b
      | .both a b => (left.answer state.1 a, right.answer state.2 b))
    (fun state query => match query with
      | .left a => (left.next state.1 a, state.2)
      | .right b => (state.1, right.next state.2 b)
      | .both a b => (left.next state.1 a, right.next state.2 b))

@[simp]
theorem parallel_answer_left (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂) (a : P.A) :
    (parallel left right).answer state (.left a) = left.answer state.1 a :=
  rfl

@[simp]
theorem parallel_answer_right (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂) (b : Q.A) :
    (parallel left right).answer state (.right b) = right.answer state.2 b :=
  rfl

@[simp]
theorem parallel_answer_both (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂)
    (a : P.A) (b : Q.A) :
    (parallel left right).answer state (.both a b) =
      (left.answer state.1 a, right.answer state.2 b) :=
  rfl

@[simp]
theorem parallel_next_left (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂) (a : P.A) :
    (parallel left right).next state (.left a) =
      (left.next state.1 a, state.2) :=
  rfl

@[simp]
theorem parallel_next_right (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂) (b : Q.A) :
    (parallel left right).next state (.right b) =
      (state.1, right.next state.2 b) :=
  rfl

@[simp]
theorem parallel_next_both (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂)
    (a : P.A) (b : Q.A) :
    (parallel left right).next state (.both a b) =
      (left.next state.1 a, right.next state.2 b) :=
  rfl

/-! ## Symmetric-monoidal observation laws -/

/-- The unique responder over the zero interface. -/
def zero : Responder PUnit (0 : PFunctor.{uA₁, uB}) :=
  Responder.mk' (fun _ operation => PEmpty.elim operation)
    (fun _ operation => PEmpty.elim operation)

/-- Parallel answers commute under the explicit interface braiding and state
swap. -/
theorem parallel_answer_comm (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂)
    (operation : (P ∥ Q).A) :
    (parallel right left).answer (state.2, state.1)
        ((PFunctor.Equiv.parallelSumComm P Q).equivA operation) =
      (PFunctor.Equiv.parallelSumComm P Q).equivB operation
        ((parallel left right).answer state operation) := by
  cases operation <;> rfl

/-- Parallel next states commute under interface and state swaps. -/
theorem parallel_next_comm (left : Responder State₁ P)
    (right : Responder State₂ Q) (state : State₁ × State₂)
    (operation : (P ∥ Q).A) :
    (parallel right left).next (state.2, state.1)
        ((PFunctor.Equiv.parallelSumComm P Q).equivA operation) =
      ((parallel left right).next state operation).swap := by
  cases operation <;> rfl

/-- Parallel answers associate under the explicit interface associator and
the corresponding reassociation of states and answers. -/
theorem parallel_answer_assoc
    {R : PFunctor.{uA₃, uB}} {State₃ : Type uS₃}
    (left : Responder State₁ P) (middle : Responder State₂ Q)
    (right : Responder State₃ R)
    (state : (State₁ × State₂) × State₃)
    (operation : ((P ∥ Q) ∥ R).A) :
    (parallel left (parallel middle right)).answer
        (state.1.1, (state.1.2, state.2))
        ((PFunctor.Equiv.parallelSumAssoc P Q R).equivA operation) =
      (PFunctor.Equiv.parallelSumAssoc P Q R).equivB operation
        ((parallel (parallel left middle) right).answer state operation) := by
  cases operation with
  | left operation => cases operation <;> rfl
  | right operation => rfl
  | both operation rightOperation => cases operation <;> rfl

/-- Parallel next states associate under the explicit interface and state
associators. -/
theorem parallel_next_assoc
    {R : PFunctor.{uA₃, uB}} {State₃ : Type uS₃}
    (left : Responder State₁ P) (middle : Responder State₂ Q)
    (right : Responder State₃ R)
    (state : (State₁ × State₂) × State₃)
    (operation : ((P ∥ Q) ∥ R).A) :
    (parallel left (parallel middle right)).next
        (state.1.1, (state.1.2, state.2))
        ((PFunctor.Equiv.parallelSumAssoc P Q R).equivA operation) =
      let next := (parallel (parallel left middle) right).next state operation
      (next.1.1, (next.1.2, next.2)) := by
  cases operation with
  | left operation => cases operation <;> rfl
  | right operation => rfl
  | both operation rightOperation => cases operation <;> rfl

theorem parallel_answer_zero_right (left : Responder State₁ P)
    (state : State₁) (operation : (P ∥ (0 : PFunctor.{uA₂, uB})).A) :
    left.answer state
        ((PFunctor.Equiv.parallelSumZero P).equivA operation) =
      (PFunctor.Equiv.parallelSumZero P).equivB operation
        ((parallel left Responder.zero).answer (state, PUnit.unit) operation) := by
  cases operation with
  | left operation => rfl
  | right operation => exact PEmpty.elim operation
  | both leftOperation rightOperation => exact PEmpty.elim rightOperation

theorem parallel_next_zero_right (left : Responder State₁ P)
    (state : State₁) (operation : (P ∥ (0 : PFunctor.{uA₂, uB})).A) :
    ((parallel left Responder.zero).next (state, PUnit.unit) operation).1 =
      left.next state
        ((PFunctor.Equiv.parallelSumZero P).equivA operation) := by
  cases operation with
  | left operation => rfl
  | right operation => exact PEmpty.elim operation
  | both leftOperation rightOperation => exact PEmpty.elim rightOperation

theorem parallel_answer_zero_left (right : Responder State₂ Q)
    (state : State₂) (operation : ((0 : PFunctor.{uA₁, uB}) ∥ Q).A) :
    right.answer state
        ((PFunctor.Equiv.zeroParallelSum Q).equivA operation) =
      (PFunctor.Equiv.zeroParallelSum Q).equivB operation
        ((parallel Responder.zero right).answer (PUnit.unit, state) operation) := by
  cases operation with
  | left operation => exact PEmpty.elim operation
  | right operation => rfl
  | both leftOperation rightOperation => exact PEmpty.elim leftOperation

theorem parallel_next_zero_left (right : Responder State₂ Q)
    (state : State₂) (operation : ((0 : PFunctor.{uA₁, uB}) ∥ Q).A) :
    ((parallel Responder.zero right).next (PUnit.unit, state) operation).2 =
      right.next state
        ((PFunctor.Equiv.zeroParallelSum Q).equivA operation) := by
  cases operation with
  | left operation => exact PEmpty.elim operation
  | right operation => rfl
  | both leftOperation rightOperation => exact PEmpty.elim leftOperation

end Responder
end PFunctor
