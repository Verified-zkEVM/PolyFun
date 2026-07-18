/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder.Behavior
public import PolyFun.PFunctor.Dynamical.Responder.Parallel.Display

/-!
# State-free parallel responder behavior

Parallel state-free behavior is obtained canonically by running the parallel
product of the two terminal responders from the pair of input behaviors.
Verified parallel behavior is the corresponding terminal semantics of
`Responder.parallelCoalgebra`.  This presentation makes the one-sided
state-freezing behavior explicit; the construction is not merely the lax
tensor map on cofree polynomials.
-/

@[expose] public section

universe uA₁ uA₂ uB uC₁ uD₁ uC₂ uD₂

namespace PFunctor
namespace Responder

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}

/-- Coproduct composition of state-free responder behaviors.  A query selects
one component and leaves the other component unchanged. -/
def sumBehavior
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB})) :
    PFunctor.M (PFunctor.sum P Q ⊸ X.{max uA₁ uA₂, uB}) :=
  (Responder.sum (Responder.terminal (P := P))
    (Responder.terminal (P := Q))).behavior (left, right)

/-- The behavior of a state-presented coproduct responder is the coproduct
composition of the component behaviors. -/
theorem sum_behavior
    {State₁ : Type uC₁} {State₂ : Type uC₂}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (state : State₁ × State₂) :
    (Responder.sum left right).behavior state =
      sumBehavior (left.behavior state.1) (right.behavior state.2) := by
  let terminalSum := Responder.sum
    (Responder.terminal (P := P)) (Responder.terminal (P := Q))
  change (Responder.sum left right).behavior state =
    terminalSum.behavior (left.behavior state.1, right.behavior state.2)
  symm
  apply behavior_eq_of_responderMap terminalSum (Responder.sum left right)
    (fun current => (left.behavior current.1, right.behavior current.2))
  · intro current operation
    cases operation <;> simp [terminalSum]
  · intro current operation
    cases operation <;> simp [terminalSum]

@[simp]
theorem sumBehavior_answer_inl
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB})) (a : P.A) :
    (Responder.terminal (P := PFunctor.sum P Q)).answer
        (sumBehavior left right) (.inl a) =
      (Responder.terminal (P := P)).answer left a := by
  change
    (Responder.terminal (P := PFunctor.sum P Q)).answer
      ((Responder.sum (Responder.terminal (P := P))
        (Responder.terminal (P := Q))).behavior (left, right)) (.inl a) = _
  rw [terminal_answer_behavior]
  rfl

@[simp]
theorem sumBehavior_answer_inr
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB})) (b : Q.A) :
    (Responder.terminal (P := PFunctor.sum P Q)).answer
        (sumBehavior left right) (.inr b) =
      (Responder.terminal (P := Q)).answer right b := by
  change
    (Responder.terminal (P := PFunctor.sum P Q)).answer
      ((Responder.sum (Responder.terminal (P := P))
        (Responder.terminal (P := Q))).behavior (left, right)) (.inr b) = _
  rw [terminal_answer_behavior]
  rfl

@[simp]
theorem sumBehavior_child_inl
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB})) (a : P.A) :
    (sumBehavior left right).children
        ⟨(Sum.inl a : (PFunctor.sum P Q).A), PUnit.unit⟩ =
      sumBehavior (left.children ⟨a, PUnit.unit⟩) right := by
  change
    ((Responder.sum (Responder.terminal (P := P))
      (Responder.terminal (P := Q))).behavior (left, right)).children
        ⟨(Sum.inl a : (PFunctor.sum P Q).A), PUnit.unit⟩ = _
  rw [behavior_child]
  rfl

@[simp]
theorem sumBehavior_child_inr
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB})) (b : Q.A) :
    (sumBehavior left right).children
        ⟨(Sum.inr b : (PFunctor.sum P Q).A), PUnit.unit⟩ =
      sumBehavior left (right.children ⟨b, PUnit.unit⟩) := by
  change
    ((Responder.sum (Responder.terminal (P := P))
      (Responder.terminal (P := Q))).behavior (left, right)).children
        ⟨(Sum.inr b : (PFunctor.sum P Q).A), PUnit.unit⟩ = _
  rw [behavior_child]
  rfl

/-- Parallel composition of state-free responder behaviors. -/
def parallelBehavior
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB})) :
    PFunctor.M ((P ∥ Q) ⊸ X.{max uA₁ uA₂, uB}) :=
  (Responder.parallel (Responder.terminal (P := P))
    (Responder.terminal (P := Q))).behavior (left, right)

/-- The behavior of a state-presented parallel responder is the parallel
composition of the component behaviors. -/
theorem parallel_behavior
    {State₁ : Type uC₁} {State₂ : Type uC₂}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (state : State₁ × State₂) :
    (Responder.parallel left right).behavior state =
      parallelBehavior (left.behavior state.1) (right.behavior state.2) := by
  let terminalParallel := Responder.parallel
    (Responder.terminal (P := P)) (Responder.terminal (P := Q))
  change (Responder.parallel left right).behavior state =
    terminalParallel.behavior
      (left.behavior state.1, right.behavior state.2)
  symm
  apply behavior_eq_of_responderMap terminalParallel
    (Responder.parallel left right)
    (fun current => (left.behavior current.1, right.behavior current.2))
  · intro current operation
    cases operation <;> simp [terminalParallel]
  · intro current operation
    cases operation <;> simp [terminalParallel]

@[simp]
theorem parallelBehavior_answer_left
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB})) (a : P.A) :
    (Responder.terminal (P := P ∥ Q)).answer
        (parallelBehavior left right)
        (ParallelChoice.left a : (P ∥ Q).A) =
      (Responder.terminal (P := P)).answer left a := by
  change
    (Responder.terminal (P := P ∥ Q)).answer
      ((Responder.parallel (Responder.terminal (P := P))
        (Responder.terminal (P := Q))).behavior (left, right))
      (ParallelChoice.left a : (P ∥ Q).A) = _
  rw [terminal_answer_behavior]
  rfl

@[simp]
theorem parallelBehavior_answer_right
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB})) (b : Q.A) :
    (Responder.terminal (P := P ∥ Q)).answer
        (parallelBehavior left right)
        (ParallelChoice.right b : (P ∥ Q).A) =
      (Responder.terminal (P := Q)).answer right b := by
  change
    (Responder.terminal (P := P ∥ Q)).answer
      ((Responder.parallel (Responder.terminal (P := P))
        (Responder.terminal (P := Q))).behavior (left, right))
      (ParallelChoice.right b : (P ∥ Q).A) = _
  rw [terminal_answer_behavior]
  rfl

@[simp]
theorem parallelBehavior_answer_both
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (a : P.A) (b : Q.A) :
    (Responder.terminal (P := P ∥ Q)).answer
        (parallelBehavior left right)
        (ParallelChoice.both a b : (P ∥ Q).A) =
      ((Responder.terminal (P := P)).answer left a,
        (Responder.terminal (P := Q)).answer right b) := by
  change
    (Responder.terminal (P := P ∥ Q)).answer
      ((Responder.parallel (Responder.terminal (P := P))
        (Responder.terminal (P := Q))).behavior (left, right))
      (ParallelChoice.both a b : (P ∥ Q).A) = _
  rw [terminal_answer_behavior]
  rfl

@[simp]
theorem parallelBehavior_child_left
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB})) (a : P.A) :
    (parallelBehavior left right).children
        ⟨(ParallelChoice.left a : (P ∥ Q).A), PUnit.unit⟩ =
      parallelBehavior
        (left.children ⟨a, PUnit.unit⟩) right := by
  change
    ((Responder.parallel (Responder.terminal (P := P))
      (Responder.terminal (P := Q))).behavior (left, right)).children
        ⟨(ParallelChoice.left a : (P ∥ Q).A), PUnit.unit⟩ = _
  rw [behavior_child]
  rfl

@[simp]
theorem parallelBehavior_child_right
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB})) (b : Q.A) :
    (parallelBehavior left right).children
        ⟨(ParallelChoice.right b : (P ∥ Q).A), PUnit.unit⟩ =
      parallelBehavior left
        (right.children ⟨b, PUnit.unit⟩) := by
  change
    ((Responder.parallel (Responder.terminal (P := P))
      (Responder.terminal (P := Q))).behavior (left, right)).children
        ⟨(ParallelChoice.right b : (P ∥ Q).A), PUnit.unit⟩ = _
  rw [behavior_child]
  rfl

@[simp]
theorem parallelBehavior_child_both
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (a : P.A) (b : Q.A) :
    (parallelBehavior left right).children
        ⟨(ParallelChoice.both a b : (P ∥ Q).A), PUnit.unit⟩ =
      parallelBehavior
        (left.children ⟨a, PUnit.unit⟩)
        (right.children ⟨b, PUnit.unit⟩) := by
  change
    ((Responder.parallel (Responder.terminal (P := P))
      (Responder.terminal (P := Q))).behavior (left, right)).children
        ⟨(ParallelChoice.both a b : (P ∥ Q).A), PUnit.unit⟩ = _
  rw [behavior_child]
  rfl

/-- Coproduct composition of state-free verified responder behaviors. -/
def sumVerifiedBehavior
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right) :
    Display.M (Display.responder (Display.sum S T))
      (sumBehavior left right) :=
  verifiedBehavior (Display.sum S T)
    (Responder.sum (Responder.terminal (P := P))
      (Responder.terminal (P := Q)))
    (fun state => Display.M (Display.responder S) state.1 ×
      Display.M (Display.responder T) state.2)
    (sumCoalgebra (Responder.terminal (P := P))
      (Responder.terminal (P := Q))
      (Display.M (Display.responder S))
      (Display.M (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder T)))
    (left, right) (displayedLeft, displayedRight)

@[simp] theorem respondDisplayed_sumVerifiedBehavior_post_inl
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right)
    (a : P.A) (contract : S.position a) :
    (sumVerifiedBehavior S T left displayedLeft right displayedRight).head
        (.inl a) (ULift.up contract) =
      ULift.up (displayedLeft.head a contract) := by
  exact (respondDisplayed_verifiedBehavior_post (Display.sum S T)
    (Responder.sum (Responder.terminal (P := P))
      (Responder.terminal (P := Q)))
    (fun state => Display.M (Display.responder S) state.1 ×
      Display.M (Display.responder T) state.2)
    (sumCoalgebra (Responder.terminal (P := P))
      (Responder.terminal (P := Q))
      (Display.M (Display.responder S))
      (Display.M (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder T)))
    (left, right) (displayedLeft, displayedRight)
    (Sum.inl a : (PFunctor.sum P Q).A) (ULift.up contract)).trans rfl

@[simp] theorem respondDisplayed_sumVerifiedBehavior_post_inr
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right)
    (b : Q.A) (contract : T.position b) :
    (sumVerifiedBehavior S T left displayedLeft right displayedRight).head
        (.inr b) (ULift.up contract) =
      ULift.up (displayedRight.head b contract) := by
  exact (respondDisplayed_verifiedBehavior_post (Display.sum S T)
    (Responder.sum (Responder.terminal (P := P))
      (Responder.terminal (P := Q)))
    (fun state => Display.M (Display.responder S) state.1 ×
      Display.M (Display.responder T) state.2)
    (sumCoalgebra (Responder.terminal (P := P))
      (Responder.terminal (P := Q))
      (Display.M (Display.responder S))
      (Display.M (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder T)))
    (left, right) (displayedLeft, displayedRight)
    (Sum.inr b : (PFunctor.sum P Q).A) (ULift.up contract)).trans rfl

/-- Exact continuation observation for verified coproduct behavior.  The two
`sumCoalgebra_obligation_*` equations specialize its witness to the selected
branch and show that the unselected witness is frozen. -/
theorem respondDisplayed_sumVerifiedBehavior_next
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right)
    (query : (PFunctor.sum P Q).A)
    (contract : (Display.sum S T).position query) :
    Display.M.transport
        (behavior_child
          (Responder.sum (Responder.terminal (P := P))
            (Responder.terminal (P := Q))) (left, right) query)
        (respondDisplayed (Display.sum S T)
          (sumVerifiedBehavior S T left displayedLeft right displayedRight)
          query contract).2 =
      verifiedBehavior (Display.sum S T)
        (Responder.sum (Responder.terminal (P := P))
          (Responder.terminal (P := Q)))
        (fun state => Display.M (Display.responder S) state.1 ×
          Display.M (Display.responder T) state.2)
        (sumCoalgebra (Responder.terminal (P := P))
          (Responder.terminal (P := Q))
          (Display.M (Display.responder S))
          (Display.M (Display.responder T))
          (Display.Coalgebra.terminal (Display.responder S))
          (Display.Coalgebra.terminal (Display.responder T)))
        ((Responder.sum (Responder.terminal (P := P))
          (Responder.terminal (P := Q))).next (left, right) query)
        (((Display.responderCoalgebraEquiv (Display.sum S T)
          (Responder.sum (Responder.terminal (P := P))
            (Responder.terminal (P := Q)))
          (fun state => Display.M (Display.responder S) state.1 ×
            Display.M (Display.responder T) state.2))
          (sumCoalgebra (Responder.terminal (P := P))
            (Responder.terminal (P := Q))
            (Display.M (Display.responder S))
            (Display.M (Display.responder T))
            (Display.Coalgebra.terminal (Display.responder S))
            (Display.Coalgebra.terminal (Display.responder T)))
          (left, right) (displayedLeft, displayedRight) query contract).2) := by
  exact respondDisplayed_verifiedBehavior_next (Display.sum S T)
    (Responder.sum (Responder.terminal (P := P))
      (Responder.terminal (P := Q)))
    (fun state => Display.M (Display.responder S) state.1 ×
      Display.M (Display.responder T) state.2)
    (sumCoalgebra (Responder.terminal (P := P))
      (Responder.terminal (P := Q))
      (Display.M (Display.responder S))
      (Display.M (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder T)))
    (left, right) (displayedLeft, displayedRight) query contract

/-- Parallel composition of state-free verified responder behaviors. -/
def parallelVerifiedBehavior
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right) :
    Display.M (Display.responder (Display.parallelSum S T))
      (parallelBehavior left right) :=
  verifiedBehavior (Display.parallelSum S T)
    (Responder.parallel (Responder.terminal (P := P))
      (Responder.terminal (P := Q)))
    (fun state => Display.M (Display.responder S) state.1 ×
      Display.M (Display.responder T) state.2)
    (parallelCoalgebra (Responder.terminal (P := P))
      (Responder.terminal (P := Q))
      (Display.M (Display.responder S))
      (Display.M (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder T)))
    (left, right) (displayedLeft, displayedRight)

@[simp] theorem respondDisplayed_parallelVerifiedBehavior_post_left
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right)
    (a : P.A) (contract : S.position a) :
    (parallelVerifiedBehavior S T left displayedLeft right displayedRight).head
        (.left a) (ULift.up contract) =
      ULift.up (displayedLeft.head a contract) := by
  exact (respondDisplayed_verifiedBehavior_post (Display.parallelSum S T)
    (Responder.parallel (Responder.terminal (P := P))
      (Responder.terminal (P := Q)))
    (fun state => Display.M (Display.responder S) state.1 ×
      Display.M (Display.responder T) state.2)
    (parallelCoalgebra (Responder.terminal (P := P))
      (Responder.terminal (P := Q))
      (Display.M (Display.responder S))
      (Display.M (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder T)))
    (left, right) (displayedLeft, displayedRight)
    (ParallelChoice.left a : (P ∥ Q).A) (ULift.up contract)).trans rfl

@[simp] theorem respondDisplayed_parallelVerifiedBehavior_post_right
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right)
    (b : Q.A) (contract : T.position b) :
    (parallelVerifiedBehavior S T left displayedLeft right displayedRight).head
        (.right b) (ULift.up contract) =
      ULift.up (displayedRight.head b contract) := by
  exact (respondDisplayed_verifiedBehavior_post (Display.parallelSum S T)
    (Responder.parallel (Responder.terminal (P := P))
      (Responder.terminal (P := Q)))
    (fun state => Display.M (Display.responder S) state.1 ×
      Display.M (Display.responder T) state.2)
    (parallelCoalgebra (Responder.terminal (P := P))
      (Responder.terminal (P := Q))
      (Display.M (Display.responder S))
      (Display.M (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder T)))
    (left, right) (displayedLeft, displayedRight)
    (ParallelChoice.right b : (P ∥ Q).A) (ULift.up contract)).trans rfl

@[simp] theorem respondDisplayed_parallelVerifiedBehavior_post_both
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right)
    (a : P.A) (b : Q.A)
    (leftContract : S.position a) (rightContract : T.position b) :
    (parallelVerifiedBehavior S T left displayedLeft right displayedRight).head
        (.both a b) (leftContract, rightContract) =
      (displayedLeft.head a leftContract,
        displayedRight.head b rightContract) := by
  exact (respondDisplayed_verifiedBehavior_post (Display.parallelSum S T)
    (Responder.parallel (Responder.terminal (P := P))
      (Responder.terminal (P := Q)))
    (fun state => Display.M (Display.responder S) state.1 ×
      Display.M (Display.responder T) state.2)
    (parallelCoalgebra (Responder.terminal (P := P))
      (Responder.terminal (P := Q))
      (Display.M (Display.responder S))
      (Display.M (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder T)))
    (left, right) (displayedLeft, displayedRight)
    (ParallelChoice.both a b : (P ∥ Q).A)
    (leftContract, rightContract)).trans rfl

theorem respondDisplayed_parallelVerifiedBehavior_next_left
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right)
    (a : P.A) (contract : S.position a) :
    Display.M.transport
        (behavior_child
          (Responder.parallel (Responder.terminal (P := P))
            (Responder.terminal (P := Q)))
          (left, right) (ParallelChoice.left a : (P ∥ Q).A))
        (respondDisplayed (Display.parallelSum S T)
          (parallelVerifiedBehavior S T left displayedLeft right displayedRight)
          (.left a) (ULift.up contract)).2 =
      verifiedBehavior (Display.parallelSum S T)
        (Responder.parallel (Responder.terminal (P := P))
          (Responder.terminal (P := Q)))
        (fun state => Display.M (Display.responder S) state.1 ×
          Display.M (Display.responder T) state.2)
        (parallelCoalgebra (Responder.terminal (P := P))
          (Responder.terminal (P := Q))
          (Display.M (Display.responder S))
          (Display.M (Display.responder T))
          (Display.Coalgebra.terminal (Display.responder S))
          (Display.Coalgebra.terminal (Display.responder T)))
        ((Responder.parallel (Responder.terminal (P := P))
          (Responder.terminal (P := Q))).next (left, right) (.left a))
        (((Display.responderCoalgebraEquiv (Display.parallelSum S T)
          (Responder.parallel (Responder.terminal (P := P))
            (Responder.terminal (P := Q)))
          (fun state => Display.M (Display.responder S) state.1 ×
            Display.M (Display.responder T) state.2))
          (parallelCoalgebra (Responder.terminal (P := P))
            (Responder.terminal (P := Q))
            (Display.M (Display.responder S))
            (Display.M (Display.responder T))
            (Display.Coalgebra.terminal (Display.responder S))
            (Display.Coalgebra.terminal (Display.responder T)))
          (left, right) (displayedLeft, displayedRight)
          (ParallelChoice.left a : (P ∥ Q).A) (ULift.up contract)).2) := by
  exact respondDisplayed_verifiedBehavior_next (Display.parallelSum S T)
    (Responder.parallel (Responder.terminal (P := P))
      (Responder.terminal (P := Q)))
    (fun state => Display.M (Display.responder S) state.1 ×
      Display.M (Display.responder T) state.2)
    (parallelCoalgebra (Responder.terminal (P := P))
      (Responder.terminal (P := Q))
      (Display.M (Display.responder S))
      (Display.M (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder T)))
    (left, right) (displayedLeft, displayedRight)
    (ParallelChoice.left a : (P ∥ Q).A) (ULift.up contract)

/-- Generic continuation observation for verified parallel behavior.  Together
with the three `parallelCoalgebra_obligation_*` equations, this covers the
left, right, and simultaneous branches without exposing the corecursor. -/
theorem respondDisplayed_parallelVerifiedBehavior_next
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right)
    (query : (P ∥ Q).A)
    (contract : (Display.parallelSum S T).position query) :
    Display.M.transport
        (behavior_child
          (Responder.parallel (Responder.terminal (P := P))
            (Responder.terminal (P := Q))) (left, right) query)
        (respondDisplayed (Display.parallelSum S T)
          (parallelVerifiedBehavior S T left displayedLeft right displayedRight)
          query contract).2 =
      verifiedBehavior (Display.parallelSum S T)
        (Responder.parallel (Responder.terminal (P := P))
          (Responder.terminal (P := Q)))
        (fun state => Display.M (Display.responder S) state.1 ×
          Display.M (Display.responder T) state.2)
        (parallelCoalgebra (Responder.terminal (P := P))
          (Responder.terminal (P := Q))
          (Display.M (Display.responder S))
          (Display.M (Display.responder T))
          (Display.Coalgebra.terminal (Display.responder S))
          (Display.Coalgebra.terminal (Display.responder T)))
        ((Responder.parallel (Responder.terminal (P := P))
          (Responder.terminal (P := Q))).next (left, right) query)
        (((Display.responderCoalgebraEquiv (Display.parallelSum S T)
          (Responder.parallel (Responder.terminal (P := P))
            (Responder.terminal (P := Q)))
          (fun state => Display.M (Display.responder S) state.1 ×
            Display.M (Display.responder T) state.2))
          (parallelCoalgebra (Responder.terminal (P := P))
            (Responder.terminal (P := Q))
            (Display.M (Display.responder S))
            (Display.M (Display.responder T))
            (Display.Coalgebra.terminal (Display.responder S))
            (Display.Coalgebra.terminal (Display.responder T)))
          (left, right) (displayedLeft, displayedRight)
          query contract).2) := by
  exact respondDisplayed_verifiedBehavior_next (Display.parallelSum S T)
    (Responder.parallel (Responder.terminal (P := P))
      (Responder.terminal (P := Q)))
    (fun state => Display.M (Display.responder S) state.1 ×
      Display.M (Display.responder T) state.2)
    (parallelCoalgebra (Responder.terminal (P := P))
      (Responder.terminal (P := Q))
      (Display.M (Display.responder S))
      (Display.M (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder T)))
    (left, right) (displayedLeft, displayedRight) query contract

/-- Forget proof-relevant evidence while retaining the intrinsically indexed
ordinary behavior. -/
def verifiedBehaviorBase
    {R : PFunctor.{uA₁, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} R)
    (behavior : PFunctor.M (R ⊸ X.{uA₁, uB}))
    (_ : Display.M (Display.responder S) behavior) :=
  behavior

/-- The displayed-to-base projection is strictly compatible with parallel
composition; the ordinary behavior is the index of the displayed one. -/
@[simp] theorem verifiedBehaviorBase_parallel
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right) :
    verifiedBehaviorBase (Display.parallelSum S T)
        (parallelBehavior left right)
        (parallelVerifiedBehavior S T left displayedLeft right displayedRight) =
      parallelBehavior left right :=
  rfl

end Responder
end PFunctor
