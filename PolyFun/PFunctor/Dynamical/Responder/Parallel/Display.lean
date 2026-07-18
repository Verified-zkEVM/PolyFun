/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module


public import PolyFun.PFunctor.Display.Parallel
public import PolyFun.PFunctor.Dynamical.Responder.Display
public import PolyFun.PFunctor.Dynamical.Responder.Parallel

/-!
# Displayed parallel responders

This module proves closure of proof-relevant responder coalgebras under the
separable parallel display.  The ordinary responder operation remains in the
display-independent sibling module.
-/

@[expose] public section

universe uA₁ uA₂ uB uS₁ uS₂ uC₁ uD₁ uC₂ uD₂ uI uJ

namespace PFunctor
namespace Responder

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
  {State₁ : Type uS₁} {State₂ : Type uS₂}

/-- Parallel closure of proof-relevant responder coalgebras for the separable
parallel display. -/
def parallelCoalgebra
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (I : State₁ → Type uI) (J : State₂ → Type uJ)
    (displayedLeft : Display.Coalgebra (Display.responder S) left.out I)
    (displayedRight : Display.Coalgebra (Display.responder T) right.out J) :
    Display.Coalgebra
      (Display.responder (Display.parallelSum S T))
      (parallel left right).out
      (fun state => I state.1 × J state.2) :=
  (Display.responderCoalgebraEquiv (Display.parallelSum S T)
    (parallel left right) (fun state => I state.1 × J state.2)).symm
      fun state witness query contract =>
        match query with
        | .left a =>
            let step := (Display.responderCoalgebraEquiv S left I)
              displayedLeft state.1 witness.1 a contract.down
            (ULift.up step.1, (step.2, witness.2))
        | .right b =>
            let step := (Display.responderCoalgebraEquiv T right J)
              displayedRight state.2 witness.2 b contract.down
            (ULift.up step.1, (witness.1, step.2))
        | .both a b =>
            let leftStep := (Display.responderCoalgebraEquiv S left I)
              displayedLeft state.1 witness.1 a contract.1
            let rightStep := (Display.responderCoalgebraEquiv T right J)
              displayedRight state.2 witness.2 b contract.2
            ((leftStep.1, rightStep.1), (leftStep.2, rightStep.2))

@[simp]
theorem parallelCoalgebra_obligation_left
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (I : State₁ → Type uI) (J : State₂ → Type uJ)
    (displayedLeft : Display.Coalgebra (Display.responder S) left.out I)
    (displayedRight : Display.Coalgebra (Display.responder T) right.out J)
    (state : State₁ × State₂) (witness : I state.1 × J state.2)
    (a : P.A) (contract : S.position a) :
    (Display.responderCoalgebraEquiv (Display.parallelSum S T)
      (parallel left right) (fun state => I state.1 × J state.2))
        (parallelCoalgebra left right I J displayedLeft displayedRight)
        state witness (ParallelChoice.left a : (P ∥ Q).A)
        (ULift.up contract) =
      let step := (Display.responderCoalgebraEquiv S left I)
        displayedLeft state.1 witness.1 a contract
      (ULift.up step.1, (step.2, witness.2)) :=
  rfl

@[simp]
theorem parallelCoalgebra_obligation_right
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (I : State₁ → Type uI) (J : State₂ → Type uJ)
    (displayedLeft : Display.Coalgebra (Display.responder S) left.out I)
    (displayedRight : Display.Coalgebra (Display.responder T) right.out J)
    (state : State₁ × State₂) (witness : I state.1 × J state.2)
    (b : Q.A) (contract : T.position b) :
    (Display.responderCoalgebraEquiv (Display.parallelSum S T)
      (parallel left right) (fun state => I state.1 × J state.2))
        (parallelCoalgebra left right I J displayedLeft displayedRight)
        state witness (ParallelChoice.right b : (P ∥ Q).A)
        (ULift.up contract) =
      let step := (Display.responderCoalgebraEquiv T right J)
        displayedRight state.2 witness.2 b contract
      (ULift.up step.1, (witness.1, step.2)) :=
  rfl

@[simp]
theorem parallelCoalgebra_obligation_both
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (I : State₁ → Type uI) (J : State₂ → Type uJ)
    (displayedLeft : Display.Coalgebra (Display.responder S) left.out I)
    (displayedRight : Display.Coalgebra (Display.responder T) right.out J)
    (state : State₁ × State₂) (witness : I state.1 × J state.2)
    (a : P.A) (b : Q.A)
    (leftContract : S.position a) (rightContract : T.position b) :
    (Display.responderCoalgebraEquiv (Display.parallelSum S T)
      (parallel left right) (fun state => I state.1 × J state.2))
        (parallelCoalgebra left right I J displayedLeft displayedRight)
        state witness (ParallelChoice.both a b : (P ∥ Q).A)
        (leftContract, rightContract) =
      let leftStep := (Display.responderCoalgebraEquiv S left I)
        displayedLeft state.1 witness.1 a leftContract
      let rightStep := (Display.responderCoalgebraEquiv T right J)
        displayedRight state.2 witness.2 b rightContract
      ((leftStep.1, rightStep.1), (leftStep.2, rightStep.2)) :=
  rfl

end Responder
end PFunctor
