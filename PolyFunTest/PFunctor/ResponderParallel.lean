/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Parallel.Free
public import PolyFun.PFunctor.Dynamical.Responder.Parallel.Compatibility

/-!
# Regression tests for parallel responder semantics

The examples distinguish sum from one-or-both parallel composition, observe
state freezing in every branch, and exercise ordinary, proof-relevant, and
reindexed execution.
-/

@[expose] public section

namespace PFunctor.ResponderParallelCanary

abbrev Left : PFunctor.{0, 0} := ⟨Bool, fun _ => Bool⟩

abbrev Right : PFunctor.{0, 0} := ⟨PUnit, fun _ => Nat⟩

def leftResponder : Responder Nat Left :=
  Responder.mk' (fun _ query => !query) (fun state _ => state + 1)

def rightResponder : Responder Nat Right :=
  Responder.mk' (fun state _ => state) (fun state _ => state + 10)

def leftProgram : FreeM Left Bool :=
  FreeM.liftBind true FreeM.pure

def rightProgram : FreeM Right Nat :=
  FreeM.liftBind PUnit.unit FreeM.pure

example :
    (Responder.sum leftResponder rightResponder).answer (0, 5) (.inl true) =
      false :=
  rfl

example :
    (Responder.sum leftResponder rightResponder).next (0, 5) (.inl true) =
      (1, 5) :=
  rfl

example :
    (Responder.sum leftResponder rightResponder).next
      (0, 5) (.inr PUnit.unit) = (0, 15) :=
  rfl

example :
    (Responder.parallel leftResponder rightResponder).next
      (0, 5) (.left true) = (1, 5) :=
  rfl

example :
    (Responder.parallel leftResponder rightResponder).next
      (0, 5) (.right PUnit.unit) = (0, 15) :=
  rfl

example :
    (Responder.parallel leftResponder rightResponder).next
      (0, 5) (.both true PUnit.unit) = (1, 15) :=
  rfl

example :
    (Responder.parallel leftResponder rightResponder).runFree
      (FreeM.parallel leftProgram rightProgram) (0, 5) =
        ((false, 5), (1, 15)) :=
  rfl

example :
    (Responder.parallel leftResponder rightResponder).runFree
      (FreeM.parallel leftProgram (FreeM.pure 7)) (0, 5) =
        ((false, 7), (1, 5)) :=
  rfl

example :
    (Responder.parallel leftResponder rightResponder).runFree
      (FreeM.parallel (FreeM.pure true) rightProgram) (0, 5) =
        ((true, 5), (0, 15)) :=
  rfl

example : (Responder.terminal (P := Left ∥ Right)).answer
    (Responder.parallelBehavior
      (leftResponder.behavior 0) (rightResponder.behavior 5))
    (.both true PUnit.unit) = (false, 5) :=
  rfl

def leftDisplay : Display Left where
  position _ := PUnit
  direction _ _ _ := PUnit

def rightDisplay : Display Right where
  position _ := PUnit
  direction _ _ _ := PUnit

def leftInvariant (_ : Nat) : Type := PUnit

def rightInvariant (_ : Nat) : Type := PUnit

def displayedLeftResponder :
    Display.Coalgebra (Display.responder leftDisplay)
      leftResponder.out leftInvariant :=
  (Display.responderCoalgebraEquiv leftDisplay leftResponder leftInvariant).symm
    fun _ _ _ _ => (PUnit.unit, PUnit.unit)

def displayedRightResponder :
    Display.Coalgebra (Display.responder rightDisplay)
      rightResponder.out rightInvariant :=
  (Display.responderCoalgebraEquiv rightDisplay rightResponder rightInvariant).symm
    fun _ _ _ _ => (PUnit.unit, PUnit.unit)

def displayedLeftProgram :
    FreeM.Displayed
      (leftDisplay.toDisplayedAlgebra (fun _ => PUnit)) leftProgram :=
  ⟨PUnit.unit, fun answer _ => leftDisplay.leaf _ answer PUnit.unit⟩

def displayedRightProgram :
    FreeM.Displayed
      (rightDisplay.toDisplayedAlgebra (fun _ => PUnit)) rightProgram :=
  ⟨PUnit.unit, fun answer _ => rightDisplay.leaf _ answer PUnit.unit⟩

def displayedParallelProgram :
    FreeM.Displayed
      ((Display.parallelSum leftDisplay rightDisplay).toDisplayedAlgebra
        (fun _ => PUnit × PUnit))
      (FreeM.parallel leftProgram rightProgram) :=
  FreeM.Displayed.parallel leftProgram rightProgram
    displayedLeftProgram displayedRightProgram

def displayedParallelResponder :
    Display.Coalgebra
      (Display.responder (Display.parallelSum leftDisplay rightDisplay))
      (Responder.parallel leftResponder rightResponder).out
      (fun state => leftInvariant state.1 × rightInvariant state.2) :=
  Responder.parallelCoalgebra leftResponder rightResponder
    leftInvariant rightInvariant displayedLeftResponder displayedRightResponder

example :
    Responder.runFreeDisplayed
      (Display.parallelSum leftDisplay rightDisplay)
      (Responder.parallel leftResponder rightResponder)
      displayedParallelResponder displayedParallelProgram
      (0, 5) (PUnit.unit, PUnit.unit) =
        ((PUnit.unit, PUnit.unit), (PUnit.unit, PUnit.unit)) :=
  rfl

def leftIdentityHandler : Handler (FreeM Left) Left := Handler.id Left

def rightIdentityHandler : Handler (FreeM Right) Right := Handler.id Right

example :
    Responder.reindex
        (Handler.parallel leftIdentityHandler rightIdentityHandler)
        (Responder.parallel leftResponder rightResponder) =
      Responder.parallel
        (Responder.reindex leftIdentityHandler leftResponder)
        (Responder.reindex rightIdentityHandler rightResponder) :=
  Responder.reindex_parallel _ _ _ _

/-! Nonidentity compatibility canaries distinguish both handler components,
the one-sided coproduct embedding, and responder-state handoff. -/

def leftNegatingHandler : Handler (FreeM Left) Left := fun query =>
  FreeM.liftBind (!query) fun answer => FreeM.pure (!answer)

def rightTwoCallHandler : Handler (FreeM Right) Right := fun _ =>
  FreeM.liftBind PUnit.unit fun first =>
    FreeM.liftBind PUnit.unit fun second => FreeM.pure (first + second)

def reindexedParallel :=
  Responder.reindex
    (Handler.parallel leftNegatingHandler rightTwoCallHandler)
    (Responder.parallel leftResponder rightResponder)

example : reindexedParallel.answer (0, 5) (.left true) = false := rfl
example : reindexedParallel.next (0, 5) (.left true) = (1, 5) := rfl
example : (show Nat from
    reindexedParallel.answer (0, 5) (.right PUnit.unit)) = 20 := rfl
example : reindexedParallel.next (0, 5) (.right PUnit.unit) = (0, 25) := rfl
example : reindexedParallel.answer (0, 5) (.both true PUnit.unit) =
    (false, 20) := rfl
example : reindexedParallel.next (0, 5) (.both true PUnit.unit) =
    (1, 25) := rfl

def parallelRestrictedToSum :=
  Responder.reindex (Handler.ofLens (Lens.sumToParallel Left Right))
    (Responder.parallel leftResponder rightResponder)

example : parallelRestrictedToSum.answer (0, 5) (.inl true) = false := rfl
example : parallelRestrictedToSum.next (0, 5) (.inl true) = (1, 5) := rfl
example : (show Nat from
    parallelRestrictedToSum.answer (0, 5) (.inr PUnit.unit)) = 5 := rfl
example : parallelRestrictedToSum.next (0, 5) (.inr PUnit.unit) = (0, 15) := rfl
example : Responder.sum leftResponder rightResponder = parallelRestrictedToSum :=
  Responder.sum_eq_reindex_parallel leftResponder rightResponder

/-! Nonconstant dependent contracts make every proof-relevant branch and
continuation observable. -/

def dependentLeftDisplay : Display Left where
  position operation := if operation then Nat else Bool
  direction _ _ answer := if answer then Fin 2 else Fin 3

def dependentRightDisplay : Display Right where
  position _ := String
  direction _ _ answer := Fin (answer + 1)

def leftPost (answer : Bool) : if answer then Fin 2 else Fin 3 := by
  cases answer <;> exact ⟨0, Nat.zero_lt_succ _⟩

def rightPost (answer : Nat) : Fin (answer + 1) :=
  ⟨0, Nat.zero_lt_succ _⟩

def leftContractTrue : dependentLeftDisplay.position true := by
  change Nat
  exact 5
def leftContractFalse : dependentLeftDisplay.position false := true
def rightContract : dependentRightDisplay.position PUnit.unit := "right"

def dependentLeftInvariant (state : Nat) : Type := Fin (state + 2)
def dependentRightInvariant (state : Nat) : Type := Fin (state + 2)

def dependentLeftCoalgebra :
    Display.Coalgebra (Display.responder dependentLeftDisplay)
      leftResponder.out dependentLeftInvariant :=
  (Display.responderCoalgebraEquiv dependentLeftDisplay
    leftResponder dependentLeftInvariant).symm fun state _ operation _ => by
      refine ⟨?_, ⟨0, Nat.zero_lt_succ _⟩⟩
      exact leftPost (!operation)

def dependentRightCoalgebra :
    Display.Coalgebra (Display.responder dependentRightDisplay)
      rightResponder.out dependentRightInvariant :=
  (Display.responderCoalgebraEquiv dependentRightDisplay
    rightResponder dependentRightInvariant).symm fun state _ _ _ =>
      ⟨rightPost state, ⟨0, Nat.zero_lt_succ _⟩⟩

def leftWitness0 : dependentLeftInvariant 0 := ⟨1, by decide⟩
def leftWitness1 : dependentLeftInvariant 1 := ⟨0, Nat.zero_lt_succ _⟩
def rightWitness5 : dependentRightInvariant 5 := ⟨1, by decide⟩
def rightWitness15 : dependentRightInvariant 15 := ⟨0, Nat.zero_lt_succ _⟩

def dependentSumCoalgebra :=
  Responder.sumCoalgebra leftResponder rightResponder
    dependentLeftInvariant dependentRightInvariant
    dependentLeftCoalgebra dependentRightCoalgebra

def dependentParallelCoalgebra :=
  Responder.parallelCoalgebra leftResponder rightResponder
    dependentLeftInvariant dependentRightInvariant
    dependentLeftCoalgebra dependentRightCoalgebra

example :
    (Display.responderCoalgebraEquiv
      (Display.sum dependentLeftDisplay dependentRightDisplay)
      (Responder.sum leftResponder rightResponder)
      (fun state => dependentLeftInvariant state.1 ×
        dependentRightInvariant state.2))
      dependentSumCoalgebra (0, 5) (leftWitness0, rightWitness5)
      (.inl true) (ULift.up leftContractTrue) =
        (ULift.up (leftPost false), (leftWitness1, rightWitness5)) := rfl

example :
    (Display.responderCoalgebraEquiv
      (Display.sum dependentLeftDisplay dependentRightDisplay)
      (Responder.sum leftResponder rightResponder)
      (fun state => dependentLeftInvariant state.1 ×
        dependentRightInvariant state.2))
      dependentSumCoalgebra (0, 5) (leftWitness0, rightWitness5)
      (.inr PUnit.unit) (ULift.up rightContract) =
        (ULift.up (rightPost 5), (leftWitness0, rightWitness15)) := rfl

example :
    (Display.responderCoalgebraEquiv
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.parallel leftResponder rightResponder)
      (fun state => dependentLeftInvariant state.1 ×
        dependentRightInvariant state.2))
      dependentParallelCoalgebra (0, 5) (leftWitness0, rightWitness5)
      (.left true) (ULift.up leftContractTrue) =
        (ULift.up (leftPost false), (leftWitness1, rightWitness5)) := rfl

example :
    (Display.responderCoalgebraEquiv
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.parallel leftResponder rightResponder)
      (fun state => dependentLeftInvariant state.1 ×
        dependentRightInvariant state.2))
      dependentParallelCoalgebra (0, 5) (leftWitness0, rightWitness5)
      (.right PUnit.unit) (ULift.up rightContract) =
        (ULift.up (rightPost 5), (leftWitness0, rightWitness15)) := rfl

example :
    (Display.responderCoalgebraEquiv
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.parallel leftResponder rightResponder)
      (fun state => dependentLeftInvariant state.1 ×
        dependentRightInvariant state.2))
      dependentParallelCoalgebra (0, 5) (leftWitness0, rightWitness5)
      (.both true PUnit.unit) (leftContractTrue, rightContract) =
        ((leftPost false, rightPost 5), (leftWitness1, rightWitness15)) := rfl

def dependentLeftDisplayedBehavior :=
  Responder.toDisplayedBehavior dependentLeftDisplay leftResponder
    dependentLeftInvariant dependentLeftCoalgebra 0 leftWitness0

def dependentRightDisplayedBehavior :=
  Responder.toDisplayedBehavior dependentRightDisplay rightResponder
    dependentRightInvariant dependentRightCoalgebra 5 rightWitness5

def dependentSumDisplayedBehavior :=
  Responder.sumDisplayedBehavior dependentLeftDisplay dependentRightDisplay
    (leftResponder.behavior 0) dependentLeftDisplayedBehavior
    (rightResponder.behavior 5) dependentRightDisplayedBehavior

def dependentParallelDisplayedBehavior :=
  Responder.parallelDisplayedBehavior dependentLeftDisplay dependentRightDisplay
    (leftResponder.behavior 0) dependentLeftDisplayedBehavior
    (rightResponder.behavior 5) dependentRightDisplayedBehavior

example : dependentSumDisplayedBehavior.head (.inl true)
    (ULift.up leftContractTrue) = ULift.up (leftPost false) := rfl

example : dependentSumDisplayedBehavior.head (.inr PUnit.unit)
    (ULift.up rightContract) = ULift.up (rightPost 5) := rfl

example : dependentParallelDisplayedBehavior.head (.left true)
    (ULift.up leftContractTrue) = ULift.up (leftPost false) := rfl

example : dependentParallelDisplayedBehavior.head (.right PUnit.unit)
    (ULift.up rightContract) = ULift.up (rightPost 5) := rfl

example : dependentParallelDisplayedBehavior.head (.both true PUnit.unit)
    (leftContractTrue, rightContract) = (leftPost false, rightPost 5) := rfl

example :
    (Responder.respondDisplayed
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.respondDisplayed
        (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
        dependentParallelDisplayedBehavior (.left true)
        (ULift.up leftContractTrue)).2
      (.right PUnit.unit) (ULift.up rightContract)).1 =
        ULift.up (rightPost 5) := rfl

example :
    (Responder.respondDisplayed
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.respondDisplayed
        (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
        dependentParallelDisplayedBehavior (.right PUnit.unit)
        (ULift.up rightContract)).2
      (.right PUnit.unit) (ULift.up rightContract)).1 =
        ULift.up (rightPost 15) := rfl

example :
    (Responder.respondDisplayed
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.respondDisplayed
        (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
        dependentParallelDisplayedBehavior (.both true PUnit.unit)
        (leftContractTrue, rightContract)).2
      (.right PUnit.unit) (ULift.up rightContract)).1 =
        ULift.up (rightPost 15) := rfl

namespace UniverseCanary

universe uA₁ uA₂ uB uS₁ uS₂ uC₁ uD₁ uC₂ uD₂ uI uJ uE uF

def parallelResponder
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {State₁ : Type uS₁} {State₂ : Type uS₂} :
    Responder State₁ P → Responder State₂ Q →
      Responder (State₁ × State₂) (P ∥ Q) :=
  Responder.parallel

def sumCoalgebra
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {State₁ : Type uS₁} {State₂ : Type uS₂}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (I : State₁ → Type uI) (J : State₂ → Type uJ)
    (dLeft : Display.Coalgebra (Display.responder S) left.out I)
    (dRight : Display.Coalgebra (Display.responder T) right.out J) :
    Display.Coalgebra (Display.responder (Display.sum S T))
      (Responder.sum left right).out (fun state => I state.1 × J state.2) :=
  Responder.sumCoalgebra left right I J dLeft dRight

def parallelCoalgebra
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {State₁ : Type uS₁} {State₂ : Type uS₂}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (I : State₁ → Type uI) (J : State₂ → Type uJ)
    (dLeft : Display.Coalgebra (Display.responder S) left.out I)
    (dRight : Display.Coalgebra (Display.responder T) right.out J) :
    Display.Coalgebra (Display.responder (Display.parallelSum S T))
      (Responder.parallel left right).out
      (fun state => I state.1 × J state.2) :=
  Responder.parallelCoalgebra left right I J dLeft dRight

def parallelBehavior
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    PFunctor.M (P ⊸ X.{uA₁, uB}) →
    PFunctor.M (Q ⊸ X.{uA₂, uB}) →
      PFunctor.M ((P ∥ Q) ⊸ X.{max uA₁ uA₂, uB}) :=
  Responder.parallelBehavior

def parallelDisplayedBehavior
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (dLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (dRight : Display.M (Display.responder T) right) :
    Display.M (Display.responder (Display.parallelSum S T))
      (Responder.parallelBehavior left right) :=
  Responder.parallelDisplayedBehavior S T left dLeft right dRight

def sumDisplayedBehavior
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (dLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (dRight : Display.M (Display.responder T) right) :
    Display.M (Display.responder (Display.sum S T))
      (Responder.sumBehavior left right) :=
  Responder.sumDisplayedBehavior S T left dLeft right dRight

theorem runFreeParallel
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {State₁ : Type uS₁} {State₂ : Type uS₂}
    (left : Responder State₁ P) (right : Responder State₂ Q)
    (leftProgram : FreeM P (ULift.{uE} PUnit))
    (rightProgram : FreeM Q (ULift.{uF} PUnit))
    (leftState : State₁) (rightState : State₂) :
    (Responder.parallel left right).runFree
        (FreeM.parallel leftProgram rightProgram) (leftState, rightState) =
      let leftResult := left.runFree leftProgram leftState
      let rightResult := right.runFree rightProgram rightState
      ((leftResult.1, rightResult.1), (leftResult.2, rightResult.2)) :=
  Responder.runFree_parallel left right leftProgram rightProgram
    leftState rightState

end UniverseCanary

end PFunctor.ResponderParallelCanary
