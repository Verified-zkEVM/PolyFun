/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder.Parallel.DisplayedCoherence

/-!
# Regression tests for proof-relevant parallel coherence

The displays below have genuinely answer-dependent postcondition types.  This
prevents symmetry, unit, and associativity laws from passing by silently
erasing or swapping displayed evidence.
-/

@[expose] public section

namespace PFunctor.ParallelDisplayedCoherenceCanary

abbrev Left : PFunctor.{0, 0} := ⟨Bool, fun _ => Bool⟩

abbrev Right : PFunctor.{0, 0} := ⟨PUnit, fun _ => Nat⟩

def leftResponder : Responder Nat Left :=
  Responder.mk' (fun _ query => !query) (fun state _ => state + 1)

def rightResponder : Responder Nat Right :=
  Responder.mk' (fun state _ => state) (fun state _ => state + 10)

def leftDisplay : Display Left where
  position operation := if operation then Nat else Bool
  direction _ _ answer := if answer then Fin 2 else Fin 3

def rightDisplay : Display Right where
  position _ := String
  direction _ _ answer := Fin (answer + 1)

def leftPost (answer : Bool) : if answer then Fin 2 else Fin 3 := by
  cases answer <;> exact ⟨0, Nat.zero_lt_succ _⟩

def rightPost (answer : Nat) : Fin (answer + 1) :=
  ⟨0, Nat.zero_lt_succ _⟩

def leftInvariant (state : Nat) : Type := Fin (state + 1)

def rightInvariant (state : Nat) : Type := PLift (state = state)

def leftCoalgebra :
    Display.Coalgebra (Display.responder leftDisplay)
      leftResponder.out leftInvariant :=
  (Display.responderCoalgebraEquiv leftDisplay
    leftResponder leftInvariant).symm fun state _ operation _ => by
      refine ⟨?_, ⟨0, Nat.zero_lt_succ _⟩⟩
      change (if !operation then Fin 2 else Fin 3)
      exact leftPost (!operation)

def rightCoalgebra :
    Display.Coalgebra (Display.responder rightDisplay)
      rightResponder.out rightInvariant :=
  (Display.responderCoalgebraEquiv rightDisplay
    rightResponder rightInvariant).symm fun state _ _ _ => by
      exact ⟨rightPost state, ⟨rfl⟩⟩

def leftDisplayed :
    Display.M (Display.responder leftDisplay) (leftResponder.behavior 0) :=
  Responder.toDisplayedBehavior leftDisplay leftResponder leftInvariant
    leftCoalgebra 0 ⟨0, Nat.zero_lt_succ _⟩

def rightDisplayed :
    Display.M (Display.responder rightDisplay) (rightResponder.behavior 5) :=
  Responder.toDisplayedBehavior rightDisplay rightResponder rightInvariant
    rightCoalgebra 5 ⟨rfl⟩

def parallelDisplayed :
    Display.M (Display.responder (Display.parallelSum leftDisplay rightDisplay))
      (Responder.parallelBehavior
        (leftResponder.behavior 0) (rightResponder.behavior 5)) :=
  Responder.parallelDisplayedBehavior leftDisplay rightDisplay
    (leftResponder.behavior 0) leftDisplayed
    (rightResponder.behavior 5) rightDisplayed

def leftContract : leftDisplay.position true := by
  change Nat
  exact 5

def rightContract : rightDisplay.position PUnit.unit :=
  "right"

example :
    (Responder.respondDisplayed
      (Display.parallelSum leftDisplay rightDisplay)
      parallelDisplayed (.both true PUnit.unit)
      (leftContract, rightContract)).1 =
        (leftPost false, rightPost 5) := by
  rfl

example :
    Display.M.transport
        (Responder.mapBehavior_parallel_comm
          (leftResponder.behavior 0) (rightResponder.behavior 5))
      (Responder.mapDisplayedBehavior
        (Display.Lens.parallelSumComm leftDisplay rightDisplay)
        (Responder.parallelBehavior
          (rightResponder.behavior 5) (leftResponder.behavior 0))
        (Responder.parallelDisplayedBehavior rightDisplay leftDisplay
          (rightResponder.behavior 5) rightDisplayed
          (leftResponder.behavior 0) leftDisplayed)) =
      parallelDisplayed :=
  Responder.mapDisplayedBehavior_parallel_comm _ _ _ _ _ _

example :
    Display.M.transport
        (Responder.mapBehavior_parallel_zero_right (leftResponder.behavior 0))
      (Responder.mapDisplayedBehavior
        (Display.Lens.parallelSumZero leftDisplay)
        (leftResponder.behavior 0) leftDisplayed) =
      Responder.parallelDisplayedBehavior leftDisplay Display.zero
        (leftResponder.behavior 0) leftDisplayed
        Responder.zeroBehavior Responder.zeroDisplayedBehavior :=
  Responder.mapDisplayedBehavior_parallel_zero_right _ _ _

example :
    Display.M.transport
        (Responder.mapBehavior_parallel_zero_left (leftResponder.behavior 0))
      (Responder.mapDisplayedBehavior
        (Display.Lens.zeroParallelSum leftDisplay)
        (leftResponder.behavior 0) leftDisplayed) =
      Responder.parallelDisplayedBehavior Display.zero leftDisplay
        Responder.zeroBehavior Responder.zeroDisplayedBehavior
        (leftResponder.behavior 0) leftDisplayed :=
  Responder.mapDisplayedBehavior_parallel_zero_left _ _ _

example :
    Display.M.transport
        (Responder.mapBehavior_parallel_assoc
          (leftResponder.behavior 0) (rightResponder.behavior 5)
          (leftResponder.behavior 0))
      (Responder.mapDisplayedBehavior
        (Display.Lens.parallelSumAssoc leftDisplay rightDisplay leftDisplay)
        (Responder.parallelBehavior (leftResponder.behavior 0)
          (Responder.parallelBehavior
            (rightResponder.behavior 5) (leftResponder.behavior 0)))
        (Responder.parallelDisplayedBehavior leftDisplay
          (Display.parallelSum rightDisplay leftDisplay)
          (leftResponder.behavior 0) leftDisplayed
          (Responder.parallelBehavior
            (rightResponder.behavior 5) (leftResponder.behavior 0))
          (Responder.parallelDisplayedBehavior rightDisplay leftDisplay
            (rightResponder.behavior 5) rightDisplayed
            (leftResponder.behavior 0) leftDisplayed))) =
      Responder.parallelDisplayedBehavior
        (Display.parallelSum leftDisplay rightDisplay) leftDisplay
        (Responder.parallelBehavior
          (leftResponder.behavior 0) (rightResponder.behavior 5))
        (Responder.parallelDisplayedBehavior leftDisplay rightDisplay
          (leftResponder.behavior 0) leftDisplayed
          (rightResponder.behavior 5) rightDisplayed)
        (leftResponder.behavior 0) leftDisplayed :=
  Responder.mapDisplayedBehavior_parallel_assoc _ _ _ _ _ _ _ _ _

end PFunctor.ParallelDisplayedCoherenceCanary
