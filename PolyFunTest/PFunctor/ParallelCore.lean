/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Parallel

/-!
# Regression tests for one-or-both parallel polynomials and displays

These examples distinguish the left, right, and simultaneous branches,
exercise relational joint evidence, and pin the heterogeneous universe
boundary of component assembly.
-/

@[expose] public section

namespace PFunctor.ParallelCoreCanary

open ParallelChoice

abbrev Left : PFunctor := ⟨Bool, fun _ => Bool⟩

abbrev Right : PFunctor := ⟨Nat, fun _ => String⟩

example : (Left ∥ Right).B (.left true) = Bool :=
  rfl

example : (Left ∥ Right).B (.right 3) = String :=
  rfl

example : (Left ∥ Right).B (.both false 4) = (Bool × String) :=
  rfl

example :
    (ParallelChoice.comm Bool Nat) (.both true 7) = .both 7 true :=
  rfl

example :
    (ParallelChoice.assoc Bool Nat String) (.both (.left true) "x") =
      .both true (.right "x") :=
  rfl

example :
    (PFunctor.Equiv.parallelSumComm Left Right).equivB
      (.both true 3) (false, "x") = ("x", false) :=
  rfl

example :
    ((PFunctor.Equiv.parallelSumComm Left Right).equivB
      (.both true 3)).symm ("x", false) = (false, "x") :=
  rfl

example :
    (PFunctor.Equiv.parallelSumAssoc Left Right Left).equivB
      (.both (.both true 3) false) ((false, "x"), true) =
        (false, ("x", true)) :=
  rfl

example :
    ((PFunctor.Equiv.parallelSumAssoc Left Right Left).equivB
      (.both (.both true 3) false)).symm (false, ("x", true)) =
        ((false, "x"), true) :=
  rfl

example :
    (PFunctor.Equiv.parallelSumDecomposition Left Right).equivA
      (.both true 3) = Sum.inr (true, 3) :=
  rfl

example :
    (PFunctor.Equiv.parallelSumDecomposition Left Right).equivA.symm
      (Sum.inr (true, 3)) = .both true 3 :=
  rfl

example :
    (PFunctor.Equiv.parallelSumDecomposition Left Right).equivB
      (.both true 3) (false, "x") = (false, "x") :=
  rfl

example :
    ((PFunctor.Equiv.parallelSumDecomposition Left Right).equivB
      (.both true 3)).symm (false, "x") = (false, "x") :=
  rfl

example :
    (PFunctor.Equiv.parallelSumZero Left).equivB
      (.left true) false = false :=
  rfl

example :
    (PFunctor.Equiv.zeroParallelSum Right).equivB
      (.right 3) "x" = "x" :=
  rfl

abbrev leftDisplay : Display Left where
  position _ := Bool
  direction _ contract answer := if contract = answer then PUnit else PEmpty

abbrev rightDisplay : Display Right where
  position _ := Nat
  direction _ contract answer := if contract = answer.length then PUnit else PEmpty

/-- The joint component is deliberately relational rather than a product of
the two unary position fibers. -/
abbrev jointDisplay : Display (Left ⊗ Right) where
  position operation :=
    if operation.1 = decide (operation.2 = 0) then PUnit else PEmpty
  direction _ _ answer :=
    if answer.1 = decide answer.2.isEmpty then PUnit else PEmpty

def tensorDirectionWitness :
    (Display.tensor leftDisplay rightDisplay).direction
      (true, 2) (true, 1) (true, "a") :=
  (PUnit.unit, PUnit.unit)

example :
    (Display.parallelSumComponents leftDisplay rightDisplay jointDisplay).position
      (.left true) = Bool :=
  rfl

example :
    (Display.parallelSumComponents leftDisplay rightDisplay jointDisplay).position
      (.both false 0) = PEmpty :=
  rfl

example : Display.jointComponent
    (Display.parallelSumComponents leftDisplay rightDisplay jointDisplay) =
      jointDisplay :=
  Display.jointComponent_parallelSumComponents _ _ _

example :
    Display.parallelSumComponents
        (Display.leftComponent
          (Display.parallelSumComponents leftDisplay rightDisplay jointDisplay))
        (Display.rightComponent
          (Display.parallelSumComponents leftDisplay rightDisplay jointDisplay))
        (Display.jointComponent
          (Display.parallelSumComponents leftDisplay rightDisplay jointDisplay)) =
      Display.parallelSumComponents leftDisplay rightDisplay jointDisplay :=
  Display.parallelSumComponents_components _

example :
    (Display.parallelSum leftDisplay rightDisplay).position (.both true 2) =
      (Bool × Nat) :=
  rfl

example (e : (Display.parallelSum leftDisplay rightDisplay).direction
    (.both true 2) (true, 1) (false, "a")) : False := by
  change PEmpty × PUnit at e
  exact PEmpty.elim e.1

universe uA₁ uA₂ uB uC₁ uD₁ uC₂ uD₂ uC₃ uD₃

/-- Component assembly preserves independent evidence universes by lifting
only at the common parallel boundary. -/
def heterogeneousComponents
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC₁, uD₁} P)
    (right : Display.{uA₂, uB, uC₂, uD₂} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC₃, uD₃} (P ⊗ Q)) :
    Display.{max uA₁ uA₂, uB, max uC₁ uC₂ uC₃,
      max uD₁ uD₂ uD₃} (P ∥ Q) :=
  Display.parallelSumComponentsLift left right joint

def heterogeneousLeftPosition
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC₁, uD₁} P)
    (right : Display.{uA₂, uB, uC₂, uD₂} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC₃, uD₃} (P ⊗ Q))
    (operation : P.A) :
    left.position operation ≃
      (heterogeneousComponents left right joint).position (.left operation) :=
  Display.parallelSumComponentsLiftPositionLeftEquiv
    left right joint operation

def heterogeneousJointDirection
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC₁, uD₁} P)
    (right : Display.{uA₂, uB, uC₂, uD₂} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC₃, uD₃} (P ⊗ Q))
    (a : P.A) (b : Q.A) (contract : joint.position (a, b))
    (answer : P.B a × Q.B b) :
    joint.direction (a, b) contract answer ≃
      (heterogeneousComponents left right joint).direction
        (.both a b) (ULift.up.{max uC₁ uC₂} contract) answer :=
  Display.parallelSumComponentsLiftDirectionBothEquiv
    left right joint a b contract answer

def heterogeneousRightDirection
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC₁, uD₁} P)
    (right : Display.{uA₂, uB, uC₂, uD₂} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC₃, uD₃} (P ⊗ Q))
    (operation : Q.A) (contract : right.position operation)
    (answer : Q.B operation) :
    right.direction operation contract answer ≃
      (heterogeneousComponents left right joint).direction
        (.right operation) (ULift.up.{max uC₁ uC₃} contract) answer :=
  Display.parallelSumComponentsLiftDirectionRightEquiv
    left right joint operation contract answer

end PFunctor.ParallelCoreCanary
