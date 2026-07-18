/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Basic
public import PolyFun.PFunctor.Parallel

/-!
# One-or-both polynomial displays

An arbitrary display over `P ∥ Q` has three independent components: unary
displays over `P` and `Q`, and a joint display over `P ⊗ Q`.  The joint
component is where genuinely relational preconditions and postconditions
live.  The binary `Display.parallelSum` from Aberlé's executable development
is the separable specialization whose joint evidence is the product of the
two unary displays.
-/

@[expose] public section

universe uA₁ uA₂ uB uC uD uC₁ uD₁ uC₂ uD₂

namespace PFunctor
namespace Display

/-- Separable tensor of two unary displays over the Dirichlet tensor.

This is the product specification used by Aberlé's concrete `r ∥Dep s`.
An arbitrary (and potentially genuinely relational) specification for a
simultaneous query is instead any `Display (P ⊗ Q)`. -/
def tensor {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    Display (P ⊗ Q) where
  position operation := S.position operation.1 × T.position operation.2
  direction operation contract answer :=
    S.direction operation.1 contract.1 answer.1 ×
      T.direction operation.2 contract.2 answer.2

@[simp]
theorem tensor_position
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (operation : (P ⊗ Q).A) :
    (tensor S T).position operation =
      (S.position operation.1 × T.position operation.2) :=
  rfl

@[simp]
theorem tensor_direction
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (operation : (P ⊗ Q).A) (contract : (tensor S T).position operation)
    (answer : (P ⊗ Q).B operation) :
    (tensor S T).direction operation contract answer =
      (S.direction operation.1 contract.1 answer.1 ×
        T.direction operation.2 contract.2 answer.2) :=
  rfl

/-! ## General relational decomposition -/

/-- Assemble a display over `P ∥ Q` from its unary-left, unary-right, and
joint components.  Unlike `parallelSum`, the joint display is supplied
independently and may relate the two operations and their answers. -/
def parallelSumComponents
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC, uD} P)
    (right : Display.{uA₂, uB, uC, uD} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC, uD} (P ⊗ Q)) :
    Display.{max uA₁ uA₂, uB, uC, uD} (P ∥ Q) where
  position
    | .left a => left.position a
    | .right b => right.position b
    | .both a b => joint.position (a, b)
  direction operation contract answer := match operation with
    | .left a => left.direction a contract answer
    | .right b => right.direction b contract answer
    | .both a b => joint.direction (a, b) contract answer

/-- Restrict a parallel display to left-only operations. -/
def leftComponent
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{max uA₁ uA₂, uB, uC, uD} (P ∥ Q)) :
    Display.{uA₁, uB, uC, uD} P where
  position a := S.position (.left a)
  direction a contract answer := S.direction (.left a) contract answer

/-- Restrict a parallel display to right-only operations. -/
def rightComponent
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{max uA₁ uA₂, uB, uC, uD} (P ∥ Q)) :
    Display.{uA₂, uB, uC, uD} Q where
  position b := S.position (.right b)
  direction b contract answer := S.direction (.right b) contract answer

/-- Restrict a parallel display to simultaneous operations.  This component
is an arbitrary display over `P ⊗ Q`, hence can express relational contracts
that do not factor into unary evidence. -/
def jointComponent
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{max uA₁ uA₂, uB, uC, uD} (P ∥ Q)) :
    Display.{max uA₁ uA₂, uB, uC, uD} (P ⊗ Q) where
  position operation := S.position (.both operation.1 operation.2)
  direction operation contract answer :=
    S.direction (.both operation.1 operation.2) contract answer

@[simp] theorem parallelSumComponents_position_left
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC, uD} P)
    (right : Display.{uA₂, uB, uC, uD} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC, uD} (P ⊗ Q)) (a : P.A) :
    (parallelSumComponents left right joint).position (.left a) =
      left.position a := rfl

@[simp] theorem parallelSumComponents_position_right
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC, uD} P)
    (right : Display.{uA₂, uB, uC, uD} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC, uD} (P ⊗ Q)) (b : Q.A) :
    (parallelSumComponents left right joint).position (.right b) =
      right.position b := rfl

@[simp] theorem parallelSumComponents_position_both
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC, uD} P)
    (right : Display.{uA₂, uB, uC, uD} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC, uD} (P ⊗ Q))
    (a : P.A) (b : Q.A) :
    (parallelSumComponents left right joint).position (.both a b) =
      joint.position (a, b) := rfl

@[simp] theorem parallelSumComponents_direction_left
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC, uD} P)
    (right : Display.{uA₂, uB, uC, uD} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC, uD} (P ⊗ Q))
    (a : P.A) (contract : left.position a) (answer : P.B a) :
    (parallelSumComponents left right joint).direction
        (.left a) contract answer = left.direction a contract answer := rfl

@[simp] theorem parallelSumComponents_direction_right
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC, uD} P)
    (right : Display.{uA₂, uB, uC, uD} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC, uD} (P ⊗ Q))
    (b : Q.A) (contract : right.position b) (answer : Q.B b) :
    (parallelSumComponents left right joint).direction
        (.right b) contract answer = right.direction b contract answer := rfl

@[simp] theorem parallelSumComponents_direction_both
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC, uD} P)
    (right : Display.{uA₂, uB, uC, uD} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC, uD} (P ⊗ Q))
    (a : P.A) (b : Q.A) (contract : joint.position (a, b))
    (answer : P.B a × Q.B b) :
    (parallelSumComponents left right joint).direction
        (.both a b) contract answer =
      joint.direction (a, b) contract answer := rfl

@[simp] theorem leftComponent_parallelSumComponents
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC, uD} P)
    (right : Display.{uA₂, uB, uC, uD} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC, uD} (P ⊗ Q)) :
    leftComponent (parallelSumComponents left right joint) = left := rfl

@[simp] theorem rightComponent_parallelSumComponents
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC, uD} P)
    (right : Display.{uA₂, uB, uC, uD} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC, uD} (P ⊗ Q)) :
    rightComponent (parallelSumComponents left right joint) = right := rfl

@[simp] theorem jointComponent_parallelSumComponents
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC, uD} P)
    (right : Display.{uA₂, uB, uC, uD} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC, uD} (P ⊗ Q)) :
    jointComponent (parallelSumComponents left right joint) = joint := by
  cases joint
  rfl

/-- Reassembling the three restrictions of an arbitrary parallel display
recovers the original display.  Together with the component simplification
laws, this states the full three-way decomposition rather than merely
providing constructors in each direction. -/
@[simp] theorem parallelSumComponents_components
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{max uA₁ uA₂, uB, uC, uD} (P ∥ Q)) :
    parallelSumComponents (leftComponent S) (rightComponent S)
      (jointComponent S) = S := by
  cases S with
  | mk position direction =>
      apply Display.ext
      · funext operation
        cases operation <;> rfl
      · apply Function.hfunext rfl
        intro operation operation' hOperation
        cases hOperation
        cases operation <;>
          apply Function.hfunext rfl <;>
          intro contract contract' hContract <;>
          cases hContract <;>
          apply Function.hfunext rfl <;>
          intro answer answer' hAnswer <;>
          cases hAnswer <;>
          exact HEq.rfl

/-- Separable one-or-both parallel sum of displays, corresponding to the
paper's concrete `r ∥Dep s`.  The joint branch is the product display
`tensor S T`; use `parallelSumComponents` for an independently chosen,
genuinely relational joint component. -/
def parallelSum
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    Display.{max uA₁ uA₂, uB, max uC₁ uC₂, max uD₁ uD₂}
      (P ∥ Q) where
  position
    | .left a => ULift (S.position a)
    | .right b => ULift (T.position b)
    | .both a b => S.position a × T.position b
  direction operation contract answer := match operation with
    | .left a => ULift (S.direction a contract.down answer)
    | .right b => ULift (T.direction b contract.down answer)
    | .both a b =>
        S.direction a contract.1 answer.1 ×
          T.direction b contract.2 answer.2

@[simp]
theorem parallelSum_position_left
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) (a : P.A) :
    (parallelSum S T).position (.left a) = ULift (S.position a) :=
  rfl

@[simp]
theorem parallelSum_position_right
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) (b : Q.A) :
    (parallelSum S T).position (.right b) = ULift (T.position b) :=
  rfl

@[simp]
theorem parallelSum_position_both
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (a : P.A) (b : Q.A) :
    (parallelSum S T).position (.both a b) =
      (S.position a × T.position b) :=
  rfl

@[simp]
theorem parallelSum_direction_left
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (a : P.A) (contract : ULift (S.position a))
    (answer : (P ∥ Q).B (.left a)) :
    (parallelSum S T).direction (.left a) contract answer =
      ULift (S.direction a contract.down answer) :=
  rfl

@[simp]
theorem parallelSum_direction_right
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (b : Q.A) (contract : ULift (T.position b))
    (answer : (P ∥ Q).B (.right b)) :
    (parallelSum S T).direction (.right b) contract answer =
      ULift (T.direction b contract.down answer) :=
  rfl

@[simp]
theorem parallelSum_direction_both
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (a : P.A) (b : Q.A)
    (contract : S.position a × T.position b)
    (answer : (P ∥ Q).B (.both a b)) :
    (parallelSum S T).direction (.both a b) contract answer =
      (S.direction a contract.1 answer.1 ×
        T.direction b contract.2 answer.2) :=
  rfl

end Display
end PFunctor
