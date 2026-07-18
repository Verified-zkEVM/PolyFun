/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Lens
public import PolyFun.PFunctor.Display.Parallel
public import PolyFun.PFunctor.Free.Parallel

/-!
# Structural fiberwise lenses for separable parallel displays

The separable display operation follows the symmetric-monoidal structure of
parallel sum.  This file lifts the base bifunctor, unitors, braiding, and
associator to `Display.Lens`; their `toHandler` maps are the corresponding
displayed structural handlers used by verified behavior.
-/

@[expose] public section

universe uA₁ uA₂ uA₃ uA₄ uA₅ uA₆ uB
  uC₁ uD₁ uC₂ uD₂ uC₃ uD₃ uC₄ uD₄ uC₅ uD₅ uC₆ uD₆

namespace PFunctor
namespace Display

namespace Lens

/-- Bifunctorial action of separable parallel displays on fiberwise lenses. -/
def parallelSumMap
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftBase : PFunctor.Lens P R} {rightBase : PFunctor.Lens Q V}
    (left : Display.Lens S U leftBase)
    (right : Display.Lens T W rightBase) :
    Display.Lens (Display.parallelSum S T) (Display.parallelSum U W)
      (PFunctor.Lens.parallelSumMap leftBase rightBase) where
  toPosition
    | .left a, contract => ULift.up (left.toPosition a contract.down)
    | .right b, contract => ULift.up (right.toPosition b contract.down)
    | .both a b, contract =>
        (left.toPosition a contract.1, right.toPosition b contract.2)
  toDirection
    | .left a, contract, answer, direction =>
        ULift.up (left.toDirection a contract.down answer direction.down)
    | .right b, contract, answer, direction =>
        ULift.up (right.toDirection b contract.down answer direction.down)
    | .both a b, contract, answer, direction =>
        (left.toDirection a contract.1 answer.1 direction.1,
          right.toDirection b contract.2 answer.2 direction.2)

@[simp] theorem parallelSumMap_toPosition_left
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftBase : PFunctor.Lens P R} {rightBase : PFunctor.Lens Q V}
    (left : Display.Lens S U leftBase)
    (right : Display.Lens T W rightBase) (a : P.A) (contract : S.position a) :
    (parallelSumMap left right).toPosition (.left a) (ULift.up contract) =
      ULift.up (left.toPosition a contract) :=
  rfl

@[simp] theorem parallelSumMap_toPosition_right
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftBase : PFunctor.Lens P R} {rightBase : PFunctor.Lens Q V}
    (left : Display.Lens S U leftBase)
    (right : Display.Lens T W rightBase) (b : Q.A) (contract : T.position b) :
    (parallelSumMap left right).toPosition (.right b) (ULift.up contract) =
      ULift.up (right.toPosition b contract) :=
  rfl

@[simp] theorem parallelSumMap_toPosition_both
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftBase : PFunctor.Lens P R} {rightBase : PFunctor.Lens Q V}
    (left : Display.Lens S U leftBase)
    (right : Display.Lens T W rightBase) (a : P.A) (b : Q.A)
    (leftContract : S.position a) (rightContract : T.position b) :
    (parallelSumMap left right).toPosition (.both a b)
        (leftContract, rightContract) =
      (left.toPosition a leftContract, right.toPosition b rightContract) :=
  rfl

@[simp] theorem parallelSumMap_toDirection_left
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftBase : PFunctor.Lens P R} {rightBase : PFunctor.Lens Q V}
    (left : Display.Lens S U leftBase)
    (right : Display.Lens T W rightBase) (a : P.A)
    (contract : S.position a) (answer : R.B (leftBase.toFunA a))
    (direction : U.direction (leftBase.toFunA a)
      (left.toPosition a contract) answer) :
    (parallelSumMap left right).toDirection (.left a) (ULift.up contract)
        answer (ULift.up direction) =
      ULift.up (left.toDirection a contract answer direction) :=
  rfl

@[simp] theorem parallelSumMap_toDirection_right
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftBase : PFunctor.Lens P R} {rightBase : PFunctor.Lens Q V}
    (left : Display.Lens S U leftBase)
    (right : Display.Lens T W rightBase) (b : Q.A)
    (contract : T.position b) (answer : V.B (rightBase.toFunA b))
    (direction : W.direction (rightBase.toFunA b)
      (right.toPosition b contract) answer) :
    (parallelSumMap left right).toDirection (.right b) (ULift.up contract)
        answer (ULift.up direction) =
      ULift.up (right.toDirection b contract answer direction) :=
  rfl

@[simp] theorem parallelSumMap_toDirection_both
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftBase : PFunctor.Lens P R} {rightBase : PFunctor.Lens Q V}
    (left : Display.Lens S U leftBase)
    (right : Display.Lens T W rightBase) (a : P.A) (b : Q.A)
    (leftContract : S.position a) (rightContract : T.position b)
    (answer : R.B (leftBase.toFunA a) × V.B (rightBase.toFunA b))
    (direction : U.direction (leftBase.toFunA a)
        (left.toPosition a leftContract) answer.1 ×
      W.direction (rightBase.toFunA b)
        (right.toPosition b rightContract) answer.2) :
    (parallelSumMap left right).toDirection (.both a b)
        (leftContract, rightContract) answer direction =
      (left.toDirection a leftContract answer.1 direction.1,
        right.toDirection b rightContract answer.2 direction.2) :=
  rfl

/-- Right unitor for separable parallel displays. -/
def parallelSumZero
    {P : PFunctor.{uA₁, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P) :
    Display.Lens (Display.parallelSum S Display.zero) S
      (PFunctor.Lens.parallelSumZero P) where
  toPosition
    | .left _, contract => contract.down
    | .right operation, _ => PEmpty.elim operation
    | .both _ operation, _ => PEmpty.elim operation
  toDirection
    | .left _, _, _, direction => ULift.up direction
    | .right operation, _, _, _ => PEmpty.elim operation
    | .both _ operation, _, _, _ => PEmpty.elim operation

@[simp] theorem parallelSumZero_toPosition
    {P : PFunctor.{uA₁, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (a : P.A) (contract : S.position a) :
    (parallelSumZero S).toPosition (.left a) (ULift.up contract) = contract :=
  rfl

@[simp] theorem parallelSumZero_toDirection
    {P : PFunctor.{uA₁, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (a : P.A) (contract : S.position a) (answer : P.B a)
    (direction : S.direction a contract answer) :
    (parallelSumZero S).toDirection (.left a) (ULift.up contract)
        answer direction = ULift.up direction :=
  rfl

/-- Left unitor for separable parallel displays. -/
def zeroParallelSum
    {P : PFunctor.{uA₁, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P) :
    Display.Lens (Display.parallelSum Display.zero S) S
      (PFunctor.Lens.zeroParallelSum P) where
  toPosition
    | .left operation, _ => PEmpty.elim operation
    | .right _, contract => contract.down
    | .both operation _, _ => PEmpty.elim operation
  toDirection
    | .left operation, _, _, _ => PEmpty.elim operation
    | .right _, _, _, direction => ULift.up direction
    | .both operation _, _, _, _ => PEmpty.elim operation

@[simp] theorem zeroParallelSum_toPosition
    {P : PFunctor.{uA₁, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (a : P.A) (contract : S.position a) :
    (zeroParallelSum S).toPosition (.right a) (ULift.up contract) = contract :=
  rfl

@[simp] theorem zeroParallelSum_toDirection
    {P : PFunctor.{uA₁, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (a : P.A) (contract : S.position a) (answer : P.B a)
    (direction : S.direction a contract answer) :
    (zeroParallelSum S).toDirection (.right a) (ULift.up contract)
        answer direction = ULift.up direction :=
  rfl

/-- Braiding for separable parallel displays. -/
def parallelSumComm
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    Display.Lens (Display.parallelSum S T) (Display.parallelSum T S)
      (PFunctor.Lens.parallelSumComm P Q) where
  toPosition
    | .left _, contract => ULift.up contract.down
    | .right _, contract => ULift.up contract.down
    | .both _ _, contract => contract.swap
  toDirection
    | .left _, _, _, direction => ULift.up direction.down
    | .right _, _, _, direction => ULift.up direction.down
    | .both _ _, _, _, direction => direction.swap

@[simp] theorem parallelSumComm_toPosition_left
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (a : P.A) (contract : S.position a) :
    (parallelSumComm S T).toPosition (.left a) (ULift.up contract) =
      ULift.up contract :=
  rfl

@[simp] theorem parallelSumComm_toPosition_right
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (b : Q.A) (contract : T.position b) :
    (parallelSumComm S T).toPosition (.right b) (ULift.up contract) =
      ULift.up contract :=
  rfl

@[simp] theorem parallelSumComm_toPosition_both
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (a : P.A) (b : Q.A) (left : S.position a) (right : T.position b) :
    (parallelSumComm S T).toPosition (.both a b) (left, right) =
      (right, left) :=
  rfl

@[simp] theorem parallelSumComm_toDirection_left
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (a : P.A) (contract : S.position a) (answer : P.B a)
    (direction : S.direction a contract answer) :
    (parallelSumComm S T).toDirection (.left a) (ULift.up contract)
        answer (ULift.up direction) = ULift.up direction :=
  rfl

@[simp] theorem parallelSumComm_toDirection_right
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (b : Q.A) (contract : T.position b) (answer : Q.B b)
    (direction : T.direction b contract answer) :
    (parallelSumComm S T).toDirection (.right b) (ULift.up contract)
        answer (ULift.up direction) = ULift.up direction :=
  rfl

@[simp] theorem parallelSumComm_toDirection_both
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (a : P.A) (b : Q.A) (left : S.position a) (right : T.position b)
    (answer : Q.B b × P.B a)
    (direction : T.direction b right answer.1 ×
      S.direction a left answer.2) :
    (parallelSumComm S T).toDirection (.both a b) (left, right)
        answer direction = direction.swap :=
  rfl

/-- Associator for separable parallel displays. -/
def parallelSumAssoc
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (U : Display.{uA₃, uB, uC₃, uD₃} R) :
    Display.Lens
      (Display.parallelSum (Display.parallelSum S T) U)
      (Display.parallelSum S (Display.parallelSum T U))
      (PFunctor.Lens.parallelSumAssoc P Q R) where
  toPosition
    | .left (.left _), contract => ULift.up contract.down.down
    | .left (.right _), contract =>
        ULift.up (ULift.up contract.down.down)
    | .left (.both _ _), contract =>
        (contract.down.1, ULift.up contract.down.2)
    | .right _, contract => ULift.up (ULift.up contract.down)
    | .both (.left _) _, contract =>
        (contract.1.down, ULift.up contract.2)
    | .both (.right _) _, contract =>
        ULift.up (contract.1.down, contract.2)
    | .both (.both _ _) _, contract =>
        (contract.1.1, (contract.1.2, contract.2))
  toDirection
    | .left (.left _), _, _, direction =>
        ULift.up (ULift.up direction.down)
    | .left (.right _), _, _, direction =>
        ULift.up (ULift.up direction.down.down)
    | .left (.both _ _), _, _, direction =>
        ULift.up (direction.1, direction.2.down)
    | .right _, _, _, direction => ULift.up direction.down.down
    | .both (.left _) _, _, _, direction =>
        (ULift.up direction.1, direction.2.down)
    | .both (.right _) _, _, _, direction =>
        (ULift.up direction.down.1, direction.down.2)
    | .both (.both _ _) _, _, _, direction =>
        ((direction.1, direction.2.1), direction.2.2)

/-- Complete forward-action equation for the displayed associator.  The
single equation deliberately exposes all seven nested `ParallelChoice`
branches and their `ULift` normalization. -/
@[simp] theorem parallelSumAssoc_toPosition
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (U : Display.{uA₃, uB, uC₃, uD₃} R) :
    (parallelSumAssoc S T U).toPosition =
      fun
      | .left (.left _), contract => ULift.up contract.down.down
      | .left (.right _), contract => ULift.up (ULift.up contract.down.down)
      | .left (.both _ _), contract =>
          (contract.down.1, ULift.up contract.down.2)
      | .right _, contract => ULift.up (ULift.up contract.down)
      | .both (.left _) _, contract =>
          (contract.1.down, ULift.up contract.2)
      | .both (.right _) _, contract =>
          ULift.up (contract.1.down, contract.2)
      | .both (.both _ _) _, contract =>
          (contract.1.1, (contract.1.2, contract.2)) :=
  rfl

/-- Complete contravariant-action equation for the displayed associator. -/
@[simp] theorem parallelSumAssoc_toDirection
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (U : Display.{uA₃, uB, uC₃, uD₃} R) :
    (parallelSumAssoc S T U).toDirection =
      fun
      | .left (.left _), _, _, direction =>
          ULift.up (ULift.up direction.down)
      | .left (.right _), _, _, direction =>
          ULift.up (ULift.up direction.down.down)
      | .left (.both _ _), _, _, direction =>
          ULift.up (direction.1, direction.2.down)
      | .right _, _, _, direction => ULift.up direction.down.down
      | .both (.left _) _, _, _, direction =>
          (ULift.up direction.1, direction.2.down)
      | .both (.right _) _, _, _, direction =>
          (ULift.up direction.down.1, direction.down.2)
      | .both (.both _ _) _, _, _, direction =>
          ((direction.1, direction.2.1), direction.2.2) :=
  rfl

/-! ## Structural lens coherence -/

/-- Bifunctorial identity coherence, observed canonically on total
polynomials. -/
@[simp] theorem parallelSumMap_id_total
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    TotalEq (parallelSumMap (id S) (id T))
      (id (Display.parallelSum S T)) := by
  apply PFunctor.Lens.ext_mapObj
  rintro ⟨operation, contract⟩
  cases operation <;> rfl

@[simp] theorem parallelSumMap_id
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    transport (PFunctor.Lens.parallelSumMap_id P Q)
        (parallelSumMap (id S) (id T)) =
      id (Display.parallelSum S T) :=
  transport_eq_of_totalEq (PFunctor.Lens.parallelSumMap_id P Q)
    _ _ (parallelSumMap_id_total S T)

/-- Bifunctorial composition coherence on total polynomials. -/
theorem parallelSumMap_comp_total
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {W : PFunctor.{uA₅, uB}} {X : PFunctor.{uA₆, uB}}
    {S₁ : Display.{uA₁, uB, uC₁, uD₁} P}
    {T₁ : Display.{uA₂, uB, uC₂, uD₂} Q}
    {S₂ : Display.{uA₃, uB, uC₃, uD₃} R}
    {T₂ : Display.{uA₄, uB, uC₄, uD₄} V}
    {S₃ : Display.{uA₅, uB, uC₅, uD₅} W}
    {T₃ : Display.{uA₆, uB, uC₆, uD₆} X}
    {firstLeftBase : PFunctor.Lens P R}
    {firstRightBase : PFunctor.Lens Q V}
    {secondLeftBase : PFunctor.Lens R W}
    {secondRightBase : PFunctor.Lens V X}
    (firstLeft : Display.Lens S₁ S₂ firstLeftBase)
    (firstRight : Display.Lens T₁ T₂ firstRightBase)
    (secondLeft : Display.Lens S₂ S₃ secondLeftBase)
    (secondRight : Display.Lens T₂ T₃ secondRightBase) :
    TotalEq
      (comp (parallelSumMap secondLeft secondRight)
        (parallelSumMap firstLeft firstRight))
      (parallelSumMap (comp secondLeft firstLeft)
        (comp secondRight firstRight)) := by
  apply PFunctor.Lens.ext_mapObj
  rintro ⟨operation, contract⟩
  cases operation <;> rfl

theorem parallelSumMap_comp
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {W : PFunctor.{uA₅, uB}} {X : PFunctor.{uA₆, uB}}
    {S₁ : Display.{uA₁, uB, uC₁, uD₁} P}
    {T₁ : Display.{uA₂, uB, uC₂, uD₂} Q}
    {S₂ : Display.{uA₃, uB, uC₃, uD₃} R}
    {T₂ : Display.{uA₄, uB, uC₄, uD₄} V}
    {S₃ : Display.{uA₅, uB, uC₅, uD₅} W}
    {T₃ : Display.{uA₆, uB, uC₆, uD₆} X}
    {firstLeftBase : PFunctor.Lens P R}
    {firstRightBase : PFunctor.Lens Q V}
    {secondLeftBase : PFunctor.Lens R W}
    {secondRightBase : PFunctor.Lens V X}
    (firstLeft : Display.Lens S₁ S₂ firstLeftBase)
    (firstRight : Display.Lens T₁ T₂ firstRightBase)
    (secondLeft : Display.Lens S₂ S₃ secondLeftBase)
    (secondRight : Display.Lens T₂ T₃ secondRightBase) :
    transport
        (PFunctor.Lens.parallelSumMap_comp secondLeftBase secondRightBase
          firstLeftBase firstRightBase)
        (comp (parallelSumMap secondLeft secondRight)
          (parallelSumMap firstLeft firstRight)) =
      parallelSumMap (comp secondLeft firstLeft)
        (comp secondRight firstRight) :=
  transport_eq_of_totalEq
    (PFunctor.Lens.parallelSumMap_comp secondLeftBase secondRightBase
      firstLeftBase firstRightBase) _ _
    (parallelSumMap_comp_total firstLeft firstRight secondLeft secondRight)

/-- The displayed braiding is involutive on total polynomials. -/
@[simp] theorem parallelSumComm_involutive_total
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    TotalEq
      (comp (parallelSumComm T S) (parallelSumComm S T))
      (id (Display.parallelSum S T)) := by
  apply PFunctor.Lens.ext_mapObj
  rintro ⟨operation, contract⟩
  cases operation <;> rfl

@[simp] theorem parallelSumComm_involutive
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    transport (PFunctor.Lens.parallelSumComm_involutive P Q)
        (comp (parallelSumComm T S) (parallelSumComm S T)) =
      id (Display.parallelSum S T) :=
  transport_eq_of_totalEq (PFunctor.Lens.parallelSumComm_involutive P Q)
    _ _ (parallelSumComm_involutive_total S T)

/-- Naturality of the displayed braiding on total polynomials. -/
theorem parallelSumComm_natural_total
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftBase : PFunctor.Lens P R} {rightBase : PFunctor.Lens Q V}
    (left : Display.Lens S U leftBase)
    (right : Display.Lens T W rightBase) :
    TotalEq
      (comp (parallelSumComm U W) (parallelSumMap left right))
      (comp (parallelSumMap right left) (parallelSumComm S T)) := by
  apply PFunctor.Lens.ext_mapObj
  rintro ⟨operation, contract⟩
  cases operation <;> rfl

theorem parallelSumComm_natural
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB, uC₃, uD₃} R}
    {W : Display.{uA₄, uB, uC₄, uD₄} V}
    {leftBase : PFunctor.Lens P R} {rightBase : PFunctor.Lens Q V}
    (left : Display.Lens S U leftBase)
    (right : Display.Lens T W rightBase) :
    transport (PFunctor.Lens.parallelSumComm_natural leftBase rightBase)
        (comp (parallelSumComm U W) (parallelSumMap left right)) =
      comp (parallelSumMap right left) (parallelSumComm S T) :=
  transport_eq_of_totalEq
    (PFunctor.Lens.parallelSumComm_natural leftBase rightBase) _ _
    (parallelSumComm_natural_total left right)

/-- Naturality of the displayed right unitor on total polynomials. -/
theorem parallelSumZero_natural_total
    {P : PFunctor.{uA₁, uB}} {R : PFunctor.{uA₂, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} R}
    {base : PFunctor.Lens P R} (displayed : Display.Lens S T base) :
    TotalEq
      (comp (parallelSumZero T)
        (parallelSumMap displayed (id Display.zero)))
      (comp displayed (parallelSumZero S)) := by
  apply PFunctor.Lens.ext_mapObj
  rintro ⟨operation, contract⟩
  cases operation with
  | left _ => rfl
  | right impossible => exact PEmpty.elim impossible
  | both _ impossible => exact PEmpty.elim impossible

theorem parallelSumZero_natural
    {P : PFunctor.{uA₁, uB}} {R : PFunctor.{uA₂, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} R}
    {base : PFunctor.Lens P R} (displayed : Display.Lens S T base) :
    transport (PFunctor.Lens.parallelSumZero_natural base)
        (comp (parallelSumZero T)
          (parallelSumMap displayed (id Display.zero))) =
      comp displayed (parallelSumZero S) :=
  transport_eq_of_totalEq (PFunctor.Lens.parallelSumZero_natural base)
    _ _ (parallelSumZero_natural_total displayed)

/-- Naturality of the displayed left unitor on total polynomials. -/
theorem zeroParallelSum_natural_total
    {P : PFunctor.{uA₁, uB}} {R : PFunctor.{uA₂, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} R}
    {base : PFunctor.Lens P R} (displayed : Display.Lens S T base) :
    TotalEq
      (comp (zeroParallelSum T)
        (parallelSumMap (id Display.zero) displayed))
      (comp displayed (zeroParallelSum S)) := by
  apply PFunctor.Lens.ext_mapObj
  rintro ⟨operation, contract⟩
  cases operation with
  | left impossible => exact PEmpty.elim impossible
  | right _ => rfl
  | both impossible _ => exact PEmpty.elim impossible

theorem zeroParallelSum_natural
    {P : PFunctor.{uA₁, uB}} {R : PFunctor.{uA₂, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} R}
    {base : PFunctor.Lens P R} (displayed : Display.Lens S T base) :
    transport (PFunctor.Lens.zeroParallelSum_natural base)
        (comp (zeroParallelSum T)
          (parallelSumMap (id Display.zero) displayed)) =
      comp displayed (zeroParallelSum S) :=
  transport_eq_of_totalEq (PFunctor.Lens.zeroParallelSum_natural base)
    _ _ (zeroParallelSum_natural_total displayed)

/-- Naturality of the displayed associator on total polynomials. -/
theorem parallelSumAssoc_natural_total
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}}
    {P' : PFunctor.{uA₄, uB}} {Q' : PFunctor.{uA₅, uB}}
    {R' : PFunctor.{uA₆, uB}}
    {S₁ : Display.{uA₁, uB, uC₁, uD₁} P}
    {T₁ : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U₁ : Display.{uA₃, uB, uC₃, uD₃} R}
    {S₂ : Display.{uA₄, uB, uC₄, uD₄} P'}
    {T₂ : Display.{uA₅, uB, uC₅, uD₅} Q'}
    {U₂ : Display.{uA₆, uB, uC₆, uD₆} R'}
    {leftBase : PFunctor.Lens P P'}
    {middleBase : PFunctor.Lens Q Q'}
    {rightBase : PFunctor.Lens R R'}
    (left : Display.Lens S₁ S₂ leftBase)
    (middle : Display.Lens T₁ T₂ middleBase)
    (right : Display.Lens U₁ U₂ rightBase) :
    TotalEq
      (comp (parallelSumAssoc S₂ T₂ U₂)
        (parallelSumMap (parallelSumMap left middle) right))
      (comp (parallelSumMap left (parallelSumMap middle right))
        (parallelSumAssoc S₁ T₁ U₁)) := by
  apply PFunctor.Lens.ext_mapObj
  rintro ⟨operation, contract⟩
  cases operation with
  | left operation => cases operation <;> rfl
  | right _ => rfl
  | both operation _ => cases operation <;> rfl

theorem parallelSumAssoc_natural
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}}
    {P' : PFunctor.{uA₄, uB}} {Q' : PFunctor.{uA₅, uB}}
    {R' : PFunctor.{uA₆, uB}}
    {S₁ : Display.{uA₁, uB, uC₁, uD₁} P}
    {T₁ : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U₁ : Display.{uA₃, uB, uC₃, uD₃} R}
    {S₂ : Display.{uA₄, uB, uC₄, uD₄} P'}
    {T₂ : Display.{uA₅, uB, uC₅, uD₅} Q'}
    {U₂ : Display.{uA₆, uB, uC₆, uD₆} R'}
    {leftBase : PFunctor.Lens P P'}
    {middleBase : PFunctor.Lens Q Q'}
    {rightBase : PFunctor.Lens R R'}
    (left : Display.Lens S₁ S₂ leftBase)
    (middle : Display.Lens T₁ T₂ middleBase)
    (right : Display.Lens U₁ U₂ rightBase) :
    transport
        (PFunctor.Lens.parallelSumAssoc_natural
          leftBase middleBase rightBase)
        (comp (parallelSumAssoc S₂ T₂ U₂)
          (parallelSumMap (parallelSumMap left middle) right)) =
      comp (parallelSumMap left (parallelSumMap middle right))
        (parallelSumAssoc S₁ T₁ U₁) :=
  transport_eq_of_totalEq
    (PFunctor.Lens.parallelSumAssoc_natural leftBase middleBase rightBase)
    _ _ (parallelSumAssoc_natural_total left middle right)

/-- Mac Lane's pentagon for the displayed forward associator. -/
theorem parallelSumAssoc_pentagon_total
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (U : Display.{uA₃, uB, uC₃, uD₃} R)
    (W : Display.{uA₄, uB, uC₄, uD₄} V) :
    TotalEq
      (comp (parallelSumMap (id S) (parallelSumAssoc T U W))
        (comp (parallelSumAssoc S (Display.parallelSum T U) W)
          (parallelSumMap (parallelSumAssoc S T U) (id W))))
      (comp (parallelSumAssoc S T (Display.parallelSum U W))
        (parallelSumAssoc (Display.parallelSum S T) U W)) := by
  apply PFunctor.Lens.ext_mapObj
  rintro ⟨operation, contract⟩
  all_goals
    cases operation with
    | left pqr =>
        cases pqr with
        | left pq => cases pq <;> rfl
        | right _ => rfl
        | both pq _ => cases pq <;> rfl
    | right _ => rfl
    | both pqr _ =>
        cases pqr with
        | left pq => cases pq <;> rfl
        | right _ => rfl
        | both pq _ => cases pq <;> rfl

theorem parallelSumAssoc_pentagon
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (U : Display.{uA₃, uB, uC₃, uD₃} R)
    (W : Display.{uA₄, uB, uC₄, uD₄} V) :
    transport (PFunctor.Lens.parallelSumAssoc_pentagon P Q R V)
        (comp (parallelSumMap (id S) (parallelSumAssoc T U W))
          (comp (parallelSumAssoc S (Display.parallelSum T U) W)
            (parallelSumMap (parallelSumAssoc S T U) (id W)))) =
      comp (parallelSumAssoc S T (Display.parallelSum U W))
        (parallelSumAssoc (Display.parallelSum S T) U W) :=
  transport_eq_of_totalEq
    (PFunctor.Lens.parallelSumAssoc_pentagon P Q R V) _ _
    (parallelSumAssoc_pentagon_total S T U W)

/-- Symmetric-monoidal hexagon for the displayed braiding and associator. -/
theorem parallelSum_hexagon_total
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (U : Display.{uA₃, uB, uC₃, uD₃} R) :
    TotalEq
      (comp (parallelSumAssoc T U S)
        (comp (parallelSumComm S (Display.parallelSum T U))
          (parallelSumAssoc S T U)))
      (comp (parallelSumMap (id T) (parallelSumComm S U))
        (comp (parallelSumAssoc T S U)
          (parallelSumMap (parallelSumComm S T) (id U)))) := by
  apply PFunctor.Lens.ext_mapObj
  rintro ⟨operation, contract⟩
  cases operation with
  | left operation => cases operation <;> rfl
  | right _ => rfl
  | both operation _ => cases operation <;> rfl

theorem parallelSum_hexagon
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (U : Display.{uA₃, uB, uC₃, uD₃} R) :
    transport (PFunctor.Lens.parallelSum_hexagon P Q R)
        (comp (parallelSumAssoc T U S)
          (comp (parallelSumComm S (Display.parallelSum T U))
            (parallelSumAssoc S T U))) =
      comp (parallelSumMap (id T) (parallelSumComm S U))
        (comp (parallelSumAssoc T S U)
          (parallelSumMap (parallelSumComm S T) (id U))) :=
  transport_eq_of_totalEq (PFunctor.Lens.parallelSum_hexagon P Q R) _ _
    (parallelSum_hexagon_total S T U)

/-- Triangle coherence for the displayed unitors and associator. -/
theorem parallelSum_triangle_total
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    TotalEq
      (parallelSumMap
        (parallelSumZero S : Display.Lens
          (Display.parallelSum S
            (Display.zero : Display (0 : PFunctor.{uA₄, uB}))) S
          (PFunctor.Lens.parallelSumZero P))
        (id T))
      (comp
        (parallelSumMap (id S)
          (zeroParallelSum T : Display.Lens
            (Display.parallelSum
              (Display.zero : Display (0 : PFunctor.{uA₄, uB})) T) T
            (PFunctor.Lens.zeroParallelSum Q)))
        (parallelSumAssoc S
          (Display.zero : Display (0 : PFunctor.{uA₄, uB})) T)) := by
  apply PFunctor.Lens.ext_mapObj
  rintro ⟨operation, contract⟩
  cases operation with
  | left pz =>
      cases pz with
      | left _ => rfl
      | right impossible => exact PEmpty.elim impossible
      | both _ impossible => exact PEmpty.elim impossible
  | right _ => rfl
  | both pz _ =>
      cases pz with
      | left _ => rfl
      | right impossible => exact PEmpty.elim impossible
      | both _ impossible => exact PEmpty.elim impossible

theorem parallelSum_triangle
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    transport (PFunctor.Lens.parallelSum_triangle P Q)
        (parallelSumMap
          (parallelSumZero S : Display.Lens
            (Display.parallelSum S
              (Display.zero : Display (0 : PFunctor.{uA₄, uB}))) S
            (PFunctor.Lens.parallelSumZero P))
          (id T)) =
      comp
        (parallelSumMap (id S)
          (zeroParallelSum T : Display.Lens
            (Display.parallelSum
              (Display.zero : Display (0 : PFunctor.{uA₄, uB})) T) T
            (PFunctor.Lens.zeroParallelSum Q)))
        (parallelSumAssoc S
          (Display.zero : Display (0 : PFunctor.{uA₄, uB})) T) :=
  transport_eq_of_totalEq (PFunctor.Lens.parallelSum_triangle P Q) _ _
    (parallelSum_triangle_total S T)

end Lens
end Display
end PFunctor
