/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Equiv.Basic

/-!
# Polynomial Universe-Lifting Equivalence Examples

These examples instantiate every lift boundary at distinct universes and
observe both branches and both directions of the sum and product equivalences.
-/

@[expose] public section

namespace PFunctor.EquivUniverseCanary

open scoped PFunctor

abbrev Left : PFunctor.{1, 2} where
  A := ULift.{1, 0} Bool
  B := fun _ => ULift.{2, 0} (Fin 2)

abbrev RightSum : PFunctor.{3, 2} where
  A := ULift.{3, 0} (Fin 3)
  B := fun _ => ULift.{2, 0} (Fin 5)

abbrev RightProd : PFunctor.{3, 4} where
  A := ULift.{3, 0} (Fin 3)
  B := fun _ => ULift.{4, 0} (Fin 5)

def leftPosition : Left.A := ULift.up true

def rightSumPosition : RightSum.A := ULift.up 1

def rightProdPosition : RightProd.A := ULift.up 2

def leftDirection : Left.B leftPosition := ULift.up 1

def rightSumDirection : RightSum.B rightSumPosition := ULift.up 3

def rightProdDirection : RightProd.B rightProdPosition := ULift.up 4

abbrev liftEquiv := PFunctor.Equiv.uliftEquiv.{7, 8} (P := Left)

example : liftEquiv.equivA leftPosition = ULift.up leftPosition := rfl

example : liftEquiv.equivA.symm (ULift.up leftPosition) = leftPosition := rfl

example : liftEquiv.equivB leftPosition leftDirection = ULift.up leftDirection := rfl

example : (liftEquiv.equivB leftPosition).symm (ULift.up leftDirection) = leftDirection := rfl

abbrev iteratedLiftEquiv :=
  PFunctor.Equiv.uliftUliftEquiv.{1, 2, 3, 4, 5, 6} Left

example :
    iteratedLiftEquiv.equivA (ULift.up (ULift.up leftPosition)) =
      ULift.up leftPosition :=
  rfl

example :
    iteratedLiftEquiv.equivA.symm (ULift.up leftPosition) =
      ULift.up (ULift.up leftPosition) :=
  rfl

example :
    iteratedLiftEquiv.equivB (ULift.up (ULift.up leftPosition))
        (ULift.up (ULift.up leftDirection)) =
      ULift.up leftDirection :=
  rfl

example :
    (iteratedLiftEquiv.equivB (ULift.up (ULift.up leftPosition))).symm
        (ULift.up leftDirection) =
      ULift.up (ULift.up leftDirection) :=
  rfl

abbrev sumEquiv :=
  PFunctor.Equiv.uliftSumEquiv.{4, 5, 6, 7, 8} (P := Left) RightSum

example :
    sumEquiv.equivA (ULift.up (.inl leftPosition)) =
      .inl (ULift.up leftPosition) :=
  rfl

example :
    sumEquiv.equivA (ULift.up (.inr rightSumPosition)) =
      .inr (ULift.up rightSumPosition) :=
  rfl

example :
    sumEquiv.equivA.symm (.inl (ULift.up leftPosition)) =
      ULift.up (.inl leftPosition) :=
  rfl

example :
    sumEquiv.equivA.symm (.inr (ULift.up rightSumPosition)) =
      ULift.up (.inr rightSumPosition) :=
  rfl

example :
    sumEquiv.equivB (ULift.up (.inl leftPosition)) (ULift.up leftDirection) =
      ULift.up leftDirection :=
  rfl

example :
    sumEquiv.equivB (ULift.up (.inr rightSumPosition)) (ULift.up rightSumDirection) =
      ULift.up rightSumDirection :=
  rfl

example :
    (sumEquiv.equivB (ULift.up (.inl leftPosition))).symm (ULift.up leftDirection) =
      ULift.up leftDirection :=
  rfl

example :
    (sumEquiv.equivB (ULift.up (.inr rightSumPosition))).symm
        (ULift.up rightSumDirection) =
      ULift.up rightSumDirection :=
  rfl

abbrev prodEquiv :=
  PFunctor.Equiv.uliftProdEquiv.{5, 6, 7, 8, 9, 10} (P := Left) RightProd

example :
    prodEquiv.equivA (ULift.up (leftPosition, rightProdPosition)) =
      (ULift.up leftPosition, ULift.up rightProdPosition) :=
  rfl

example :
    prodEquiv.equivA.symm (ULift.up leftPosition, ULift.up rightProdPosition) =
      ULift.up (leftPosition, rightProdPosition) :=
  rfl

example :
    prodEquiv.equivB (ULift.up (leftPosition, rightProdPosition))
        (ULift.up (.inl leftDirection)) =
      .inl (ULift.up leftDirection) :=
  rfl

example :
    prodEquiv.equivB (ULift.up (leftPosition, rightProdPosition))
        (ULift.up (.inr rightProdDirection)) =
      .inr (ULift.up rightProdDirection) :=
  rfl

example :
    (prodEquiv.equivB (ULift.up (leftPosition, rightProdPosition))).symm
        (.inl (ULift.up leftDirection)) =
      ULift.up (.inl leftDirection) :=
  rfl

example :
    (prodEquiv.equivB (ULift.up (leftPosition, rightProdPosition))).symm
        (.inr (ULift.up rightProdDirection)) =
      ULift.up (.inr rightProdDirection) :=
  rfl

end PFunctor.EquivUniverseCanary
