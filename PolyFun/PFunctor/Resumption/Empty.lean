/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption
public import PolyFun.PFunctor.M.Vertex

/-!
# Non-returning resumptions and M-types

When the return type is empty, the return summand of a resumption disappears.
Consequently `Resumption P PEmpty` is exactly the behavior-tree M-type `M P`.
-/

@[expose] public section

universe uA uB uR

namespace PFunctor
namespace M

variable {P : PFunctor.{uA, uB}}

/-- Eliminate the empty return summand from the resumption polynomial. -/
def emptyResumptionPolyEquiv :
    Lens.Equiv.{max uA uR, uB, uA, uB}
      (P + C.{uR, uB} PEmpty.{uR + 1}) P := by
  simpa only [C_empty] using
    (Lens.Equiv.sumZero (P := P) : Lens.Equiv.{max uA uR, uB, uA, uB}
      (P + (0 : PFunctor.{uR, uB})) P)

/-- Regard a behavior tree as a resumption that can only issue queries. -/
def toEmptyResumption (tree : M P) : Resumption P PEmpty.{uR + 1} :=
  M.mapLens (emptyResumptionPolyEquiv (P := P)).invLens tree

/-- Forget the impossible return case of an empty-valued resumption. -/
def ofEmptyResumption
    (computation : Resumption P PEmpty.{uR + 1}) : M P :=
  M.mapLens (emptyResumptionPolyEquiv (P := P)).toLens computation

@[simp] theorem ofEmptyResumption_toEmptyResumption (tree : M P) :
    ofEmptyResumption (toEmptyResumption tree :
      Resumption P PEmpty.{uR + 1}) = tree := by
  unfold ofEmptyResumption toEmptyResumption
  rw [← M.mapLens_comp,
    (emptyResumptionPolyEquiv (P := P)).right_inv,
    M.mapLens_id]

@[simp] theorem toEmptyResumption_ofEmptyResumption
    (computation : Resumption P PEmpty.{uR + 1}) :
    toEmptyResumption (ofEmptyResumption computation) = computation := by
  unfold ofEmptyResumption toEmptyResumption
  rw [← M.mapLens_comp,
    (emptyResumptionPolyEquiv (P := P)).left_inv,
    M.mapLens_id]

/-- Behavior trees are exactly empty-valued resumptions. -/
def equivEmptyResumption :
    M P ≃ Resumption P PEmpty.{uR + 1} where
  toFun := toEmptyResumption
  invFun := ofEmptyResumption
  left_inv := ofEmptyResumption_toEmptyResumption
  right_inv := toEmptyResumption_ofEmptyResumption

end M
end PFunctor
