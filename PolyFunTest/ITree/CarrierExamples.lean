/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Basic

/-!
# Operation-first ITree carrier canaries

Concrete layers and coalgebras pin the raw `F + C α + X` representation to the
ergonomic pure/step/query view. Boolean query children are deliberately
distinct so a summand or continuation swap is observable.
-/

@[expose] public section

namespace ITree.CarrierExamples

abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

def pureLayer : (ITree.ViewPoly coinP Nat).Obj Nat :=
  ⟨.pure 7, PEmpty.elim⟩

def stepLayer : (ITree.ViewPoly coinP Nat).Obj Nat :=
  ⟨.step, fun _ => 11⟩

def queryLayer : (ITree.ViewPoly coinP Nat).Obj Nat :=
  ⟨.query PUnit.unit, fun answer => if answer then 13 else 17⟩

/-- Pack/unpack preserves each computational constructor. -/
example : ITree.unpack (ITree.pack pureLayer) = pureLayer := by simp
example : ITree.unpack (ITree.pack stepLayer) = stepLayer := by simp
example : ITree.unpack (ITree.pack queryLayer) = queryLayer := by simp

/-- Both directions of the raw/computational view equivalence are exercised on
an answer-dependent query layer. -/
example : ITree.viewEquiv.symm (ITree.viewEquiv (ITree.pack queryLayer)) =
    ITree.pack queryLayer := by
  simp

example : ITree.viewEquiv (ITree.viewEquiv.symm queryLayer) = queryLayer := by
  simp

/-! ## Constructor/destructor round trips -/

def leaf : ITree coinP Nat := ITree.pure 7
def delayed : ITree coinP Nat := ITree.step leaf
def branch : ITree coinP Nat :=
  ITree.query PUnit.unit fun answer => if answer then leaf else delayed

example : ITree.shape' (ITree.ofShape ⟨.pure 7, PEmpty.elim⟩) =
    (⟨.pure 7, PEmpty.elim⟩ : (ITree.ViewPoly coinP Nat).Obj (ITree coinP Nat)) := by
  exact ITree.shape'_ofShape _

example : ITree.shape' (ITree.ofShape ⟨.step, fun _ => leaf⟩) =
    (⟨.step, fun _ => leaf⟩ : (ITree.ViewPoly coinP Nat).Obj (ITree coinP Nat)) := by
  exact ITree.shape'_ofShape _

example : ITree.shape' (ITree.ofShape
    ⟨.query PUnit.unit, fun answer => if answer then leaf else delayed⟩) =
    (⟨.query PUnit.unit, fun answer => if answer then leaf else delayed⟩ :
      (ITree.ViewPoly coinP Nat).Obj (ITree coinP Nat)) := by
  exact ITree.shape'_ofShape _

example : ITree.ofShape (ITree.shape' leaf) = leaf := by simp
example : ITree.ofShape (ITree.shape' delayed) = delayed := by simp
example : ITree.ofShape (ITree.shape' branch) = branch := by simp

/-! ## Corecursor heads -/

def pureCoalgebra (_ : PUnit) : (ITree.ViewPoly coinP Nat).Obj PUnit :=
  ⟨.pure 19, PEmpty.elim⟩

def stepCoalgebra : Bool → (ITree.ViewPoly coinP Nat).Obj Bool
  | true => ⟨.step, fun _ => false⟩
  | false => ⟨.pure 23, PEmpty.elim⟩

def queryCoalgebra (_ : Bool) : (ITree.ViewPoly coinP Nat).Obj Bool :=
  ⟨.query PUnit.unit, fun answer => answer⟩

example : ITree.shape' (ITree.corec pureCoalgebra PUnit.unit) =
    ⟨.pure 19, PEmpty.elim⟩ := by
  rw [ITree.shape'_corec_apply]
  exact Sigma.ext rfl (heq_of_eq (funext fun direction => direction.elim))

example : ITree.shape' (ITree.corec stepCoalgebra true) =
    ⟨.step, fun _ => ITree.corec stepCoalgebra false⟩ := by
  rw [ITree.shape'_corec_apply]
  exact Sigma.ext rfl (heq_of_eq (funext fun direction => by cases direction; rfl))

example : ITree.shape' (ITree.corec queryCoalgebra true) =
    ⟨.query PUnit.unit, fun answer => ITree.corec queryCoalgebra answer⟩ := by
  rw [ITree.shape'_corec_apply]
  exact Sigma.ext rfl (heq_of_eq (funext fun _ => rfl))

/-! ## Relational corecursion -/

def leftLoop (_ : Bool) : (ITree.ViewPoly coinP Nat).Obj Bool :=
  ⟨.step, fun _ => false⟩

def rightLoop (_ : Nat) : (ITree.ViewPoly coinP Nat).Obj Nat :=
  ⟨.step, fun _ => 0⟩

/-- Distinct seed types and values generate the same infinite silent tree. -/
example : ITree.corec leftLoop true = ITree.corec rightLoop 37 := by
  apply ITree.corec_eq_corec leftLoop rightLoop (fun _ _ => True)
  · trivial
  · intro leftSeed rightSeed _
    exact ⟨.step, fun _ => false, fun _ => 0, rfl, rfl, fun _ => trivial⟩

end ITree.CarrierExamples
