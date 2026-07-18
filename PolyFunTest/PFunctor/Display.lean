/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display

/-! Worked examples for polynomial displays and their free extension. -/

@[expose] public section

namespace PFunctor.Display.Example

def Unary : PFunctor.{0, 0} where
  A := Bool
  B _ := PUnit

def contract : Display.{0, 0, 0, 0} Unary where
  position _ := PUnit
  direction _ _ _ := PUnit

def oneStep : FreeM Unary Nat :=
  .liftBind true fun _ => .pure 7

def oneStepData :
    FreeM.Displayed (contract.toDisplayedShape fun _ : Nat => PUnit.{1}) oneStep :=
  ⟨.unit, fun _ _ => contract.leaf (fun _ : Nat => PUnit.{1}) 7 .unit⟩

example :
    contract.bind oneStep oneStepData (fun n => .pure (n + 1))
      (fun _ _ => contract.leaf (fun _ : Nat => PUnit.{1}) _ .unit) =
      ⟨.unit, fun _ _ => contract.leaf (fun _ : Nat => PUnit.{1}) 8 .unit⟩ :=
  rfl

def identityHandler :
    Handler contract contract (fun a => FreeM.lift a) :=
  Handler.id contract

example :
    contract.liftM contract oneStep oneStepData
      (fun a => FreeM.lift a) identityHandler = oneStepData := by
  rfl

/-! The following example is deliberately non-constant in every local index:
the response type depends on the operation arity, displayed positions depend
on the same arity, and displayed directions depend on both the selected
position and the concrete response. -/

inductive DepOp where
  | query (arity : Nat)

def Dependent : PFunctor.{0, 0} where
  A := DepOp
  B
    | .query arity => Fin arity

def dependentContract : Display.{0, 0, 0, 0} Dependent where
  position
    | .query arity => Fin (arity + 1)
  direction
    | .query _, c, b => Fin (c.val + b.val + 1)

def dependentTree : FreeM Dependent Nat :=
  .liftBind (.query 2) fun b => .pure b.val

def dependentTreeData :
    FreeM.Displayed
      (dependentContract.toDisplayedShape fun _ : Nat => Nat) dependentTree :=
  ⟨⟨2, by omega⟩, fun b direction =>
    dependentContract.leaf (fun _ : Nat => Nat) b.val (b.val + direction.val)⟩

example :
    dependentContract.bind dependentTree dependentTreeData
      (fun n => .pure (n + 10))
      (fun n evidence =>
        dependentContract.leaf (fun _ : Nat => Nat) (n + 10) (evidence + 1)) =
      ⟨⟨2, by omega⟩, fun b direction =>
        dependentContract.leaf (fun _ : Nat => Nat) (b.val + 10)
          (b.val + direction.val + 1)⟩ := by
  rfl

example :
    dependentContract.transport (fun _ : Nat => Nat)
        (FreeM.liftM_lift_eq_self dependentTree)
        (dependentContract.liftM dependentContract dependentTree dependentTreeData
          (fun a => FreeM.lift a) (Handler.id dependentContract)) =
      dependentTreeData :=
  dependentContract.liftM_id dependentTree dependentTreeData

example :
    dependentContract.transport (fun _ : Nat => Nat)
        (FreeM.liftM_comp dependentTree (fun a => FreeM.lift a)
          (fun a => FreeM.lift a))
        (dependentContract.liftM dependentContract dependentTree
          (dependentContract.liftM dependentContract dependentTree dependentTreeData
            (fun a => FreeM.lift a) (Handler.id dependentContract))
          (fun a => FreeM.lift a) (Handler.id dependentContract)) =
      dependentContract.liftM dependentContract dependentTree dependentTreeData
        (fun a => (FreeM.lift a).liftM fun a => FreeM.lift a)
        ((Handler.id dependentContract).comp (Handler.id dependentContract)) :=
  dependentContract.liftM_comp dependentContract dependentContract
    dependentTree dependentTreeData (fun a => FreeM.lift a)
      (Handler.id dependentContract) (fun a => FreeM.lift a)
      (Handler.id dependentContract)

end PFunctor.Display.Example

/-! Universe-polymorphic smoke tests. These ensure operation, response,
displayed-position, displayed-direction, and leaf-value universes remain
independent in the public handler laws. -/

universe uA uA' uA'' uB uC uD uC' uD' uC'' uD'' uF uG

namespace PFunctor.Display.UniverseTest

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
  {R : PFunctor.{uA'', uB}}
  (S : Display.{uA, uB, uC, uD} P)
  (T : Display.{uA', uB, uC', uD'} Q)
  (U : Display.{uA'', uB, uC'', uD''} R)
  {E E' : Type uB} {F : E → Type uF} {G : E' → Type uG}

example (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedShape F) t) :=
  S.liftM_id t d

example (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedShape F) t)
    (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first)
    (second : (a : Q.A) → FreeM R (Q.B a))
    (dsecond : Handler T U second) :=
  S.liftM_comp T U t d first dfirst second dsecond

example (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedShape F) t)
    (g : E → FreeM P E')
    (dg : (x : E) → F x → FreeM.Displayed (S.toDisplayedShape G) (g x))
    (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first) :=
  S.liftM_bind T t d g dg first dfirst

example (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first) (a : P.A) (c : S.position a) :=
  Handler.id_comp_apply dfirst a c

example (first : (a : P.A) → FreeM Q (P.B a))
    (dfirst : Handler S T first) (a : P.A) (c : S.position a) :=
  Handler.comp_id_apply dfirst a c

end PFunctor.Display.UniverseTest
