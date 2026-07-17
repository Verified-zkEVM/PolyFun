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
  fun a c =>
    ⟨c, fun b d => contract.leaf (contract.direction a c) b d⟩

example :
    contract.mapHandler contract oneStep oneStepData
      (fun a => FreeM.lift a) identityHandler = oneStepData := by
  rfl

end PFunctor.Display.Example
