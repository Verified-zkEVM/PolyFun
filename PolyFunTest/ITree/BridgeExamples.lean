/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module


public import PolyFun.ITree.PatternRunsOnMatter
public import PolyFun.PFunctor.Resumption.Empty

/-! # Fixed-point and ITree bridge smoke tests -/

@[expose] public section

namespace ITree.BridgeExamples

open PFunctor

@[reducible] def Choice : PFunctor := ⟨Bool, fun _ => Bool⟩

def finite : FreeM Choice Nat :=
  FreeM.liftBind true fun answer => FreeM.pure (if answer then 1 else 0)

example : FreeM.toITree finite =
    ITree.query true fun answer => ITree.pure (if answer then 1 else 0) := by
  change FreeM.toITree
      (FreeM.liftBind (P := Choice) true fun answer : Bool =>
        FreeM.pure (if answer then 1 else 0)) = _
  rw [FreeM.toITree_liftBind]
  congr 1
  funext answer
  exact FreeM.toITree_pure _

example : ITree.TauFree (FreeM.toITree finite) := by
  simp

example : Resumption.WellFounded (FreeM.toResumption finite) :=
  FreeM.wellFounded_toResumption finite

example :
    (FreeM.equivWellFoundedResumption finite).1 =
      FreeM.toResumption finite := by
  simp

example (tree : ITree Choice Nat) :
    ITree.ofResumptionWithTau (ITree.toResumptionWithTau tree) = tree := by
  simp

example (tree : ITree Choice Nat) :
    ITree.toResumptionWithTau (ITree.step tree) =
      Resumption.query (Sum.inr PUnit.unit)
        (fun _ => ITree.toResumptionWithTau tree) := by
  simp

example (handler : PFunctor.Handler (FreeM Choice) Choice) :
    ITree.WeakBisim
      (FreeM.toITree (finite.liftM handler))
      (ITree.simulate (ITree.Handler.ofFree handler) (FreeM.toITree finite)) :=
  FreeM.toITree_liftM_weakBisim handler finite

example (tree : M Choice) :
    M.ofEmptyResumption (M.toEmptyResumption tree) = tree := by
  simp

end ITree.BridgeExamples
