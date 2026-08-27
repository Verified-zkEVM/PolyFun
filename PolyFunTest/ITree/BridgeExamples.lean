/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module


public import PolyFun.ITree.PatternRunsOnMatter
public import PolyFun.ITree.Unfold
public import PolyFun.PFunctor.Resumption.Empty

/-! # Fixed-point and ITree bridge smoke tests -/

@[expose] public section

namespace ITree.BridgeExamples

open PFunctor

attribute [local implicit_reducible] PFunctor.Obj

@[reducible] def Choice : PFunctor := ⟨Bool, fun _ => Bool⟩

def finite : FreeM Choice Nat :=
  FreeM.liftBind true fun answer => FreeM.pure (if answer then 1 else 0)

/-- A non-well-founded resumption whose visible position and next seed both
depend on observable Boolean data. -/
def infinite (seed : Bool) : Resumption Choice Nat :=
  Resumption.corec
    (fun current => Sum.inr
      ⟨current, fun answer => xor current answer⟩) seed

/-- A non-returning M-tree with the same position- and answer-sensitive
branching used to pin the empty-resumption bridge. -/
def behavior (seed : Bool) : M Choice :=
  M.corec (fun current =>
    ⟨current, fun answer => xor current answer⟩) seed

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

/-- The unrestricted resumption view commutes with the tau-free embedding even
for a genuinely infinite, answer-dependent resumption. -/
example (seed : Bool) :
    ITree.toResumptionWithTau (Resumption.toITree (infinite seed)) =
      Resumption.mapLens
        (Lens.inl (P := Choice) (Q := PFunctor.y)) (infinite seed) :=
  ITree.toResumptionWithTau_toITree (infinite seed)

/-- The direct M-tree ITree semantics agrees with the route through an
empty-valued resumption on nontrivial coinductive behavior. -/
example (seed : Bool) :
    M.toITree (behavior seed) =
      Resumption.toITree (M.toEmptyResumption (behavior seed)) :=
  M.toITree_eq_toITree_toEmptyResumption (behavior seed)

/-- The empty-resumption producer preserves the visible position and the
answer-selected child rather than merely participating in a round trip. -/
example (seed : Bool) :
    Resumption.dest (M.toEmptyResumption (behavior seed)) =
      Sum.inr ⟨seed, fun answer =>
        M.toEmptyResumption (behavior (xor seed answer))⟩ := by
  rw [M.dest_toEmptyResumption]
  change (Sum.inr
      (⟨(M.dest (behavior seed)).1,
        fun direction => M.toEmptyResumption ((M.dest (behavior seed)).2 direction)⟩ :
        Choice.Obj (Resumption Choice PEmpty)) :
      Sum PEmpty (Choice.Obj (Resumption Choice PEmpty))) = _
  rw [show M.dest (behavior seed) =
      ⟨seed, fun answer => behavior (xor seed answer)⟩ by
    unfold behavior
    rw [M.dest_corec_apply]]

end ITree.BridgeExamples
