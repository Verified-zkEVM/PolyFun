/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.ResumptionWithTau
public import PolyFun.PFunctor.Dynamical.DynComputation
public import PolyFun.PFunctor.Dynamical.Trajectory

/-!
# Interaction trees as machines

An interaction tree is itself a machine, in two ways.

* `ITree.toDynSystem` reads the tree as a dynamical system over its raw polynomial
  `ITree.Poly F α`. The state is the tree, the exposed position is its head node, and an answer
  selects the child. Its behavior is the raw M-type tree (`ITree.behavior_toDynSystem`).
* `ITree.toDynComputation` reads the tree as a returning computation over `F + y`, the
  resumption-with-tau encoding of `PolyFun.ITree.ResumptionWithTau`. Silent steps become
  visible unit queries, so the bounded, chunked and `IO` runners of `DynComputation` apply to
  interaction trees, and a silent step can be counted like any other query. Its denotation is
  `ITree.toResumptionWithTau` (`ITree.denote_toDynComputation`).
-/

@[expose] public section

universe uA uB uα

namespace ITree

open PFunctor

variable {F : PFunctor.{uA, uB}} {α : Type uα}

/-- An interaction tree as a dynamical system over its raw polynomial: expose the head node of the
M-type representation and update to the selected child. -/
def toDynSystem : DynSystem (ITree F α) (ITree.Poly F α) where
  toFunA t := (M.dest t.toM).1
  toFunB t d := ⟨(M.dest t.toM).2 d⟩

/-- The behavior of `toDynSystem` is the raw M-type representation. -/
theorem behavior_toDynSystem :
    (toDynSystem (F := F) (α := α)).behavior = ITree.toM := by
  symm
  apply DynSystem.behavior_unique
  intro t
  rfl

/-- An interaction tree as a returning computation over `F + y`: silent steps become visible unit
queries. -/
noncomputable def toDynComputation :
    DynSystem.DynComputation (F + PFunctor.y.{uA, uB}) (ITree F α) α :=
  DynSystem.DynComputation.ofResumption toResumptionWithTau

/-- The denotation of `toDynComputation` is the resumption-with-tau encoding. -/
@[simp] theorem denote_toDynComputation (t : ITree F α) :
    (toDynComputation (F := F)).denote t = toResumptionWithTau t :=
  DynSystem.DynComputation.denote_ofResumption _ _

end ITree
