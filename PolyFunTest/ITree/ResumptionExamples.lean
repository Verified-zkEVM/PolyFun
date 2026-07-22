/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Resumption

/-!
# Tau-free interaction-tree examples

These examples exercise the exact-image theorem with infinite visible behavior,
dependent query branches, empty direction types, and tau counterexamples.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uβ

namespace ITree.ResumptionExamples

open PFunctor
open PFunctor.Resumption

/-- A query whose answer type depends on the selected operation. -/
def dependentSpec : PFunctor.{0, 0} where
  A := Bool
  B operation := if operation then Bool else Fin 3

def visibleStep (seed : Bool) : Nat ⊕ dependentSpec.Obj Bool :=
  Sum.inr ⟨true, fun answer => by
    change Bool at answer
    exact xor seed answer⟩

/-- An infinite visible-query loop, with no silent nodes. -/
def visibleLoop (seed : Bool) : Resumption dependentSpec Nat :=
  Resumption.corec visibleStep seed

example (seed : Bool) : ITree.TauFree (toITree (visibleLoop seed)) := by simp

example (value : Nat) : ITree.TauFree (ITree.pure (F := dependentSpec) value) := by simp

example (tree : ITree dependentSpec Nat) : ¬ ITree.TauFree (ITree.step tree) :=
  ITree.not_tauFree_step tree

/-- A tau below a visible query is rejected, not merely a root tau. -/
example : ¬ ITree.TauFree
    (ITree.query (F := dependentSpec) true fun _ =>
      ITree.step (ITree.pure (F := dependentSpec) 7)) := by
  intro h
  have hchild := (ITree.tauFree_query _ _).1 h false
  exact ITree.not_tauFree_step _ hchild

/-- Nullary visible queries are accepted vacuously. -/
def nullarySpec : PFunctor.{0, 0} where
  A := Unit
  B _ := PEmpty

example : ITree.TauFree
    (ITree.query (F := nullarySpec) () (fun direction =>
      (PEmpty.elim direction : ITree nullarySpec Nat))) := by
  rw [ITree.tauFree_query]
  exact fun direction => PEmpty.elim direction

def dependentBranch : Resumption dependentSpec Nat :=
  Resumption.query true fun answer => by
    change Bool at answer
    exact Resumption.pure (if answer then 7 else 11)

example :
    ofTauFreeITree ⟨toITree dependentBranch, toITree_tauFree dependentBranch⟩ =
      dependentBranch := by
  simp [ofTauFreeITree_toITree]

example (state : {tree : ITree dependentSpec Nat // ITree.TauFree tree}) :
    toITree (ofTauFreeITree state) = state.1 :=
  toITree_ofTauFreeITree state

example (left right : Resumption dependentSpec Nat)
    (h : toITree left = toITree right) : left = right :=
  toITree_injective h

/-- Lens orientation and all position/direction/result universes stay independent. -/
theorem lensCanary {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}
    {β : Type uβ} (lens : Lens p q) (computation : Resumption p β) :
    toITree (mapLens lens computation) = ITree.mapSpec lens (toITree computation) := by
  simp

example (computation : Resumption dependentSpec Nat)
    (k : Nat → Resumption dependentSpec Bool) :
    toITree (Resumption.bind computation k) =
      ITree.bind (toITree computation) (fun value => toITree (k value)) :=
  toITree_bind computation k

end ITree.ResumptionExamples
