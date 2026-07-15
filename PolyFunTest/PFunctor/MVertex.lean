/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.M.Vertex

/-!
# Regression tests for finite M-type vertices

These examples make path order and the backward direction of a lens
observable.  They also exercise roots, canonical splitting, concatenation,
and independent position/direction universes.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uA₃ uB₃

namespace PFunctor
namespace MVertexTest

/-- A binary signature whose node labels and directions are both bits. -/
abbrev binaryP : PFunctor := ⟨Bool, fun _ => Bool⟩

/-- The state records the most recently selected branch. -/
def binaryStep (history : List Bool) : binaryP (List Bool) :=
  ⟨history.head?.getD false, fun direction => direction :: history⟩

def binaryTreeAt (history : List Bool) : M binaryP :=
  M.corec binaryStep history

def binaryTree : M binaryP :=
  binaryTreeAt []

theorem head_binaryTreeAt (history : List Bool) :
    M.head (binaryTreeAt history) = history.head?.getD false :=
  congrArg Sigma.fst (M.dest_corec_apply binaryStep history)

theorem children_binaryTreeAt (history : List Bool) (direction : Bool) :
    M.children (binaryTreeAt history) direction =
      binaryTreeAt (direction :: history) := by
  have h := M.dest_corec_apply binaryStep history
  have hA := congrArg Sigma.fst h
  have hB := (Sigma.ext_iff.mp h).2
  cases hA
  exact congrFun (eq_of_heq hB) direction

/-- A path that first selects `true`, then `false`. -/
def depthTwo : M.Vertex binaryTree :=
  .child true (.child false (.root _))

example : M.Vertex.depth depthTwo = 2 :=
  rfl

/-- Subtree selection follows the directions in outer-to-inner order. -/
example : M.head (M.Vertex.subtree depthTwo) = false := by
  change M.head
    (M.children (M.children (binaryTreeAt []) true) false) = false
  rw [children_binaryTreeAt, children_binaryTreeAt, head_binaryTreeAt]
  rfl

/-- Splitting after one edge produces a one-edge prefix and residual. -/
example : M.Vertex.depth (M.Vertex.splitAt 1 depthTwo).1 = 1 := by
  rw [M.Vertex.depth_splitAt_fst]
  decide

example : M.Vertex.depth (M.Vertex.splitAt 1 depthTwo).2 = 1 := by
  rw [M.Vertex.depth_splitAt_snd]
  decide

/-- Recombination pins the orientation of prefix followed by residual. -/
example : M.Vertex.append (M.Vertex.splitAt 1 depthTwo).1
    (M.Vertex.splitAt 1 depthTwo).2 = depthTwo :=
  M.Vertex.append_splitAt 1 depthTwo

/-- A target signature with natural-number node labels. -/
abbrev natBinaryP : PFunctor := ⟨Nat, fun _ => Bool⟩

/-- Map node labels to `0`/`1` and reverse target branches on the way back. -/
def reverseBranchLens : Lens binaryP natBinaryP :=
  (fun label => if label then 1 else 0) ⇆ (fun _ branch => !branch)

def mappedFalse : M.Vertex (M.mapLens reverseBranchLens binaryTree) :=
  .child false (.root _)

/-- Pulling target branch `false` really selects source branch `true`. -/
example :
    match M.Vertex.pullMapLens reverseBranchLens binaryTree mappedFalse with
    | .root _ => False
    | .child direction _ => direction = true := by
  rw [M.Vertex.pullMapLens.eq_def]
  rfl

/-- The transported path preserves its length and selects a mapped copy of
the exact target subtree. -/
example : M.Vertex.depth
    (M.Vertex.pullMapLens reverseBranchLens binaryTree mappedFalse) = 1 := by
  rw [M.Vertex.depth_pullMapLens]
  rfl

example : M.mapLens reverseBranchLens
      (M.Vertex.subtree
        (M.Vertex.pullMapLens reverseBranchLens binaryTree mappedFalse)) =
    M.Vertex.subtree mappedFalse :=
  M.Vertex.subtree_pullMapLens reverseBranchLens binaryTree mappedFalse

/-- Root-only behavior remains stable for a nullary signature. -/
abbrev nullaryP : PFunctor := ⟨Unit, fun _ => Empty⟩

def nullaryTree : M nullaryP :=
  M.corec (fun _ : Unit => ⟨(), Empty.elim⟩) ()

example : M.Vertex.splitAt 7 (.root nullaryTree) =
    ⟨.root nullaryTree, .root nullaryTree⟩ := by
  rfl

/-- Tree mapping leaves all three polynomial universe pairs independent. -/
example (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB₂})
    (R : PFunctor.{uA₃, uB₃}) (f : Lens P Q) (g : Lens Q R)
    (tree : M P) :
    M.mapLens (g ∘ₗ f) tree = M.mapLens g (M.mapLens f tree) :=
  M.mapLens_comp g f tree

/-- Lens mapping fuses with an independently universe-polymorphic coalgebra. -/
example {α : Type uA₃} (P : PFunctor.{uA, uB})
    (Q : PFunctor.{uA₂, uB₂}) (l : Lens P Q) (step : α → P α)
    (seed : α) :
    M.mapLens l (M.corec step seed) =
      M.corec (fun state => Lens.mapObj l (step state)) seed :=
  M.mapLens_corec l step seed

/-- Vertex transport likewise does not couple source and target universes. -/
example (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB₂})
    (l : Lens P Q) (tree : M P) :
    M.Vertex (M.mapLens l tree) → M.Vertex tree :=
  M.Vertex.pullMapLens l tree

end MVertexTest
end PFunctor
