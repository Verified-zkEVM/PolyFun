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

/-- A one-edge prefix in the mapped tree. -/
def mappedPrefix : M.Vertex (M.mapLens reverseBranchLens binaryTree) :=
  .child false (.root _)

/-- A one-edge suffix below `mappedPrefix`. -/
def mappedSuffix : M.Vertex (M.Vertex.subtree mappedPrefix) :=
  .child true (.root _)

/-- Pulling target branch `false` really selects source branch `true`. -/
example :
    match M.Vertex.pullMapLens reverseBranchLens binaryTree mappedPrefix with
    | .root _ => False
    | .child direction _ => direction = true := by
  unfold mappedPrefix
  rw [M.Vertex.pullMapLens_child]
  rfl

def pulledMappedPrefix : M.Vertex binaryTree :=
  M.Vertex.pullMapLens reverseBranchLens binaryTree mappedPrefix

def pulledMappedSuffix : M.Vertex (M.Vertex.subtree pulledMappedPrefix) :=
  M.Vertex.pullMapLens reverseBranchLens
    (M.Vertex.subtree pulledMappedPrefix)
    (M.Vertex.castEquiv
      (M.Vertex.subtree_pullMapLens
        reverseBranchLens binaryTree mappedPrefix).symm mappedSuffix)

/-- The concrete concatenation law keeps the reversed prefix before the
reversed suffix. -/
example :
    M.Vertex.pullMapLens reverseBranchLens binaryTree
        (M.Vertex.append mappedPrefix mappedSuffix) =
      M.Vertex.append pulledMappedPrefix pulledMappedSuffix :=
  M.Vertex.pullMapLens_append reverseBranchLens binaryTree
    mappedPrefix mappedSuffix

example :
    match pulledMappedPrefix with
    | .child direction _ => direction = true
    | _ => False := by
  unfold pulledMappedPrefix mappedPrefix
  rw [M.Vertex.pullMapLens_child]
  rfl

def mappedChildSuffix : M.Vertex
    (M.mapLens reverseBranchLens (M.children binaryTree true)) :=
  .child true (.root _)

example :
    match M.Vertex.pullMapLens reverseBranchLens
        (M.children binaryTree true) mappedChildSuffix with
    | .child direction _ => direction = false
    | _ => False := by
  unfold mappedChildSuffix
  rw [M.Vertex.pullMapLens_child]
  rfl

/-- The transported path preserves its length and selects a mapped copy of
the exact target subtree. -/
example : M.Vertex.depth
    (M.Vertex.pullMapLens reverseBranchLens binaryTree mappedPrefix) = 1 := by
  rw [M.Vertex.depth_pullMapLens]
  rfl

example : M.mapLens reverseBranchLens
      (M.Vertex.subtree
        (M.Vertex.pullMapLens reverseBranchLens binaryTree mappedPrefix)) =
    M.Vertex.subtree mappedPrefix :=
  M.Vertex.subtree_pullMapLens reverseBranchLens binaryTree mappedPrefix

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

/-- Pulling mapped vertices preserves prefix-then-suffix concatenation across
independent source and target polynomial universes. -/
example (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB₂})
    (l : Lens P Q) (tree : M P)
    (initial : M.Vertex (M.mapLens l tree))
    (suffix : M.Vertex (M.Vertex.subtree initial)) :
    M.Vertex.pullMapLens l tree (M.Vertex.append initial suffix) =
      M.Vertex.append (M.Vertex.pullMapLens l tree initial)
        (M.Vertex.pullMapLens l
          (M.Vertex.subtree (M.Vertex.pullMapLens l tree initial))
          (M.Vertex.castEquiv
            (M.Vertex.subtree_pullMapLens l tree initial).symm suffix)) :=
  M.Vertex.pullMapLens_append l tree initial suffix

/-- Transport preserves the explicit root/child structure of a finite
vertex, including the dependent child subtree. -/
example (P : PFunctor.{uA, uB}) {tree tree' : M P}
    (h : tree = tree') (direction : P.B (M.head tree))
    (next : M.Vertex (M.children tree direction)) :
    M.Vertex.castEquiv h (.child direction next) =
      .child (M.castDirection h direction)
        (M.Vertex.castEquiv
          (M.children_castDirection h direction) next) :=
  M.Vertex.cast_child h direction next

/-- Contravariant vertex transport is itself functorial across fully
independent polynomial universes. -/
example (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB₂})
    (R : PFunctor.{uA₃, uB₃}) (f : Lens P Q) (g : Lens Q R)
    (tree : M P) (vertex : M.Vertex (M.mapLens (g ∘ₗ f) tree)) :
    M.Vertex.pullMapLens (g ∘ₗ f) tree vertex =
      M.Vertex.pullMapLens f tree
        (M.Vertex.pullMapLens g (M.mapLens f tree)
          (M.Vertex.castEquiv (M.mapLens_comp g f tree) vertex)) :=
  M.Vertex.pullMapLens_comp g f tree vertex

example (P : PFunctor.{uA, uB}) (tree : M P)
    (vertex : M.Vertex (M.mapLens (Lens.id P) tree)) :
    M.Vertex.pullMapLens (Lens.id P) tree vertex =
      M.Vertex.castEquiv (M.mapLens_id tree) vertex :=
  M.Vertex.pullMapLens_id tree vertex

end MVertexTest
end PFunctor
