/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.Cartesian
import Mathlib.Data.Fintype.OfMap
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# In-order traversal as a polynomial lens

A binary tree has one entry at each node and leaf. The in-order lens sends its shape to the
number of entries and sends each flat index back to its tree position. A separate executable
walk fills one array, pushing each entry once. Its lookup theorem identifies the walk with the lens.
The convention follows Bruno Gavranović's
[TensorType traversal example](https://github.com/bgavran/TensorType/blob/7715491df8a38e121489187f0a2383523af69d47/examples/TensorManipulation.idr#L215-L232).
-/

public section

namespace Examples.TreeTensor

/-- The shape of a binary tree with a payload at every node and every leaf. -/
inductive Shape where
  | leaf
  | node (left right : Shape)
  deriving DecidableEq, Repr

/-- The locations at which an all-node tree carries an entry. -/
inductive Pos : Shape → Type where
  | atLeaf : Pos .leaf
  | left {l r : Shape} : Pos l → Pos (.node l r)
  | atNode {l r : Shape} : Pos (.node l r)
  | right {l r : Shape} : Pos r → Pos (.node l r)
  deriving DecidableEq, Repr

/-- Number of payloads visited in order. -/
@[expose] def size : Shape → Nat
  | .leaf => 1
  | .node l r => size l + (1 + size r)

/-- The polynomial of labelled binary trees. -/
abbrev treeP : PFunctor := ⟨Shape, Pos⟩

/-- The polynomial of flat vectors of arbitrary length. -/
abbrev flatP : PFunctor := ⟨Nat, Fin⟩

private def leafPositions : Fin 1 ≃ Pos .leaf where
  toFun _ := .atLeaf
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv p := by cases p; rfl

private def nodePositions (l r : Shape) : Pos l ⊕ (Fin 1 ⊕ Pos r) ≃ Pos (.node l r) where
  toFun
    | .inl p => .left p
    | .inr (.inl _) => .atNode
    | .inr (.inr p) => .right p
  invFun
    | .left p => .inl p
    | .atNode => .inr (.inl 0)
    | .right p => .inr (.inr p)
  left_inv
    | .inl _ => rfl
    | .inr (.inl k) => by
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      rfl
    | .inr (.inr _) => rfl
  right_inv p := by cases p <;> rfl

/-- Convert between an in-order index and a tree position in either direction. -/
def indexEquiv : (s : Shape) → Fin (size s) ≃ Pos s
  | .leaf => leafPositions
  | .node l r =>
    let rest := finSumFinEquiv.symm.trans ((Equiv.refl (Fin 1)).sumCongr (indexEquiv r))
    (finSumFinEquiv.symm.trans ((indexEquiv l).sumCongr rest)).trans (nodePositions l r)

/-- Enumerate positions constructively in traversal order. -/
instance instFintypePos (s : Shape) : Fintype (Pos s) :=
  Fintype.ofEquiv (Fin (size s)) (indexEquiv s)

/-- Flattening sends the shape to its size and pulls payloads from in-order positions. -/
@[expose] def inorder : PFunctor.Lens treeP flatP where
  toFunA := size
  toFunB := fun s => indexEquiv s

@[simp] theorem inorder_toFunA (s : Shape) : inorder.toFunA s = size s := rfl

@[simp] theorem inorder_toFunB (s : Shape) (i : Fin (size s)) :
    inorder.toFunB s i = indexEquiv s i := rfl

/-- Every direction has a unique flat index for the specified shape. -/
instance inorder_isCartesian : inorder.IsCartesian where
  bijective s := (indexEquiv s).bijective

private def pushEntries {α : Type*} : (s : Shape) → (Pos s → α) → Array α → Array α
  | .leaf, x, acc => acc.push (x .atLeaf)
  | .node l r, x, acc =>
    let left := pushEntries l (fun p => x (.left p)) acc
    pushEntries r (fun p => x (.right p)) (left.push (x .atNode))

private theorem size_pushEntries {α : Type*} (s : Shape) (x : Pos s → α) (acc : Array α) :
    (pushEntries s x acc).size = acc.size + size s := by
  induction s generalizing acc with
  | leaf => simp [pushEntries, size]
  | node l r ihl ihr => simp [pushEntries, size, ihl, ihr, Nat.add_assoc]

private theorem pushEntries_append {α : Type*} (s : Shape) (x : Pos s → α) (a b : Array α) :
    pushEntries s x (a ++ b) = a ++ pushEntries s x b := by
  induction s generalizing a b with
  | leaf => simp [pushEntries]
  | node l r ihl ihr => simp only [pushEntries, ihl, Array.push_append, ihr]

/-- Visit every leaf and node in order, pushing its payload into one preallocated array. -/
def flatten {α : Type*} (s : Shape) (x : Pos s → α) : Vector α (size s) :=
  ⟨pushEntries s x (.emptyWithCapacity (size s)), by simp [size_pushEntries]⟩

@[simp] theorem flatten_leaf {α : Type*} (x : Pos .leaf → α) :
    flatten .leaf x = #v[x .atLeaf] := by
  apply Vector.toArray_inj.mp
  simp [flatten, pushEntries]

/-- A node yields its left entries, its payload and its right entries, in that order. -/
theorem flatten_node {α : Type*} (l r : Shape) (x : Pos (.node l r) → α) :
    flatten (.node l r) x = flatten l (fun p => x (.left p)) ++
      (#v[x .atNode] ++ flatten r (fun p => x (.right p))) := by
  apply Vector.toArray_inj.mp
  simp only [flatten, pushEntries, Array.emptyWithCapacity_eq, Vector.toArray_append]
  simpa only [Array.append_empty, Array.append_singleton_assoc] using
    pushEntries_append r (fun p => x (.right p)) ((pushEntries l _ #[]).push (x .atNode)) #[]

private theorem append_get_left {α : Type*} {n m : Nat} (xs : Vector α n) (ys : Vector α m)
    (i : Fin n) : (xs.append ys).get (Fin.castAdd m i) = xs.get i :=
  Vector.getElem_append_left i.isLt

private theorem append_get_right {α : Type*} {n m : Nat} (xs : Vector α n) (ys : Vector α m)
    (i : Fin m) : (xs.append ys).get (Fin.natAdd n i) = ys.get i := by
  change (xs ++ ys)[n + i.val] = ys[i.val]
  rw [Vector.getElem_append_right (by omega) (by omega)]
  simp

private theorem flatten_get_position {α : Type*} {s : Shape} (p : Pos s) (x : Pos s → α) :
    (flatten s x).get ((indexEquiv s).symm p) = x p := by
  induction p with
  | atLeaf => rfl
  | left p ih =>
    rw [flatten_node]
    change Vector.get (Vector.append _ _) (Fin.castAdd _ ((indexEquiv _).symm p)) = _
    rw [append_get_left]
    exact ih _
  | atNode =>
    rw [flatten_node]
    change Vector.get (Vector.append _ (Vector.append _ _))
      (Fin.natAdd _ (Fin.castAdd _ (0 : Fin 1))) = _
    rw [append_get_right, append_get_left]
    rfl
  | right p ih =>
    rw [flatten_node]
    change Vector.get (Vector.append _ (Vector.append _ _))
      (Fin.natAdd _ (Fin.natAdd 1 ((indexEquiv _).symm p))) = _
    rw [append_get_right, append_get_right]
    exact ih _

/-- Every entry in the materialized vector agrees with the direction chosen by the lens. -/
theorem flatten_get {α : Type*} (s : Shape) (x : Pos s → α) (i : Fin (size s)) :
    (flatten s x).get i = x (indexEquiv s i) := by
  simpa using flatten_get_position (indexEquiv s i) x

/-- For a fixed shape the walker and lookup by the inverse index recover one another. -/
def flattenEquiv (s : Shape) (α : Type*) : (Pos s → α) ≃ Vector α (size s) where
  toFun := flatten s
  invFun y p := y.get ((indexEquiv s).symm p)
  left_inv x := funext fun p => flatten_get_position p x
  right_inv y := by
    ext i hi
    change (flatten s _).get ⟨i, hi⟩ = y.get ⟨i, hi⟩
    simpa using flatten_get s (fun p => y.get ((indexEquiv s).symm p)) ⟨i, hi⟩

@[simp] theorem flattenEquiv_apply {α : Type*} (s : Shape) (x : Pos s → α) :
    flattenEquiv s α x = flatten s x := by
  rfl

@[simp] theorem flattenEquiv_symm_apply {α : Type*} (s : Shape) (y : Vector α (size s)) :
    (flattenEquiv s α).symm y = fun p => y.get ((indexEquiv s).symm p) := by
  rfl

end Examples.TreeTensor
