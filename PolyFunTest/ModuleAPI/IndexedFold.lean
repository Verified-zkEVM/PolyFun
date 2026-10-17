/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Traversal

/-!
# Ordinary-import canaries for indexed folds, reindexing, and traversals

A two-sorted expression signature over `Bool` (`false` for numbers, `true` for
Booleans) has addition at the number sort and a zero test at the Boolean sort; leaves
carry values of their sort. Its trees fold into a sort-indexed carrier, a lens that swaps
the operands of addition reindexes them along the identity, and the traversal of that
reindexing agrees with it. Equations are checked through ordinary imports.
-/

@[expose] public section

namespace PolyFunTest.ModuleAPI.IndexedFold

open IPFunctor

/-- Addition at the number sort and a zero test at the Boolean sort. Every child has the
number sort. -/
def Sig : IPFunctor.Endo.{0, 0, 0} Bool where
  A _ := Unit
  B
    | false, _ => Bool
    | true, _ => Unit
  src _ _ _ := false

/-- The meaning of each sort. -/
def Den : Bool → Type
  | false => Nat
  | true => Bool

/-- Evaluate one constructor from the meanings of its children. -/
def eval : FoldAlgebra Sig Den
  | false, (), child =>
      let x : Nat := child false
      let y : Nat := child true
      (x + y : Nat)
  | true, (), child =>
      let x : Nat := child ()
      (x == 0 : Bool)

/-- Trees whose leaves are values of their sort. -/
abbrev Term := IFreeM Sig Den

/-- A numeric leaf. -/
def num (n : Nat) : Term false := .pure (s := false) (show Den false from n)

/-- Addition, with its left operand at response `false`. -/
def add (x y : Term false) : Term false :=
  .liftBind (P := Sig) (s := false) () fun b => match b with
    | false => x
    | true => y

/-- The zero test. -/
def isZero (x : Term false) : Term true := .liftBind (P := Sig) (s := true) () fun _ => x

/-- Evaluate a tree. -/
def run {s : Bool} (t : Term s) : Den s := t.fold (fun _ v => v) eval

example : run (add (num 2) (num 3)) = (5 : Nat) := rfl
example : run (isZero (add (num 0) (num 0))) = true := rfl

example (a : Unit) (next : (b : Bool) → Term false) :
    run (.liftBind (P := Sig) (s := false) a next) = eval false a fun b => run (next b) :=
  IFreeM.fold_liftBind (P := Sig) (fun _ v => v) eval (s := false) a next

/-- Folds are determined by their leaf and constructor equations. -/
example {s : Bool} (t : Term s) : run t = t.fold (fun _ v => v) eval :=
  IFreeM.fold_unique (fun _ v => v) eval (fun _ t => run t) (fun _ _ => rfl)
    (fun _ _ _ => rfl) t

/-- Swap the operands of addition. -/
def swap : Lens Sig Sig where
  toFunA _ a := a
  toFunB
    | false, _, b => !b
    | true, _, b => b
  src_eq _ _ _ := rfl

/-- Reindex a tree along the swap lens. -/
def swapped {s : Bool} (t : Term s) : Term s := t.reindex swap.toReindexing fun _ v => v

example : swapped (add (num 2) (num 3)) = add (num 3) (num 2) := by
  refine (IFreeM.reindex_toReindexing_liftBind swap _ (s := false) () _).trans ?_
  unfold add
  congr 1
  funext b
  cases b <;> rfl

/-- Swapping preserves the meaning of a concrete tree. -/
example : run (swapped (isZero (add (num 1) (num 0)))) = run (isZero (add (num 1) (num 0))) :=
  rfl

/-- Reindexing along two lenses is reindexing along their composite. -/
example {s : Bool} (t : Term s) :
    swapped (swapped t) = t.reindex (swap.comp swap).toReindexing fun _ v => v := by
  simp [swapped]

/-- The identity lens leaves every tree unchanged. -/
example {s : Bool} (t : Term s) : t.reindex (Lens.id Sig).toReindexing (fun _ v => v) = t := by
  simp

/-- Traversal along the reindexing at the translated judgment is the reindexing. -/
example {s : Bool} (t : Term s) :
    t.traverse swap.toReindexing.toTraversal (fun r v => .pure (r.down ▸ v)) ⟨rfl⟩ =
      swapped t :=
  IFreeM.traverse_toTraversal_rfl swap.toReindexing (fun _ v => v) t

example {s : Bool} (t : Term s) :
    t.traverse swap.toReindexing.toTraversal (fun r v => .pure (r.down ▸ v)) ⟨rfl⟩ =
      swapped t := by
  simp only [IFreeM.traverse_toTraversal]
  rfl

/-- The identity traversal at a reflexive judgment returns the tree. -/
example {s : Bool} (t : Term s) :
    t.traverse (Traversal.identity Sig) (fun r v => .pure (r.down ▸ v)) ⟨rfl⟩ = t := by
  simp

example : (Reindexing.id Sig).toTraversal = Traversal.identity Sig :=
  Reindexing.toTraversal_id Sig

/-- Interpreting after a traversal is a fold carrying the traversal state. -/
example {s : Bool} (t : Term s) :
    (t.traverse (Traversal.identity Sig) (fun r v => .pure (r.down ▸ v)) ⟨rfl⟩).fold
        (fun _ v => v) eval =
      t.fold (D := fun i => ∀ j, PLift (i = j) → Den j)
        (fun _ v _ r => (IFreeM.pure (P := Sig) (r.down ▸ v)).fold (fun _ v => v) eval)
        (fun _ a next _ r => eval _ ((Traversal.identity Sig).op r a)
          (fun b => next ((Traversal.identity Sig).arg r a b) _
            ((Traversal.identity Sig).next r a b))) s ⟨rfl⟩ :=
  IFreeM.fold_traverse _ _ _ _ _ t

end PolyFunTest.ModuleAPI.IndexedFold
