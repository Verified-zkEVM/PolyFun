/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Computability.DecisionTree.Parity

public import CslibFrontier.Computability.DecisionTree.Parity
public import PolyFun.PFunctor.Bound

/-!
# Decision trees as free programs

A Boolean decision tree over variables `ι` queries a variable at each node and branches on its
value. That is a free program over the monomial interface `monomial ι Bool`, which asks a position
`i : ι` and receives a bit. This file identifies the two (`Cslib.DecisionTree.equivFreeM`).

- Evaluating a tree on an input `x` folds its program, answering each query `i` by `x i`
  (`Cslib.DecisionTree.eval_toFreeM`).
- The depth of a tree is the total roll bound of its program
  (`Cslib.DecisionTree.depth_le_iff_isTotalRollBound`).

So the decision-tree theory of cslib-frontier applies to free programs over Boolean queries; the
lower bounds are in `PolyFunFrontier.PFunctor.Free.DecisionTree.LowerBound`.

## Main definitions

* `Cslib.DecisionTree.toFreeM`, `Cslib.DecisionTree.ofFreeM`: the two directions.
* `Cslib.DecisionTree.equivFreeM`: decision trees are the free programs of `monomial ι Bool`.

## Main results

* `Cslib.DecisionTree.eval_toFreeM`, `Cslib.DecisionTree.eval_ofFreeM`: evaluation is the fold
  that answers each query from the input.
* `Cslib.DecisionTree.depth_le_iff_isTotalRollBound`,
  `Cslib.DecisionTree.depth_ofFreeM_le_iff`: depth is the total roll bound.
-/

@[expose] public section

universe u v

namespace Cslib.DecisionTree

open PFunctor

variable {ι : Type u} {β : Type v}

/-- A decision tree as a free program: a leaf returns its output, and a node queries its variable
and continues with the branch for the answer. -/
def toFreeM : DecisionTree ι β → (monomial ι Bool).FreeM β
  | leaf b => .pure b
  | node i t₀ t₁ => .liftBind i fun b => cond b t₁.toFreeM t₀.toFreeM

/-- A free program over Boolean queries as a decision tree. -/
def ofFreeM : (monomial ι Bool).FreeM β → DecisionTree ι β
  | .pure b => leaf b
  | .liftBind i k => node i (ofFreeM (k false)) (ofFreeM (k true))

@[simp] theorem toFreeM_leaf (b : β) : (leaf b : DecisionTree ι β).toFreeM = pure b := rfl

@[simp] theorem toFreeM_node (i : ι) (t₀ t₁ : DecisionTree ι β) :
    (node i t₀ t₁).toFreeM =
      (FreeM.lift (P := monomial ι Bool) i).bind fun b => cond b t₁.toFreeM t₀.toFreeM :=
  rfl

@[simp] theorem ofFreeM_pure (b : β) : ofFreeM (pure b : (monomial ι Bool).FreeM β) = leaf b :=
  rfl

@[simp] theorem ofFreeM_lift_bind (i : ι)
    (k : (monomial ι Bool).B i → (monomial ι Bool).FreeM β) :
    ofFreeM ((FreeM.lift (P := monomial ι Bool) i).bind
        (α := no_index (monomial ι Bool).B i) k) =
      node i (ofFreeM (k false)) (ofFreeM (k true)) :=
  rfl

@[simp] theorem ofFreeM_toFreeM (t : DecisionTree ι β) : ofFreeM t.toFreeM = t := by
  induction t with
  | leaf => rfl
  | node i t₀ t₁ ih₀ ih₁ => exact congrArg₂ (node i) ih₀ ih₁

@[simp] theorem toFreeM_ofFreeM (p : (monomial ι Bool).FreeM β) : (ofFreeM p).toFreeM = p := by
  induction p using FreeM.induction with
  | pure => rfl
  | lift_bind i k ih =>
    rw [ofFreeM_lift_bind, toFreeM_node]
    congr 1
    funext b
    cases b
    · exact ih false
    · exact ih true

/-- Decision trees over `ι` are exactly the free programs of the Boolean query interface
`monomial ι Bool`. -/
def equivFreeM : DecisionTree ι β ≃ (monomial ι Bool).FreeM β where
  toFun := toFreeM
  invFun := ofFreeM
  left_inv := ofFreeM_toFreeM
  right_inv := toFreeM_ofFreeM

@[simp] theorem equivFreeM_apply (t : DecisionTree ι β) : equivFreeM t = t.toFreeM := rfl

@[simp] theorem equivFreeM_symm_apply (p : (monomial ι Bool).FreeM β) :
    equivFreeM.symm p = ofFreeM p :=
  rfl

/-- Evaluating a decision tree on `x` folds its free program, answering each query `i` by
`x i`. -/
theorem eval_toFreeM (t : DecisionTree ι β) (x : ι → Bool) :
    t.toFreeM.foldFreeM id (fun i k => k (x i)) = t.eval x := by
  induction t with
  | leaf => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    change FreeM.foldFreeM id _ (cond (x i) t₁.toFreeM t₀.toFreeM) = cond (x i) _ _
    cases x i
    · exact ih₀
    · exact ih₁

/-- A free program over Boolean queries, answered from `x`, returns what its decision tree
returns on `x`. -/
theorem eval_ofFreeM (p : (monomial ι Bool).FreeM β) (x : ι → Bool) :
    (ofFreeM p).eval x = p.foldFreeM id (fun i k => k (x i)) := by
  rw [← eval_toFreeM, toFreeM_ofFreeM]

/-- The depth of a decision tree is the total roll bound of its free program. -/
theorem depth_le_iff_isTotalRollBound (t : DecisionTree ι β) (n : ℕ) :
    t.depth ≤ n ↔ t.toFreeM.IsTotalRollBound n := by
  induction t generalizing n with
  | leaf => simp
  | node i t₀ t₁ ih₀ ih₁ =>
    rw [toFreeM_node, FreeM.isTotalRollBound_lift_bind_iff, Bool.forall_bool]
    simp only [depth_node, Bool.cond_false, Bool.cond_true, ← ih₀, ← ih₁]
    omega

/-- A free program over Boolean queries has total roll bound `n` exactly when its decision tree has
depth at most `n`. -/
theorem depth_ofFreeM_le_iff (p : (monomial ι Bool).FreeM β) (n : ℕ) :
    (ofFreeM p).depth ≤ n ↔ p.IsTotalRollBound n := by
  rw [depth_le_iff_isTotalRollBound, toFreeM_ofFreeM]

end Cslib.DecisionTree
