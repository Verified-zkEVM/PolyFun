/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Complexity.Computability.DecisionTree.Basic
public import Cslib.Foundations.Data.PFunctor.Free.Fold
public import PolyFun.PFunctor.Bound

/-!
# Query complexity over a polynomial interface

A free program over a polynomial `P` asks positions `a : P.A` and continues on the answer in
`P.B a`. Answering every query from a section `x : (a : P.A) → P.B a` evaluates it, through the
fold `PFunctor.FreeM.foldFreeM`. The *query complexity* of a function of the section is the least
worst-case number of queries of a program computing it, measured by
`PFunctor.FreeM.IsTotalRollBound`.

complexitylib's Boolean decision trees are the case `P = ⟨ι, fun _ => Bool⟩`:
`Cslib.DecisionTree.equivFreeM` identifies the two, matches evaluation with the fold and depth
with the total roll bound, and `Cslib.DecisionTree.complexity_eq_queryComplexity` identifies their
complexity measures.

## Main definitions

* `PFunctor.FreeM.Computes`: a free program computes a function of the answering section.
* `PFunctor.FreeM.queryComplexity`: the least worst-case query count of such a program.
* `PFunctor.FreeM.queryAll`: query a list of positions in turn and apply a function.
* `Cslib.DecisionTree.equivFreeM`: decision trees are free programs of the Boolean interface.

## Main results

* `PFunctor.FreeM.queryComplexity_le_card`: over finitely many answerable positions, querying
  each once computes every function.
* `Cslib.DecisionTree.depth_le_iff_isTotalRollBound`: depth is the total roll bound.
* `Cslib.DecisionTree.complexity_eq_queryComplexity`: decision tree complexity is query
  complexity over the Boolean interface.
-/

@[expose] public section

universe uA uB u v

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {β : Type v}

/-- A free program *computes* `f` when answering every query from the section `x` returns
`f x`. -/
def Computes (t : P.FreeM β) (f : ((a : P.A) → P.B a) → β) : Prop :=
  ∀ x, t.foldFreeM id (fun a k => k (x a)) = f x

/-- The query complexity of `f` over the interface `P`: the least worst-case number of queries of
a free program computing it. It is `0` when no program computes `f`. -/
noncomputable def queryComplexity (f : ((a : P.A) → P.B a) → β) : ℕ :=
  sInf {d | ∃ t : P.FreeM β, t.Computes f ∧ t.IsTotalRollBound d}

theorem queryComplexity_le {f : ((a : P.A) → P.B a) → β} {t : P.FreeM β} {d : ℕ}
    (ht : t.Computes f) (hd : t.IsTotalRollBound d) : queryComplexity f ≤ d :=
  Nat.sInf_le ⟨t, ht, hd⟩

section QueryAll

variable [DecidableEq P.A]

/-- Query the positions of `l` in turn, starting from the partial answers `acc`, and return `f`
of the answers reached. -/
def queryAll (f : ((a : P.A) → P.B a) → β) :
    List P.A → ((a : P.A) → P.B a) → P.FreeM β
  | [], acc => pure (f acc)
  | a :: l, acc => .liftBind a fun b => queryAll f l (Function.update acc a b)

theorem foldFreeM_queryAll (f : ((a : P.A) → P.B a) → β) (l : List P.A)
    (acc x : (a : P.A) → P.B a) :
    (queryAll f l acc).foldFreeM id (fun a k => k (x a)) =
      f fun a => if a ∈ l then x a else acc a := by
  induction l generalizing acc with
  | nil => simp [queryAll]
  | cons a l ih =>
    change (queryAll f l (Function.update acc a (x a))).foldFreeM id _ = _
    rw [ih]
    congr 1
    funext a'
    by_cases hl : a' ∈ l
    · simp [hl]
    · by_cases ha : a' = a
      · subst ha
        simp
      · simp [hl, ha]

theorem isTotalRollBound_queryAll (f : ((a : P.A) → P.B a) → β) (l : List P.A)
    (acc : (a : P.A) → P.B a) : (queryAll f l acc).IsTotalRollBound l.length := by
  induction l generalizing acc with
  | nil => exact isTotalRollBound_pure _ _
  | cons a l ih =>
    rw [queryAll, isTotalRollBound_liftBind_iff]
    exact ⟨Nat.succ_pos _, fun b => ih _⟩

end QueryAll

/-- Over finitely many positions, each with an answer, querying every position once computes any
function of the answers. -/
theorem queryComplexity_le_card [Fintype P.A] [∀ a, Nonempty (P.B a)]
    (f : ((a : P.A) → P.B a) → β) : queryComplexity f ≤ Fintype.card P.A := by
  classical
  let acc : (a : P.A) → P.B a := fun a => Classical.choice inferInstance
  refine queryComplexity_le (t := queryAll f Finset.univ.toList acc) (fun x => ?_) ?_
  · rw [foldFreeM_queryAll]
    simp
  · simpa using isTotalRollBound_queryAll f Finset.univ.toList acc

end PFunctor.FreeM

namespace Cslib.DecisionTree

open PFunctor

variable {ι : Type u} {β : Type v}

/-- The query interface of Boolean decision trees: a position for each variable, answered by a
bit. -/
abbrev queryPFunctor (ι : Type u) : PFunctor.{u, 0} := ⟨ι, fun _ => Bool⟩

/-- A decision tree as a free program: a leaf returns, a node queries its variable. -/
def toFreeM : DecisionTree ι β → (queryPFunctor ι).FreeM β
  | leaf b => .pure b
  | node i t₀ t₁ => .liftBind i fun b => cond b t₁.toFreeM t₀.toFreeM

/-- A free program over the Boolean query interface as a decision tree. -/
def ofFreeM : (queryPFunctor ι).FreeM β → DecisionTree ι β
  | .pure b => leaf b
  | .liftBind i k => node i (ofFreeM (k false)) (ofFreeM (k true))

@[simp] theorem toFreeM_leaf (b : β) : (leaf b : DecisionTree ι β).toFreeM = pure b := rfl

@[simp] theorem toFreeM_node (i : ι) (t₀ t₁ : DecisionTree ι β) :
    (node i t₀ t₁).toFreeM = .liftBind i fun b => cond b t₁.toFreeM t₀.toFreeM := rfl

/-- Decision trees are exactly the free programs of the Boolean query interface. -/
def equivFreeM : DecisionTree ι β ≃ (queryPFunctor ι).FreeM β where
  toFun := toFreeM
  invFun := ofFreeM
  left_inv t := by
    induction t with
    | leaf => rfl
    | node i t₀ t₁ ih₀ ih₁ =>
      change node i (ofFreeM t₀.toFreeM) (ofFreeM t₁.toFreeM) = _
      rw [ih₀, ih₁]
  right_inv p := by
    induction p with
    | pure => rfl
    | lift_bind i k ih =>
      change FreeM.liftBind i (fun b => cond b (ofFreeM (k true)).toFreeM
        (ofFreeM (k false)).toFreeM) = FreeM.liftBind i k
      congr 1
      funext b
      cases b
      · exact ih false
      · exact ih true

@[simp] theorem equivFreeM_apply (t : DecisionTree ι β) : equivFreeM t = t.toFreeM := rfl

@[simp] theorem equivFreeM_symm_apply (p : (queryPFunctor ι).FreeM β) :
    equivFreeM.symm p = ofFreeM p := rfl

/-- Evaluating a decision tree is folding its free program against the input. -/
theorem eval_eq_foldFreeM (t : DecisionTree ι β) (x : ι → Bool) :
    t.eval x = t.toFreeM.foldFreeM id fun i k => k (x i) := by
  induction t with
  | leaf => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    change cond (x i) (t₁.eval x) (t₀.eval x) =
      FreeM.foldFreeM id _ (cond (x i) t₁.toFreeM t₀.toFreeM)
    cases x i
    · exact ih₀
    · exact ih₁

theorem computes_iff_toFreeM {t : DecisionTree ι β} {f : (ι → Bool) → β} :
    t.Computes f ↔ t.toFreeM.Computes f := by
  simp only [DecisionTree.Computes, FreeM.Computes, eval_eq_foldFreeM]

/-- The depth of a decision tree is the total roll bound of its free program. -/
theorem depth_le_iff_isTotalRollBound (t : DecisionTree ι β) (n : ℕ) :
    t.depth ≤ n ↔ t.toFreeM.IsTotalRollBound n := by
  induction t generalizing n with
  | leaf => simp [FreeM.isTotalRollBound_pure]
  | node i t₀ t₁ ih₀ ih₁ =>
    rw [toFreeM_node, FreeM.isTotalRollBound_liftBind_iff, Bool.forall_bool]
    simp only [depth_node, Bool.cond_false, Bool.cond_true, ← ih₀, ← ih₁]
    omega

/-- Decision tree complexity is query complexity over the Boolean query interface. -/
theorem complexity_eq_queryComplexity (f : (ι → Bool) → β) :
    complexity f = FreeM.queryComplexity (P := queryPFunctor ι) f := by
  refine congrArg sInf (Set.ext fun d => ⟨?_, ?_⟩)
  · rintro ⟨t, ht, hd⟩
    exact ⟨t.toFreeM, computes_iff_toFreeM.mp ht, (depth_le_iff_isTotalRollBound t d).mp hd⟩
  · rintro ⟨p, hp, hd⟩
    refine ⟨ofFreeM p, computes_iff_toFreeM.mpr ?_, (depth_le_iff_isTotalRollBound _ d).mpr ?_⟩
    · rwa [← equivFreeM_symm_apply, ← equivFreeM_apply, Equiv.apply_symm_apply]
    · rwa [← equivFreeM_symm_apply, ← equivFreeM_apply, Equiv.apply_symm_apply]

end Cslib.DecisionTree
