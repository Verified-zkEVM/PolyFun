/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Domain
public import PolyFun.PFunctor.Resumption.Truncate

/-!
# Finite truncations approximate continuous resumption semantics

Interpret cutoff leaves as bottom. The resulting folds form an increasing
chain whose supremum is the least continuous-algebra interpretation. Queries
need not be strict or finitely branching; a cutoff is never an error value.
-/

public section

open OmegaCompletePartialOrder

namespace PFunctor.Resumption

universe uA uB uα uD

variable {P : PFunctor.{uA, uB}} {α : Type uα} {D : Type uD}
  [OmegaCompletePartialOrder D] [OrderBot D]

/-- Fold a finite truncation, interpreting its cutoff leaves as bottom. -/
@[expose] def foldTruncate (ret : α → D) (alg : ContinuousAlgebra P D)
    (fuel : Nat) (tree : Resumption P α) : D :=
  FreeM.foldFreeM (fun result => result.elim ⊥ ret) (fun a => alg a) (truncate fuel tree)

theorem foldTruncate_zero (ret : α → D) (alg : ContinuousAlgebra P D)
    (tree : Resumption P α) : foldTruncate ret alg 0 tree = match dest tree with
      | .inl value => ret value
      | .inr _ => ⊥ := by
  unfold foldTruncate
  rw [truncate_zero]
  cases dest tree <;> rfl

theorem foldTruncate_succ (ret : α → D) (alg : ContinuousAlgebra P D)
    (fuel : Nat) (tree : Resumption P α) :
    foldTruncate ret alg (fuel + 1) tree = match dest tree with
      | .inl value => ret value
      | .inr ⟨a, next⟩ => alg a (fun b => foldTruncate ret alg fuel (next b)) := by
  unfold foldTruncate
  rw [truncate_succ]
  cases dest tree <;> rfl

/-- A finite fold never asserts more information than the unbounded meaning. -/
theorem foldTruncate_le_denote (ret : α → D) (alg : ContinuousAlgebra P D)
    (fuel : Nat) (tree : Resumption P α) :
    foldTruncate ret alg fuel tree ≤ denote ret alg tree := by
  induction fuel generalizing tree with
  | zero =>
      rw [foldTruncate_zero, denote_eq]
      cases dest tree <;> simp
  | succ n ih =>
      rw [foldTruncate_succ, denote_eq]
      rcases dest tree with value | ⟨a, next⟩
      · exact le_rfl
      · exact (alg a).monotone (fun b => ih (next b))

/-- Truncation at depth `n` contains at least the `n`-th fixed-point approximation. -/
theorem approximants_le_foldTruncate (ret : α → D) (alg : ContinuousAlgebra P D)
    (fuel : Nat) (tree : Resumption P α) :
    (domainStep ret alg).approximants fuel tree ≤ foldTruncate ret alg fuel tree := by
  induction fuel generalizing tree with
  | zero => exact bot_le
  | succ n ih =>
      rw [ContinuousHom.approximants_succ, foldTruncate_succ]
      simp only [domainStep, ContinuousHom.ofFun_apply]
      rcases dest tree with value | ⟨a, next⟩
      · exact le_rfl
      · exact (alg a).monotone (fun b => ih (next b))

/-- Increasing the cutoff budget increases the interpreted information. -/
theorem foldTruncate_le_succ (ret : α → D) (alg : ContinuousAlgebra P D)
    (fuel : Nat) (tree : Resumption P α) :
    foldTruncate ret alg fuel tree ≤ foldTruncate ret alg (fuel + 1) tree := by
  induction fuel generalizing tree with
  | zero =>
      rw [foldTruncate_zero, foldTruncate_succ]
      cases dest tree <;> simp
  | succ n ih =>
      rw [foldTruncate_succ, foldTruncate_succ]
      rcases dest tree with value | ⟨a, next⟩
      · exact le_rfl
      · exact (alg a).monotone (fun b => ih (next b))

/-- The increasing family of finite folds, simultaneously over all trees. -/
@[expose] def truncationChain (ret : α → D) (alg : ContinuousAlgebra P D) :
    Chain (Resumption P α → D) :=
  ⟨foldTruncate ret alg, monotone_nat_of_le_succ (fun n tree =>
    foldTruncate_le_succ ret alg n tree)⟩

/-- Finite polynomial folds approximate the entire coinductive interpretation. -/
theorem denote_eq_sup_truncations (ret : α → D) (alg : ContinuousAlgebra P D) :
    denote ret alg = ωSup (truncationChain ret alg) := by
  apply le_antisymm
  · apply ωSup_le
    intro n tree
    exact le_trans (approximants_le_foldTruncate ret alg n tree)
      (le_ωSup (truncationChain ret alg) n tree)
  · exact ωSup_le _ _ (fun n tree => foldTruncate_le_denote ret alg n tree)

end PFunctor.Resumption
