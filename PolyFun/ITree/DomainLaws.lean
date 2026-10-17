/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Domain
public import PolyFun.PFunctor.Resumption.DomainLaws

/-!
# Continuous interpretations of embedded and sequenced interaction trees

The tau-free resumption embedding commutes with continuous interpretation.
Sequencing substitutes the meanings of continuation trees at return leaves.
-/

public section

open OmegaCompletePartialOrder
open PFunctor.Resumption (ContinuousAlgebra)

namespace ITree

universe uA uB uα uβ uD uE

variable {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
  {D : Type uD} {E : Type uE} [OmegaCompletePartialOrder D] [OrderBot D]
  [OmegaCompletePartialOrder E] [OrderBot E]

/-- The canonical resumption embedding commutes with continuous interpretation. -/
theorem denote_toITree (ret : α → D) (alg : ContinuousAlgebra P D)
    (tree : PFunctor.Resumption P α) :
    denote ret alg tree.toITree = PFunctor.Resumption.denote ret alg tree := by
  let pre : (ITree P α → D) →𝒄 (PFunctor.Resumption P α → D) :=
    .ofFun (fun f t => f t.toITree)
  have comm (f : ITree P α → D) :
      pre (domainStep ret alg f) = PFunctor.Resumption.domainStep ret alg (pre f) := by
    funext t
    simp only [pre, ContinuousHom.ofFun_apply, domainStep,
      PFunctor.Resumption.domainStep, PFunctor.Resumption.shape'_toITree]
    cases PFunctor.Resumption.dest t <;> rfl
  exact congrFun ((domainStep ret alg).fix_fusion
    (PFunctor.Resumption.domainStep ret alg) pre rfl comm) tree

/-- A strict continuous algebra morphism commutes with interpretation, including silent steps. -/
theorem denote_fusion (ret : α → D) (alg : ContinuousAlgebra P D)
    (target : ContinuousAlgebra P E) (f : D →𝒄 E) (hbot : f ⊥ = ⊥)
    (halg : ∀ a k, f (alg a k) = target a (fun b => f (k b))) (tree : ITree P α) :
    f (denote ret alg tree) = denote (fun a => f (ret a)) target tree := by
  rw [← denote_toResumptionWithTau, ← denote_toResumptionWithTau]
  apply PFunctor.Resumption.denote_fusion _ _ _ f hbot
  intro a k
  cases a with
  | inl a => exact halg a k
  | inr tick => rfl

/-- Leastness of continuous interpretation against a prefixed interpretation. -/
theorem denote_le (ret : α → D) (alg : ContinuousAlgebra P D)
    (meaning : ITree P α → D) (h : domainStep ret alg meaning ≤ meaning) :
    denote ret alg ≤ meaning :=
  (domainStep ret alg).fix_le h

/-- Substitution changes only the interpretation of return leaves. -/
theorem denote_bind (ret : β → D) (alg : ContinuousAlgebra P D)
    (tree : ITree P α) (next : α → ITree P β) :
    denote ret alg (bind tree next) = denote (fun a => denote ret alg (next a)) alg tree := by
  let rhs := denote (fun a => denote ret alg (next a)) alg
  have lower : rhs ≤ fun t => denote ret alg (bind t next) := by
    apply denote_le
    intro t
    rcases ht : shape' t with ⟨head, children⟩
    cases head with
    | pure a =>
      have he := eq_pure_of_dest ht
      subst t
      simp [domainStep, bind_pure_left]
    | step =>
      have he := eq_step_of_dest ht
      subst t
      simp [domainStep, bind_step]
    | query a =>
      have he := eq_query_of_dest ht
      subst t
      simp [domainStep, bind_query]
  have upper (n : ℕ) (t : ITree P α) :
      (domainStep ret alg).approximants n (bind t next) ≤ rhs t := by
    induction n generalizing t with
    | zero => exact bot_le
    | succ n ih =>
      rcases ht : shape' t with ⟨head, children⟩
      cases head with
      | pure a =>
        have he := eq_pure_of_dest ht
        rw [he, bind_pure_left]
        change _ ≤ denote (fun a => denote ret alg (next a)) alg (pure a)
        rw [denote_pure]
        exact (domainStep ret alg).approximants_le_fix (n + 1) (next a)
      | step =>
        have he := eq_step_of_dest ht
        rw [he, bind_step, ContinuousHom.approximants_succ]
        change (domainStep ret alg).approximants n (bind (children PUnit.unit) next) ≤ _
        simpa only [rhs, denote_step] using ih (children PUnit.unit)
      | query a =>
        have he := eq_query_of_dest ht
        rw [he, bind_query, ContinuousHom.approximants_succ]
        change alg a (fun b => (domainStep ret alg).approximants n (bind (children b) next)) ≤ _
        change _ ≤ denote (fun a => denote ret alg (next a)) alg (query a children)
        rw [denote_query]
        exact (alg a).monotone fun b => ih (children b)
  apply le_antisymm _ (lower tree)
  change (ωSup (domainStep ret alg).approximants) (bind tree next) ≤ rhs tree
  exact ωSup_le _ _ (fun n => upper n tree)

/-- Silent divergence has the least denotation, independently of the visible algebra. -/
@[simp] theorem denote_diverge (ret : α → D) (alg : ContinuousAlgebra P D) :
    denote ret alg (diverge : ITree P α) = ⊥ := by
  apply le_antisymm _ bot_le
  apply ωSup_le
  intro n
  have h : (domainStep ret alg).approximants n (diverge : ITree P α) = ⊥ := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [ContinuousHom.approximants_succ]
        simpa only [domainStep, ContinuousHom.ofFun_apply, shape'_diverge] using ih
  exact h.le

end ITree
