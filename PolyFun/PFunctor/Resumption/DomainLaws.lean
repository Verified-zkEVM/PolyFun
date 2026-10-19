/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Domain

/-!
# Fusion and substitution for continuous resumption interpretations

Strict continuous maps commuting with the operation algebra commute with
interpretation. Substitution changes the return interpretation and preserves
the query algebra, even for infinite trees and unbounded branching.
-/

public section

open OmegaCompletePartialOrder

namespace PFunctor.Resumption

universe uA uB uα uβ uD uE

variable {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}
  {D : Type uD} {E : Type uE} [OmegaCompletePartialOrder D] [OrderBot D]
  [OmegaCompletePartialOrder E] [OrderBot E]

/-- A strict continuous algebra morphism commutes with interpretation. -/
theorem denote_fusion (ret : α → D) (alg : ContinuousAlgebra P D)
    (target : ContinuousAlgebra P E) (f : D →𝒄 E) (hbot : f ⊥ = ⊥)
    (halg : ∀ a k, f (alg a k) = target a (fun b => f (k b))) (tree : Resumption P α) :
    f (denote ret alg tree) = denote (fun a => f (ret a)) target tree := by
  let post : (Resumption P α → D) →𝒄 (Resumption P α → E) :=
    .ofFun (fun meaning t => f (meaning t)) (by
      exact ωScottContinuous.of_apply₂ fun t => f.ωScottContinuous.comp
        (ωScottContinuous.apply t))
  have hstrict : post ⊥ = ⊥ := funext fun _ => hbot
  have comm (meaning : Resumption P α → D) :
      post (domainStep ret alg meaning) =
        domainStep (fun a => f (ret a)) target (post meaning) := by
    funext t
    change f (match dest t with
      | .inl a => ret a
      | .inr ⟨a, next⟩ => alg a (fun b => meaning (next b))) = _
    rcases ht : dest t with a | ⟨a, next⟩
    · simp [post, domainStep, ht]
    · simpa [post, domainStep, ht] using halg a (fun b => meaning (next b))
  exact congrFun ((domainStep ret alg).fix_fusion
    (domainStep (fun a => f (ret a)) target) post hstrict comm) tree

/-- Substitution is interpreted by assigning each source return its continuation's meaning. -/
theorem denote_bind (ret : β → D) (alg : ContinuousAlgebra P D)
    (tree : Resumption P α) (next : α → Resumption P β) :
    denote ret alg (bind tree next) = denote (fun a => denote ret alg (next a)) alg tree := by
  let rhs := denote (fun a => denote ret alg (next a)) alg
  have lower : rhs ≤ fun t => denote ret alg (bind t next) := by
    apply denote_le
    intro t
    rcases ht : dest t with a | ⟨a, children⟩
    · have he : t = pure a := eq_of_dest_eq (ht.trans (dest_pure a).symm)
      simp [he]
    · rw [denote_eq ret alg, dest_bind, ht]
  have upper (n : ℕ) (t : Resumption P α) :
      (domainStep ret alg).approximants n (bind t next) ≤ rhs t := by
    induction n generalizing t with
    | zero => exact bot_le
    | succ n ih =>
      rcases ht : dest t with a | ⟨a, children⟩
      · have he : t = pure a := eq_of_dest_eq (ht.trans (dest_pure a).symm)
        rw [he, pure_bind]
        change _ ≤ denote (fun a => denote ret alg (next a)) alg (pure a)
        rw [denote_pure]
        exact (domainStep ret alg).approximants_le_fix (n + 1) (next a)
      · rw [ContinuousHom.approximants_succ]
        change (match dest (bind t next) with
          | .inl b => ret b
          | .inr ⟨q, k⟩ => alg q (fun b => (domainStep ret alg).approximants n (k b))) ≤ _
        rw [dest_bind, ht]
        change alg a (fun b => (domainStep ret alg).approximants n (bind (children b) next)) ≤ _
        conv_rhs =>
          dsimp only [rhs]
          rw [denote_eq, ht]
        exact (alg a).monotone fun b => ih (children b)
  apply le_antisymm _ (lower tree)
  change (ωSup (domainStep ret alg).approximants) (bind tree next) ≤ rhs tree
  exact ωSup_le _ _ (fun n => upper n tree)

end PFunctor.Resumption
