/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.Bisim.Equiv
public import PolyFun.ITree.WP.Basic

/-!
# Weakest preconditions are invariant under weak bisimulation

The total and partial readings of `PolyFun.ITree.WP.Basic` read a silent step as its continuation,
so they cannot tell trees apart by their silent steps. They are invariant under finite stripping
of silent steps (`ITree.TauSteps.wpTotal_eq`) and under weak bisimulation. The relational form
compares trees with different return types: `t ≈[RR] s` and postconditions related along `RR`
give `wp t post ≤ wp s post'` (`ITree.WeakBisimRel.wpTotal_le`, `ITree.WeakBisimRel.wpPartial_le`).

Silent divergence is respected: a tree weakly bisimilar to `ITree.diverge` is `ITree.diverge`
(`ITree.TauSteps.diverge_target_eq`), so it keeps its readings `⊥` and `⊤`.

## Main results

* `ITree.TauSteps.wpTotal_eq`, `ITree.TauSteps.wpPartial_eq`.
* `ITree.WeakBisimRel.wpTotal_le`, `ITree.WeakBisimRel.wpPartial_le`.
* `ITree.WeakBisim.wpTotal_eq`, `ITree.WeakBisim.wpPartial_eq`.
-/

@[expose] public section

universe uA uB uα uβ w

namespace ITree

open PFunctor

variable {F : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {l : Type w} [CompleteLattice l]
  {Φ : OpSpec F l}

theorem TauSteps.wpTotal_eq (hΦ : Φ.Monotone) {post : α → l} {t t' : ITree F α}
    (h : TauSteps t t') : wpTotal Φ t post = wpTotal Φ t' post := by
  induction h with
  | refl => rfl
  | step c ht _ ih => rw [eq_step_of_dest ht, wpTotal_step hΦ, ih]

theorem TauSteps.wpPartial_eq (hΦ : Φ.Monotone) {post : α → l} {t t' : ITree F α}
    (h : TauSteps t t') : wpPartial Φ t post = wpPartial Φ t' post := by
  induction h with
  | refl => rfl
  | step c ht _ ih => rw [eq_step_of_dest ht, wpPartial_step hΦ, ih]

section Rel

variable (hΦ : Φ.Monotone) {RR : α → β → Prop} {post : α → l} {post' : β → l}
  (hpost : ∀ a b, RR a b → post a ≤ post' b)
include hΦ hpost

/-- Total correctness transfers along a relational weak bisimulation whose related return values
have related postconditions. -/
theorem WeakBisimRel.wpTotal_le {t : ITree F α} {s : ITree F β} (h : t ≈[RR] s) :
    wpTotal Φ t post ≤ wpTotal Φ s post' := by
  refine (wpTotal_le_of_wpStepFun_le
    (X := fun t => ⨅ (s : ITree F β) (_ : t ≈[RR] s), wpTotal Φ s post') ?_ t).trans
    (iInf_le_of_le s (iInf_le _ h))
  intro t
  refine le_iInf₂ fun s h => ?_
  induction t using shape_cases with
  | step t =>
    rw [wpStepFun_step]
    exact iInf_le_of_le s (iInf_le _ (h.tauSteps_left (.step _ (shape'_step t) (.refl t))))
  | pure r =>
    rw [wpStepFun_pure]
    obtain ⟨t'', s'', ht'', hs'', hm⟩ := h.dest
    rw [TauSteps.rigid_of_pure r (shape'_pure r) ht''] at hm
    rw [TauSteps.wpTotal_eq hΦ hs'']
    cases hm with
    | pure r₁ r' hrr ht hs =>
      rw [shape'_pure] at ht
      cases ht
      rw [eq_pure_of_dest hs, wpTotal_pure hΦ]
      exact hpost _ _ hrr
    | query _ _ _ ht => rw [shape'_pure] at ht; cases ht
    | tau _ _ ht => rw [shape'_pure] at ht; cases ht
  | query a c =>
    rw [wpStepFun_query]
    obtain ⟨t'', s'', ht'', hs'', hm⟩ := h.dest
    rw [TauSteps.rigid_of_query a c (shape'_query a c) ht''] at hm
    rw [TauSteps.wpTotal_eq hΦ hs'']
    cases hm with
    | pure _ _ _ ht => rw [shape'_query] at ht; cases ht
    | query a₁ c₁ c₁' ht hs hc =>
      rw [shape'_query] at ht
      cases ht
      rw [eq_query_of_dest hs, wpTotal_query hΦ]
      exact hΦ a fun b => iInf_le_of_le (c₁' b) (iInf_le _ (hc b))
    | tau _ _ ht => rw [shape'_query] at ht; cases ht

/-- Partial correctness transfers along a relational weak bisimulation whose related return
values have related postconditions. -/
theorem WeakBisimRel.wpPartial_le {t : ITree F α} {s : ITree F β} (h : t ≈[RR] s) :
    wpPartial Φ t post ≤ wpPartial Φ s post' := by
  refine (le_iSup_of_le t (le_iSup (fun _ : t ≈[RR] s => wpPartial Φ t post) h)).trans
    (le_wpPartial_of_le_wpStepFun
      (X := fun s => ⨆ (t : ITree F α) (_ : t ≈[RR] s), wpPartial Φ t post) ?_ s)
  intro s
  refine iSup₂_le fun t h => ?_
  induction s using shape_cases with
  | step s =>
    rw [wpStepFun_step]
    exact le_iSup_of_le t (le_iSup (fun _ : t ≈[RR] s => wpPartial Φ t post)
      (h.step_absorb_right _ (shape'_step s)))
  | pure r' =>
    rw [wpStepFun_pure]
    obtain ⟨t'', s'', ht'', hs'', hm⟩ := h.dest
    rw [TauSteps.rigid_of_pure r' (shape'_pure r') hs''] at hm
    rw [TauSteps.wpPartial_eq hΦ ht'']
    cases hm with
    | pure r r₁ hrr ht hs =>
      rw [shape'_pure] at hs
      cases hs
      rw [eq_pure_of_dest ht, wpPartial_pure hΦ]
      exact hpost _ _ hrr
    | query _ _ _ _ hs => rw [shape'_pure] at hs; cases hs
    | tau _ _ _ hs => rw [shape'_pure] at hs; cases hs
  | query a c' =>
    rw [wpStepFun_query]
    obtain ⟨t'', s'', ht'', hs'', hm⟩ := h.dest
    rw [TauSteps.rigid_of_query a c' (shape'_query a c') hs''] at hm
    rw [TauSteps.wpPartial_eq hΦ ht'']
    cases hm with
    | pure _ _ _ _ hs => rw [shape'_query] at hs; cases hs
    | query a₁ c₁ c₁' ht hs hc =>
      rw [shape'_query] at hs
      cases hs
      rw [eq_query_of_dest ht, wpPartial_query hΦ]
      exact hΦ a fun b => le_iSup_of_le (c₁ b)
        (le_iSup (fun _ : c₁ b ≈[RR] c' b => wpPartial Φ (c₁ b) post) (hc b))
    | tau _ _ _ hs => rw [shape'_query] at hs; cases hs

end Rel

theorem WeakBisim.wpTotal_eq (hΦ : Φ.Monotone) {post : α → l} {t s : ITree F α}
    (h : WeakBisim t s) :
    wpTotal Φ t post = wpTotal Φ s post :=
  le_antisymm (WeakBisimRel.wpTotal_le hΦ (fun _ _ (hab : _ = _) => hab ▸ le_rfl) h)
    (WeakBisimRel.wpTotal_le hΦ (fun _ _ (hab : _ = _) => hab ▸ le_rfl) h.symm)

theorem WeakBisim.wpPartial_eq (hΦ : Φ.Monotone) {post : α → l} {t s : ITree F α}
    (h : WeakBisim t s) :
    wpPartial Φ t post = wpPartial Φ s post :=
  le_antisymm (WeakBisimRel.wpPartial_le hΦ (fun _ _ (hab : _ = _) => hab ▸ le_rfl) h)
    (WeakBisimRel.wpPartial_le hΦ (fun _ _ (hab : _ = _) => hab ▸ le_rfl) h.symm)

end ITree
