/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.Sim.Facts
public import PolyFun.ITree.WP.Basic

/-!
# Weakest preconditions of interaction-tree programs

The total and partial readings of `PolyFun.ITree.WP.Basic` under the constructions that build
programs: sequencing, mapping, iteration, relabelling events along a lens, and simulating events
by a handler.

Both readings distribute over `bind` exactly (`ITree.wpTotal_bind'`, `ITree.wpPartial_bind'`), and
so does every reading defined from them. Loops have three rules:
* a partial-correctness invariant rule (`ITree.le_wpPartial_iter`), which needs no termination;
* a total-correctness upper bound (`ITree.wpTotal_iter_le`);
* a total-correctness variant rule (`ITree.le_wpTotal_iter`), by well-founded induction.

Simulating events by a handler is sound for the readings. Reading each operation as the
correctness of its handler bounds the correctness of the simulation
(`ITree.wpTotal_le_wpTotal_simulate`, `ITree.wpPartial_simulate_le_wpPartial`).

## Main results

* `ITree.wpTotal_bind'`, `ITree.wpPartial_bind'`, and their monadic forms.
* `ITree.wpTotal_iter`, `ITree.wpPartial_iter`: one unfolding of a loop.
* `ITree.le_wpPartial_iter`, `ITree.wpTotal_iter_le`, `ITree.le_wpTotal_iter`: loop rules.
* `ITree.wpTotal_mapSpec`, `ITree.wpPartial_mapSpec`: relabelling along a lens.
* `ITree.wpTotal_le_wpTotal_simulate`, `ITree.wpPartial_simulate_le_wpPartial`: handler soundness.
-/

@[expose] public section

universe uA uB uEA uEB uα uβ w

namespace ITree

open PFunctor

variable {F : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {l : Type w} [CompleteLattice l]
  {Φ : OpSpec F l}

/-! ## Sequencing -/

section Bind

variable (hΦ : Φ.Monotone) (k : α → ITree F β) (post : β → l)
include hΦ

/-- Total correctness of a sequence is total correctness of its first part, for the total
correctness of the continuation. -/
theorem wpTotal_bind' (t : ITree F α) :
    wpTotal Φ (bind t k) post = wpTotal Φ t fun a => wpTotal Φ (k a) post := by
  apply le_antisymm
  · refine (wpTotal_le_of_wpStepFun_le (X := fun u => wpTotal Φ u post ⊓
      ⨅ (t₀ : ITree F α) (_ : bind t₀ k = u), wpTotal Φ t₀ fun a => wpTotal Φ (k a) post) ?_
      (bind t k)).trans ?_
    · intro u
      refine le_inf ((wpLayer_mono hΦ post (fun _ => inf_le_left) _).trans
        ((wpStepFun_wpTotal hΦ).le u)) (le_iInf₂ fun t₀ ht₀ => ?_)
      subst ht₀
      induction t₀ using shape_cases with
      | pure r =>
        rw [bind_pure_left, wpTotal_pure hΦ]
        exact (wpLayer_mono hΦ post (fun _ => inf_le_left) _).trans
          ((wpStepFun_wpTotal hΦ).le (k r))
      | step t' =>
        rw [bind_step, wpStepFun_step, wpTotal_step hΦ]
        exact inf_le_right.trans (iInf_le_of_le t' (iInf_le _ rfl))
      | query a c =>
        rw [bind_query, wpStepFun_query, wpTotal_query hΦ]
        exact hΦ a fun b => inf_le_right.trans (iInf_le_of_le (c b) (iInf_le _ rfl))
    · exact inf_le_right.trans (iInf_le_of_le t (iInf_le _ rfl))
  · refine wpTotal_le_of_wpStepFun_le (X := fun t₀ => wpTotal Φ (bind t₀ k) post) ?_ t
    intro t₀
    induction t₀ using shape_cases with
    | pure r => simp only [wpStepFun_pure, bind_pure_left, le_refl]
    | step t' => simp only [wpStepFun_step, bind_step, wpTotal_step hΦ, le_refl]
    | query a c => simp only [wpStepFun_query, bind_query, wpTotal_query hΦ, le_refl]

/-- Partial correctness of a sequence is partial correctness of its first part, for the partial
correctness of the continuation. -/
theorem wpPartial_bind' (t : ITree F α) :
    wpPartial Φ (bind t k) post = wpPartial Φ t fun a => wpPartial Φ (k a) post := by
  apply le_antisymm
  · refine le_wpPartial_of_le_wpStepFun (X := fun t₀ => wpPartial Φ (bind t₀ k) post) ?_ t
    intro t₀
    induction t₀ using shape_cases with
    | pure r => simp only [wpStepFun_pure, bind_pure_left, le_refl]
    | step t' => simp only [wpStepFun_step, bind_step, wpPartial_step hΦ, le_refl]
    | query a c => simp only [wpStepFun_query, bind_query, wpPartial_query hΦ, le_refl]
  · refine le_trans ?_ (le_wpPartial_of_le_wpStepFun (X := fun u => wpPartial Φ u post ⊔
      ⨆ (t₀ : ITree F α) (_ : bind t₀ k = u), wpPartial Φ t₀ fun a => wpPartial Φ (k a) post) ?_
      (bind t k))
    · exact le_sup_of_le_right (le_iSup_of_le t (le_iSup (fun _ : bind t k = bind t k => _) rfl))
    · intro u
      refine sup_le (((wpStepFun_wpPartial hΦ).ge u).trans
        (wpLayer_mono hΦ post (fun _ => le_sup_left) _)) (iSup₂_le fun t₀ ht₀ => ?_)
      subst ht₀
      induction t₀ using shape_cases with
      | pure r =>
        rw [bind_pure_left, wpPartial_pure hΦ]
        exact ((wpStepFun_wpPartial hΦ).ge (k r)).trans
          (wpLayer_mono hΦ post (fun _ => le_sup_left) _)
      | step t' =>
        rw [bind_step, wpStepFun_step, wpPartial_step hΦ]
        exact le_sup_of_le_right
          (le_iSup_of_le t' (le_iSup (fun _ : bind t' k = bind t' k => _) rfl))
      | query a c =>
        rw [bind_query, wpStepFun_query, wpPartial_query hΦ]
        exact hΦ a fun b => le_sup_of_le_right
          (le_iSup_of_le (c b) (le_iSup (fun _ : bind (c b) k = bind (c b) k => _) rfl))

end Bind

section Monadic

variable (hΦ : Φ.Monotone)
include hΦ

theorem wpTotal_bind {γ : Type uα} (t : ITree F α) (k : α → ITree F γ) (post : γ → l) :
    wpTotal Φ (t >>= k) post = wpTotal Φ t fun a => wpTotal Φ (k a) post :=
  wpTotal_bind' hΦ k post t

theorem wpPartial_bind {γ : Type uα} (t : ITree F α) (k : α → ITree F γ) (post : γ → l) :
    wpPartial Φ (t >>= k) post = wpPartial Φ t fun a => wpPartial Φ (k a) post :=
  wpPartial_bind' hΦ k post t

theorem wpTotal_map (f : α → β) (t : ITree F α) (post : β → l) :
    wpTotal Φ (map f t) post = wpTotal Φ t (post ∘ f) := by
  rw [map, wpTotal_bind' hΦ]
  congr 1
  funext a
  exact wpTotal_pure hΦ (f a)

theorem wpPartial_map (f : α → β) (t : ITree F α) (post : β → l) :
    wpPartial Φ (map f t) post = wpPartial Φ t (post ∘ f) := by
  rw [map, wpPartial_bind' hΦ]
  congr 1
  funext a
  exact wpPartial_pure hΦ (f a)

end Monadic

/-! ## Iteration -/

section IterStep

variable (body : β → ITree F (β ⊕ α))

private theorem iterStep_pure_inl (j : β) :
    iterStep body (pure (Sum.inl j)) = .mk .step (fun _ => body j) := by
  simp only [iterStep, shape'_pure]

private theorem iterStep_pure_inr (r : α) :
    iterStep body (pure (Sum.inr r)) = .mk (.pure r) PEmpty.elim := by
  simp only [iterStep, shape'_pure]

private theorem iterStep_step (t : ITree F (β ⊕ α)) :
    iterStep body (step t) = .mk .step (fun _ => t) := by
  simp only [iterStep, shape'_step]

private theorem iterStep_query (a : F.A) (c : F.B a → ITree F (β ⊕ α)) :
    iterStep body (query a c) = .mk (.query a) c := by
  simp only [iterStep, shape'_query]

end IterStep

section Iter

variable (hΦ : Φ.Monotone) (body : β → ITree F (β ⊕ α)) (post : α → l)
include hΦ

/-- One unfolding of a loop's total reading. -/
theorem wpTotal_iter (j : β) :
    wpTotal Φ (iter body j) post =
      wpTotal Φ (body j) (Sum.elim (fun j' => wpTotal Φ (iter body j') post) post) := by
  rw [iter_unfold, wpTotal_bind' hΦ]
  congr 1
  funext rj
  rcases rj with j' | r
  · exact wpTotal_step hΦ _
  · exact wpTotal_pure hΦ r

/-- One unfolding of a loop's partial reading. -/
theorem wpPartial_iter (j : β) :
    wpPartial Φ (iter body j) post =
      wpPartial Φ (body j) (Sum.elim (fun j' => wpPartial Φ (iter body j') post) post) := by
  rw [iter_unfold, wpPartial_bind' hΦ]
  congr 1
  funext rj
  rcases rj with j' | r
  · exact wpPartial_step hΦ _
  · exact wpPartial_pure hΦ r

/-- Partial correctness of a loop from an invariant: if `I j` guarantees that the body
re-establishes `I` when it continues and `post` when it stops, then `I j` guarantees `post` for the
loop. No termination is needed. -/
theorem le_wpPartial_iter {I : β → l} (hI : ∀ j, I j ≤ wpPartial Φ (body j) (Sum.elim I post))
    (j : β) : I j ≤ wpPartial Φ (iter body j) post := by
  refine (hI j).trans (le_wpPartial_corec (iterStep body) hΦ
    (Y := fun u => wpPartial Φ u (Sum.elim I post)) (fun u => ?_) (body j))
  induction u using shape_cases with
  | pure r =>
    rcases r with j' | r
    · rw [iterStep_pure_inl body, wpPartial_pure hΦ]
      exact hI j'
    · rw [iterStep_pure_inr body, wpPartial_pure hΦ]
      exact le_rfl
  | step t =>
    rw [iterStep_step body, wpPartial_step hΦ]
    exact le_rfl
  | query a c =>
    rw [iterStep_query body, wpPartial_query hΦ]
    exact le_rfl

/-- An upper bound on a loop's total reading from a bound the body preserves. No well-foundedness
is needed: a bound is an upper estimate, and divergence reads `⊥`. -/
theorem wpTotal_iter_le {B : β → l} (hB : ∀ j, wpTotal Φ (body j) (Sum.elim B post) ≤ B j)
    (j : β) : wpTotal Φ (iter body j) post ≤ B j := by
  refine (wpTotal_corec_le (iterStep body) hΦ (Y := fun u => wpTotal Φ u (Sum.elim B post))
    (fun u => ?_) (body j)).trans (hB j)
  induction u using shape_cases with
  | pure r =>
    rcases r with j' | r
    · rw [iterStep_pure_inl body, wpTotal_pure hΦ]
      exact hB j'
    · rw [iterStep_pure_inr body, wpTotal_pure hΦ]
      exact le_rfl
  | step t =>
    rw [iterStep_step body, wpTotal_step hΦ]
    exact le_rfl
  | query a c =>
    rw [iterStep_query body, wpTotal_query hΦ]
    exact le_rfl

/-- Total correctness of a loop from a variant. Suppose `I j` guarantees that the body either stops
with `post` or continues at some `j'` below `j`, in a well-founded relation, with `I j'`. Then
`I j` guarantees that the loop stops with `post`. -/
theorem le_wpTotal_iter {r : β → β → Prop} (hr : WellFounded r) {I : β → l}
    (hI : ∀ j, I j ≤ wpTotal Φ (body j) (Sum.elim (fun j' => ⨆ _ : r j' j, I j') post))
    (j : β) : I j ≤ wpTotal Φ (iter body j) post := by
  refine hr.induction (C := fun j => I j ≤ wpTotal Φ (iter body j) post) j fun j ih => ?_
  rw [wpTotal_iter hΦ]
  refine (hI j).trans (wpTotal_mono hΦ (fun rj => ?_) _)
  rcases rj with j' | a
  · exact iSup_le (ih j')
  · exact le_rfl

end Iter

/-! ## Relabelling and simulating events -/

section Events

variable {E : PFunctor.{uEA, uEB}}

/-- Relabelling events along a lens reads the spec through the lens: an `E`-operation is specified
by the `F`-spec of its image. -/
theorem wpTotal_mapSpec (hΦ : Φ.Monotone) (φ : Lens E F) (t : ITree E α) (post : α → l) :
    wpTotal Φ (mapSpec φ t) post =
      wpTotal (fun a k => Φ (φ.toFunA a) (k ∘ φ.toFunB a)) t post := by
  have hΨ : OpSpec.Monotone (fun a k => Φ (φ.toFunA a) (k ∘ φ.toFunB a) : OpSpec E l) :=
    fun a _ _ h => hΦ _ fun b => h _
  apply le_antisymm
  · refine wpTotal_corec_le (mapSpecStep φ) hΦ
      (Y := fun u => wpTotal (fun a k => Φ (φ.toFunA a) (k ∘ φ.toFunB a)) u post)
      (fun u => ?_) t
    induction u using shape_cases with
    | pure r =>
      rw [mapSpecStep_pure, wpTotal_pure hΨ]
      exact le_rfl
    | step u =>
      rw [mapSpecStep_step, wpTotal_step hΨ]
      exact le_rfl
    | query a c =>
      rw [mapSpecStep_query, wpTotal_query hΨ]
      exact le_rfl
  · refine wpTotal_le_of_wpStepFun_le (X := fun u => wpTotal Φ (mapSpec φ u) post)
      (le_of_eq (wpStepFun_eq_self _ _ (fun r => ?_) (fun u => ?_) (fun a c => ?_))) t
    · rw [mapSpec_pure, wpTotal_pure hΦ]
    · rw [mapSpec_step, wpTotal_step hΦ]
    · rw [mapSpec_query, wpTotal_query hΦ]
      rfl

/-- Relabelling events along a lens reads the spec through the lens, for partial correctness. -/
theorem wpPartial_mapSpec (hΦ : Φ.Monotone) (φ : Lens E F) (t : ITree E α) (post : α → l) :
    wpPartial Φ (mapSpec φ t) post =
      wpPartial (fun a k => Φ (φ.toFunA a) (k ∘ φ.toFunB a)) t post := by
  have hΨ : OpSpec.Monotone (fun a k => Φ (φ.toFunA a) (k ∘ φ.toFunB a) : OpSpec E l) :=
    fun a _ _ h => hΦ _ fun b => h _
  apply le_antisymm
  · refine le_wpPartial_of_le_wpStepFun (X := fun u => wpPartial Φ (mapSpec φ u) post)
      (le_of_eq (wpStepFun_eq_self _ _ (fun r => ?_) (fun u => ?_) (fun a c => ?_)).symm) t
    · rw [mapSpec_pure, wpPartial_pure hΦ]
    · rw [mapSpec_step, wpPartial_step hΦ]
    · rw [mapSpec_query, wpPartial_query hΦ]
      rfl
  · refine le_wpPartial_corec (mapSpecStep φ) hΦ
      (Y := fun u => wpPartial (fun a k => Φ (φ.toFunA a) (k ∘ φ.toFunB a)) u post)
      (fun u => ?_) t
    induction u using shape_cases with
    | pure r =>
      rw [mapSpecStep_pure, wpPartial_pure hΨ]
      exact le_rfl
    | step u =>
      rw [mapSpecStep_step, wpPartial_step hΨ]
      exact le_rfl
    | query a c =>
      rw [mapSpecStep_query, wpPartial_query hΨ]
      exact le_rfl

/-- Soundness of simulation for total correctness: reading each `E`-operation as the total
correctness of its handler bounds the total correctness of the simulated tree from below. -/
theorem wpTotal_le_wpTotal_simulate (hΦ : Φ.Monotone) (h : Handler E F) (t : ITree E α)
    (post : α → l) :
    wpTotal (fun a k => wpTotal Φ (h a) k) t post ≤ wpTotal Φ (simulate h t) post :=
  wpTotal_le_of_wpStepFun_le (X := fun u => wpTotal Φ (simulate h u) post)
    (le_of_eq (wpStepFun_eq_self _ _
      (fun r => by rw [simulate_pure, wpTotal_pure hΦ])
      (fun u => by rw [simulate_step_eq, wpTotal_step hΦ])
      (fun a c => by
        rw [simulate_query_eq_bind, wpTotal_bind' hΦ]
        simp only [wpTotal_step hΦ]))) t

/-- Soundness of simulation for partial correctness: reading each `E`-operation as the partial
correctness of its handler bounds the partial correctness of the simulated tree from above. -/
theorem wpPartial_simulate_le_wpPartial (hΦ : Φ.Monotone) (h : Handler E F) (t : ITree E α)
    (post : α → l) :
    wpPartial Φ (simulate h t) post ≤ wpPartial (fun a k => wpPartial Φ (h a) k) t post :=
  le_wpPartial_of_le_wpStepFun (X := fun u => wpPartial Φ (simulate h u) post)
    (le_of_eq (wpStepFun_eq_self _ _
      (fun r => by rw [simulate_pure, wpPartial_pure hΦ])
      (fun u => by rw [simulate_step_eq, wpPartial_step hΦ])
      (fun a c => by
        rw [simulate_query_eq_bind, wpPartial_bind' hΦ]
        simp only [wpPartial_step hΦ])).symm) t

end Events

end ITree
