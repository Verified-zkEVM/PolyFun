/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import PolyFun.PFunctor.Handler.Stateful.Combinators
public import Std.WP

/-!
# Frame rules for sums of stateful handlers

A program over the left interface of `Handler.Stateful.sum f g` changes only the first
component of its product state. A Hoare triple for the program under `f` therefore extends
to a triple under the sum with any predicate on the second component conjoined to both
assertions. The symmetric rule frames predicates on the first component.

`wp_run_frame_of_apply_map_eq` transports predicates along any family of state maps that
commutes with each request. The sum triples need only the lower laws of `Std.WP.WPMonad`.

The core `Std.WP.WP.Frames` laws use `frameFst` and `frameSnd`. These operators first
existentially hide the old spectator component of an assertion, then impose the frame on
the current spectator. On assertions independent of that component they are ordinary
conjunction with the frame. This gives an operator on full-state assertions, as required
by core's frame machinery, without requiring an exact or conjunctive WP interpretation.
These operators have no identity on arbitrary full-state assertions. Their frame closures
need not equal the original weakest precondition.
-/

public section

universe u v w uA uA' uT

namespace PFunctor.Handler.Stateful

open Std.WP Lean.Order

variable {m : Type u → Type v} {EPred : Type w} [Monad m] [Assertion EPred]
  [WPMonad m Prop EPred] {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}} {α : Type u}

/-- Transport a weakest precondition along state maps commuting with every request.
The relation `sep` describes the image of a source assertion together with a frame. -/
theorem wp_run_frame_of_apply_map_eq {S S' : Type u} {T : Type uT}
    (h : Stateful m S P) (h' : Stateful m S' P) (emb : T → S → S')
    (hemb : ∀ t a s, Prod.map _root_.id (emb t) <$> (h a).run s = (h' a).run (emb t s))
    (sep : (S → Prop) → (T → Prop) → S' → Prop)
    (hsep_elim : ∀ A F s', sep A F s' → ∃ s t, s' = emb t s ∧ A s ∧ F t)
    (hsep_intro : ∀ A F s t, A s → F t → sep A F (emb t s))
    (x : FreeM P α) (post : α → S → Prop) (epost : EPred) (F : T → Prop) :
    sep (wp (x.liftM h) post epost) F ⊑
      wp (x.liftM h') (fun a => sep (post a) F) epost := by
  intro s' hs'
  obtain ⟨s, t, rfl, hA, hF⟩ := hsep_elim _ _ _ hs'
  change wp (h.run x s) (fun r => post r.1 r.2) epost at hA
  change wp (h'.run x (emb t s)) (fun r => sep (post r.1) F r.2) epost
  rw [← run_map_eq_of_apply_map_eq h h' (emb t) (hemb t) x s]
  have hc : wp (h.run x s) (fun r => sep (post r.1) F (emb t r.2)) epost :=
    (show _ → _ from WP.wp_consequence (h.run x s) _ _ epost
      (fun r hr => hsep_intro _ _ _ _ hr hF)) hA
  exact (show _ → _ from WPMonad.map_le_wp_map (Prod.map _root_.id (emb t))
    (h.run x s) (fun r => sep (post r.1) F r.2) epost) hc

variable {S T : Type u}

/-- A left-component triple extends with any predicate on the unchanged right component. -/
theorem triple_sum_inl_frame (f : Stateful m S P) (g : Stateful m T Q) {x : FreeM P α}
    {A : S → Prop} {B : α → S → Prop} {epost : EPred} (F : T → Prop)
    (h : Triple (x.liftM f) A B epost) :
    Triple ((x.mapLens Lens.inl).liftM (sum f g)) (fun st => A st.1 ∧ F st.2)
      (fun a st => B a st.1 ∧ F st.2) epost := by
  rw [Handler.liftM_mapLens_inl_eq_of_apply _ _ (fun _ => rfl) x]
  constructor
  intro st hst
  exact wp_run_frame_of_apply_map_eq f _ (fun t s => (s, t)) (fun _ _ _ => rfl)
    (fun A F st => A st.1 ∧ F st.2)
    (fun _ _ st hst => ⟨st.1, st.2, rfl, hst⟩)
    (fun _ _ _ _ hA hF => ⟨hA, hF⟩) x B epost F st ⟨h.le_wp _ hst.1, hst.2⟩

/-- A right-component triple extends with any predicate on the unchanged left component. -/
theorem triple_sum_inr_frame (f : Stateful m S P) (g : Stateful m T Q) {x : FreeM Q α}
    {A : T → Prop} {B : α → T → Prop} {epost : EPred} (F : S → Prop)
    (h : Triple (x.liftM g) A B epost) :
    Triple ((x.mapLens Lens.inr).liftM (sum f g)) (fun st => F st.1 ∧ A st.2)
      (fun a st => F st.1 ∧ B a st.2) epost := by
  rw [Handler.liftM_mapLens_inr_eq_of_apply _ _ (fun _ => rfl) x]
  constructor
  intro st hst
  exact wp_run_frame_of_apply_map_eq g _ (fun s t => (s, t)) (fun _ _ _ => rfl)
    (fun A F st => F st.1 ∧ A st.2)
    (fun _ _ st hst => ⟨st.2, st.1, rfl, hst.2, hst.1⟩)
    (fun _ _ _ _ hA hF => ⟨hF, hA⟩) x B epost F st ⟨hst.1, h.le_wp _ hst.2⟩

/-- Hide an assertion's old right component and frame its current right component. -/
@[expose] def frameFst (F : T → Prop) (A : S × T → Prop) : S × T → Prop :=
  fun st => (∃ t, A (st.1, t)) ∧ F st.2

/-- Hide an assertion's old left component and frame its current left component. -/
@[expose] def frameSnd (F : S → Prop) (A : S × T → Prop) : S × T → Prop :=
  fun st => F st.1 ∧ ∃ s, A (s, st.2)

/-- On an assertion about the first component, `frameFst` is conjunction with the frame. -/
theorem frameFst_fst (F : T → Prop) (A : S → Prop) :
    frameFst F (fun st => A st.1) = fun st => A st.1 ∧ F st.2 := by
  funext st
  exact propext ⟨fun ⟨⟨_, hA⟩, hF⟩ => ⟨hA, hF⟩,
    fun ⟨hA, hF⟩ => ⟨⟨st.2, hA⟩, hF⟩⟩

/-- On an assertion about the second component, `frameSnd` is conjunction with the frame. -/
theorem frameSnd_snd (F : S → Prop) (A : T → Prop) :
    frameSnd F (fun st => A st.2) = fun st => F st.1 ∧ A st.2 := by
  funext st
  exact propext ⟨fun ⟨hF, _, hA⟩ => ⟨hF, hA⟩,
    fun ⟨hF, hA⟩ => ⟨hF, st.1, hA⟩⟩

private theorem sup_pred_apply_iff (c : (S → Prop) → Prop) (s : S) :
    CompleteLattice.sup c s ↔ ∃ A, c A ∧ A s := by
  constructor
  · have h : CompleteLattice.sup c ⊑ (fun s => ∃ A, c A ∧ A s) :=
      sup_le c fun A hA s h => ⟨A, hA, h⟩
    exact h s
  · rintro ⟨A, hA, hs⟩
    exact le_sup c hA s hs

/-- Right-component framing preserves arbitrary suprema of assertions. -/
instance instPreservesSupFrameFst (F : T → Prop) : PreservesSup (frameFst (S := S) F) where
  map_sup c := by
    funext st
    apply propext
    simp only [frameFst, sup_pred_apply_iff]
    constructor
    · rintro ⟨⟨t, A, hc, hA⟩, hF⟩
      exact ⟨frameFst F A, ⟨A, hc, rfl⟩, ⟨t, hA⟩, hF⟩
    · rintro ⟨_, ⟨A, hc, rfl⟩, ⟨t, hA⟩, hF⟩
      exact ⟨⟨t, A, hc, hA⟩, hF⟩

/-- Left-component framing preserves arbitrary suprema of assertions. -/
instance instPreservesSupFrameSnd (F : S → Prop) : PreservesSup (frameSnd (T := T) F) where
  map_sup c := by
    funext st
    apply propext
    simp only [frameSnd, sup_pred_apply_iff]
    constructor
    · rintro ⟨hF, s, A, hc, hA⟩
      exact ⟨frameSnd F A, ⟨A, hc, rfl⟩, hF, s, hA⟩
    · rintro ⟨_, ⟨A, hc, rfl⟩, hF, s, hA⟩
      exact ⟨hF, s, A, hc, hA⟩

/-- The left-summand program frames right-component predicates through `frameFst`. -/
theorem frames_sum_inl (f : Stateful m S P) (g : Stateful m T Q) (x : FreeM P α)
    (F : T → Prop) : WP.Frames frameFst ((x.mapLens Lens.inl).liftM (sum f g)) F := by
  rw [Handler.liftM_mapLens_inl_eq_of_apply _ _ (fun _ => rfl) x]
  constructor
  intro post epost
  exact wp_run_frame_of_apply_map_eq (fun a => sum f g (.inl a))
    (fun a => sum f g (.inl a)) (fun t st => (st.1, t))
    (fun _ _ _ => by
      dsimp only [sum, StateT.run, StateT.mk]
      rw [Functor.map_map]
      rfl)
    (fun A F => frameFst F A)
    (fun _ _ st hst => by
      obtain ⟨⟨t, hA⟩, hF⟩ := hst
      exact ⟨(st.1, t), st.2, rfl, hA, hF⟩)
    (fun _ _ st _ hA hF => ⟨⟨st.2, hA⟩, hF⟩) x post epost F

/-- The right-summand program frames left-component predicates through `frameSnd`. -/
theorem frames_sum_inr (f : Stateful m S P) (g : Stateful m T Q) (x : FreeM Q α)
    (F : S → Prop) : WP.Frames frameSnd ((x.mapLens Lens.inr).liftM (sum f g)) F := by
  rw [Handler.liftM_mapLens_inr_eq_of_apply _ _ (fun _ => rfl) x]
  constructor
  intro post epost
  exact wp_run_frame_of_apply_map_eq (fun a => sum f g (.inr a))
    (fun a => sum f g (.inr a)) (fun s st => (s, st.2))
    (fun _ _ _ => by
      dsimp only [sum, StateT.run, StateT.mk]
      rw [Functor.map_map]
      rfl)
    (fun A F => frameSnd F A)
    (fun _ _ st hst => by
      obtain ⟨hF, s, hA⟩ := hst
      exact ⟨(s, st.2), st.1, rfl, hA, hF⟩)
    (fun _ _ st _ hA hF => ⟨hF, st.1, hA⟩) x post epost F

end PFunctor.Handler.Stateful
