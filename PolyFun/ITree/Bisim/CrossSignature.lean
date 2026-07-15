/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Bisim.Bind

/-! # Weak bisimulation across event signatures

`ITree.CrossSignatureWeakBisim` is the cross-signature counterpart of
`WeakBisimRel`. It relates interaction trees whose event signatures, replies,
and return values may all differ. An `EventSignatureRel E F` supplies a
relation on event names and, for each related pair of names, a dependent
relation on their replies.

The Coq Interaction Trees library calls the corresponding construction `rutt`,
short for “relation up to tau”. PolyFun uses the descriptive semantic name in
its public API and retains `rutt` only as source provenance.

As with `WeakBisimRel`, finite silent-step stripping is separated from the
greatest fixed point.  This rules out an unsound proof that a terminating tree
is related to silent divergence by infinitely many one-sided τ rules.

The initial API is deliberately consumer-shaped rather than a port of the
Paco up-to tower from the Coq Interaction Trees library.  It contains:

* coinduction, unfolding, folding, constructors, and symmetry;
* equivalence with `WeakBisimRel` for the identity event-signature relation;
* two-sided `bind` and `map` congruence across signatures.
-/

@[expose] public section

universe uEA uEB uFA uFB uα uβ uγ uδ

namespace ITree

/-! ### Relations between event signatures -/

/-- A dependent relation between two event signatures.

`event a b` says that the event names correspond. Once event names are
related by `hab`, `reply a b hab x y` says that two possible replies
correspond. No totality or functionality is imposed: this accommodates refinements and
nondeterministic protocol relations as well as pure renamings. -/
structure EventSignatureRel (E : PFunctor.{uEA, uEB}) (F : PFunctor.{uFA, uFB}) where
  /-- Relation on event names. -/
  event : E.A → F.A → Prop
  /-- Dependent relation on replies to related event names. -/
  reply : (a : E.A) → (b : F.A) → event a b → E.B a → F.B b → Prop

namespace EventSignatureRel

/-- Reverse a relation between event signatures. -/
def flip {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    (r : EventSignatureRel E F) : EventSignatureRel F E where
  event b a := r.event a b
  reply b a hba y x := r.reply a b hba x y

/-- The identity relation on an event signature.

Replies use heterogeneous equality so the relation remains well typed before
the equality of event names is eliminated. -/
def eq (E : PFunctor.{uEA, uEB}) : EventSignatureRel E E where
  event := Eq
  reply _ _ _ x y := HEq x y

/-- A variance-correct map between event-signature relations. Events map
covariantly, while reply obligations map contravariantly because
`CrossSignatureWeakBisim` quantifies over every related reply pair. -/
structure Hom {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    (source target : EventSignatureRel E F) : Prop where
  /-- Every source-related event pair is target-related. -/
  event {a : E.A} {b : F.A} : source.event a b → target.event a b
  /-- Every target reply obligation is available to the source relation. -/
  reply {a : E.A} {b : F.A} (hab : source.event a b)
      {x : E.B a} {y : F.B b} :
    target.reply a b (event hab) x y → source.reply a b hab x y

namespace Hom

/-- Identity map of an event-signature relation. -/
protected theorem refl {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    (eventRel : EventSignatureRel E F) : Hom eventRel eventRel where
  event := id
  reply _ := id

end Hom

end EventSignatureRel

variable {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
  {α : Type uα} {β : Type uβ}

/-! ### Relational head matching -/

/-- One observable-head match between trees over potentially different event
signatures. -/
inductive CrossSignatureWeakBisim.HeadMatch
    (eventRel : EventSignatureRel E F) (resultRel : α → β → Prop)
    (treeRel : ITree E α → ITree F β → Prop) :
    ITree E α → ITree F β → Prop where
  /-- Pure heads carry related return values. -/
  | pure {t : ITree E α} {s : ITree F β} (x : α) (y : β) (hxy : resultRel x y)
      (ht : shape' t = ⟨.pure x, PEmpty.elim⟩)
      (hs : shape' s = ⟨.pure y, PEmpty.elim⟩) :
      CrossSignatureWeakBisim.HeadMatch eventRel resultRel treeRel t s
  /-- Query heads carry related events, and continuations are related for
  every pair of related replies. -/
  | query {t : ITree E α} {s : ITree F β}
      (a : E.A) (b : F.A) (hab : eventRel.event a b)
      (ct : E.B a → ITree E α) (cs : F.B b → ITree F β)
      (ht : shape' t = ⟨.query a, ct⟩)
      (hs : shape' s = ⟨.query b, cs⟩)
      (h : ∀ x y, eventRel.reply a b hab x y → treeRel (ct x) (cs y)) :
      CrossSignatureWeakBisim.HeadMatch eventRel resultRel treeRel t s
  /-- Silent heads continue through the relation. -/
  | tau {t : ITree E α} {s : ITree F β}
      (ct : PUnit.{uEB + 1} → ITree E α)
      (cs : PUnit.{uFB + 1} → ITree F β)
      (ht : shape' t = ⟨.step, ct⟩) (hs : shape' s = ⟨.step, cs⟩)
      (h : treeRel (ct PUnit.unit) (cs PUnit.unit)) :
      CrossSignatureWeakBisim.HeadMatch eventRel resultRel treeRel t s

namespace CrossSignatureWeakBisim.HeadMatch

/-- Monotonicity in the continuation relation. -/
theorem mono {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {treeRel nextTreeRel : ITree E α → ITree F β → Prop}
    (hmono : ∀ t s, treeRel t s → nextTreeRel t s) {t : ITree E α} {s : ITree F β}
    (h : CrossSignatureWeakBisim.HeadMatch eventRel resultRel treeRel t s) :
    CrossSignatureWeakBisim.HeadMatch eventRel resultRel nextTreeRel t s := by
  cases h with
  | pure x y hxy ht hs => exact .pure x y hxy ht hs
  | query a b hab ct cs ht hs hcont =>
      exact .query a b hab ct cs ht hs (fun x y hxy => hmono _ _ (hcont x y hxy))
  | tau ct cs ht hs hcont => exact .tau ct cs ht hs (hmono _ _ hcont)

/-- Monotonicity in the return-value relation. -/
theorem mono_result {eventRel : EventSignatureRel E F} {resultRel outputRel : α → β → Prop}
    (hmono : ∀ x y, resultRel x y → outputRel x y)
    {treeRel : ITree E α → ITree F β → Prop}
    {t : ITree E α} {s : ITree F β}
    (h : CrossSignatureWeakBisim.HeadMatch eventRel resultRel treeRel t s) :
    CrossSignatureWeakBisim.HeadMatch eventRel outputRel treeRel t s := by
  cases h with
  | pure x y hxy ht hs => exact .pure x y (hmono x y hxy) ht hs
  | query a b hab ct cs ht hs hcont => exact .query a b hab ct cs ht hs hcont
  | tau ct cs ht hs hcont => exact .tau ct cs ht hs hcont

/-- Change the event relation along a variance-correct signature-relation map. -/
theorem mono_eventRel {source target : EventSignatureRel E F}
    (map : EventSignatureRel.Hom source target)
    {resultRel : α → β → Prop} {treeRel : ITree E α → ITree F β → Prop}
    {t : ITree E α} {s : ITree F β}
    (h : CrossSignatureWeakBisim.HeadMatch source resultRel treeRel t s) :
    CrossSignatureWeakBisim.HeadMatch target resultRel treeRel t s := by
  cases h with
  | pure x y hxy ht hs => exact .pure x y hxy ht hs
  | query a b hab ct cs ht hs hcont =>
      refine .query a b (map.event hab) ct cs ht hs ?_
      intro x y hxy
      exact hcont x y (map.reply hab hxy)
  | tau ct cs ht hs hcont => exact .tau ct cs ht hs hcont

/-- Swap both trees and all component relations. -/
theorem swap {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {treeRel : ITree E α → ITree F β → Prop}
    {t : ITree E α} {s : ITree F β}
    (h : CrossSignatureWeakBisim.HeadMatch eventRel resultRel treeRel t s) :
    CrossSignatureWeakBisim.HeadMatch eventRel.flip
      (fun y x => resultRel x y) (fun s t => treeRel t s) s t := by
  cases h with
  | pure x y hxy ht hs => exact .pure y x hxy hs ht
  | query a b hab ct cs ht hs hcont =>
      exact .query b a hab cs ct hs ht (fun y x hyx => hcont x y hyx)
  | tau ct cs ht hs hcont => exact .tau cs ct hs ht hcont

end CrossSignatureWeakBisim.HeadMatch

/-! ### Greatest fixed point -/

/-- One-step functor for cross-signature relational trees. -/
def CrossSignatureWeakBisim.Layer
    (eventRel : EventSignatureRel E F) (resultRel : α → β → Prop)
    (treeRel : ITree E α → ITree F β → Prop)
    (t : ITree E α) (s : ITree F β) : Prop :=
  ∃ t' : ITree E α, ∃ s' : ITree F β,
    TauSteps t t' ∧ TauSteps s s' ∧
      CrossSignatureWeakBisim.HeadMatch eventRel resultRel treeRel t' s'

namespace CrossSignatureWeakBisim.Layer

/-- Monotonicity in the continuation relation. -/
theorem mono {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {treeRel nextTreeRel : ITree E α → ITree F β → Prop}
    (hmono : ∀ t s, treeRel t s → nextTreeRel t s) {t : ITree E α} {s : ITree F β}
    (h : CrossSignatureWeakBisim.Layer eventRel resultRel treeRel t s) :
    CrossSignatureWeakBisim.Layer eventRel resultRel nextTreeRel t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := h
  exact ⟨t', s', ht, hs, hm.mono hmono⟩

/-- Monotonicity in the return-value relation. -/
theorem mono_result {eventRel : EventSignatureRel E F} {resultRel outputRel : α → β → Prop}
    (hmono : ∀ x y, resultRel x y → outputRel x y)
    {treeRel : ITree E α → ITree F β → Prop}
    {t : ITree E α} {s : ITree F β}
    (h : CrossSignatureWeakBisim.Layer eventRel resultRel treeRel t s) :
    CrossSignatureWeakBisim.Layer eventRel outputRel treeRel t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := h
  exact ⟨t', s', ht, hs, hm.mono_result hmono⟩

end CrossSignatureWeakBisim.Layer

/-- Weak bisimulation between interaction trees over potentially different
event signatures. This is the Tarski greatest fixed point of
`CrossSignatureWeakBisim.Layer`. -/
def CrossSignatureWeakBisim (eventRel : EventSignatureRel E F) (resultRel : α → β → Prop)
    (t : ITree E α) (s : ITree F β) : Prop :=
  ∃ treeRel : ITree E α → ITree F β → Prop,
    (∀ t s, treeRel t s →
      CrossSignatureWeakBisim.Layer eventRel resultRel treeRel t s) ∧
    treeRel t s

namespace CrossSignatureWeakBisim

variable {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
  {γ : Type uγ} {δ : Type uδ}

/-- Coinduction principle for `CrossSignatureWeakBisim`. -/
theorem coinduct (eventRel : EventSignatureRel E F) (resultRel : α → β → Prop)
    (treeRel : ITree E α → ITree F β → Prop)
    (h : ∀ t s, treeRel t s →
      CrossSignatureWeakBisim.Layer eventRel resultRel treeRel t s)
    {t : ITree E α} {s : ITree F β} (hts : treeRel t s) :
    CrossSignatureWeakBisim eventRel resultRel t s :=
  ⟨treeRel, h, hts⟩

/-- Unfold a relational tree once. -/
theorem unfold {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {t : ITree E α} {s : ITree F β}
    (h : CrossSignatureWeakBisim eventRel resultRel t s) :
    CrossSignatureWeakBisim.Layer eventRel resultRel
      (CrossSignatureWeakBisim eventRel resultRel) t s := by
  obtain ⟨treeRel, hcl, hts⟩ := h
  obtain ⟨t', s', ht, hs, hm⟩ := hcl t s hts
  exact ⟨t', s', ht, hs, hm.mono (fun x y hxy => ⟨treeRel, hcl, hxy⟩)⟩

/-- Extract the stripped observable heads. -/
theorem dest {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {t : ITree E α} {s : ITree F β} (h : CrossSignatureWeakBisim eventRel resultRel t s) :
    ∃ t' : ITree E α, ∃ s' : ITree F β,
      TauSteps t t' ∧ TauSteps s s' ∧
        CrossSignatureWeakBisim.HeadMatch eventRel resultRel
          (CrossSignatureWeakBisim eventRel resultRel) t' s' :=
  unfold h

/-- Fold one `CrossSignatureWeakBisim.Layer` layer. -/
theorem fold {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {t : ITree E α} {s : ITree F β}
    (h : CrossSignatureWeakBisim.Layer eventRel resultRel
      (CrossSignatureWeakBisim eventRel resultRel) t s) :
    CrossSignatureWeakBisim eventRel resultRel t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := h
  refine coinduct eventRel resultRel
    (fun x y => CrossSignatureWeakBisim eventRel resultRel x y ∨ (x = t ∧ y = s)) ?_
    (Or.inr ⟨rfl, rfl⟩)
  rintro x y (hxy | ⟨rfl, rfl⟩)
  · exact (unfold hxy).mono (fun a b hab => Or.inl hab)
  · exact ⟨t', s', ht, hs, hm.mono (fun a b hab => Or.inl hab)⟩

/-- Pure trees are related when their return values are. -/
theorem pure {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {x : α} {y : β} (hxy : resultRel x y) :
    CrossSignatureWeakBisim eventRel resultRel (ITree.pure x) (ITree.pure y) := by
  apply fold
  exact ⟨_, _, .refl _, .refl _,
    CrossSignatureWeakBisim.HeadMatch.pure x y hxy (shape'_pure x) (shape'_pure y)⟩

/-- Related visible events produce related queries when all related replies
lead to related continuations. -/
theorem query {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    (a : E.A) (b : F.A) (hab : eventRel.event a b)
    (ct : E.B a → ITree E α) (cs : F.B b → ITree F β)
    (h : ∀ x y, eventRel.reply a b hab x y →
      CrossSignatureWeakBisim eventRel resultRel (ct x) (cs y)) :
    CrossSignatureWeakBisim eventRel resultRel (ITree.query a ct) (ITree.query b cs) := by
  apply fold
  exact ⟨_, _, .refl _, .refl _,
    CrossSignatureWeakBisim.HeadMatch.query a b hab ct cs
      (shape'_query a ct) (shape'_query b cs) h⟩

/-- Add a silent step on the left. -/
theorem step_left {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {t : ITree E α} {s : ITree F β} (h : CrossSignatureWeakBisim eventRel resultRel t s) :
    CrossSignatureWeakBisim eventRel resultRel (ITree.step t) s := by
  obtain ⟨t', s', ht, hs, hm⟩ := h.dest
  apply fold
  exact ⟨t', s', (TauSteps.one _ (shape'_step t)).trans ht, hs, hm⟩

/-- Add a silent step on the right. -/
theorem step_right {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {t : ITree E α} {s : ITree F β} (h : CrossSignatureWeakBisim eventRel resultRel t s) :
    CrossSignatureWeakBisim eventRel resultRel t (ITree.step s) := by
  obtain ⟨t', s', ht, hs, hm⟩ := h.dest
  apply fold
  exact ⟨t', s', ht, (TauSteps.one _ (shape'_step s)).trans hs, hm⟩

/-- Add silent steps to both sides. -/
theorem step {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {t : ITree E α} {s : ITree F β} (h : CrossSignatureWeakBisim eventRel resultRel t s) :
    CrossSignatureWeakBisim eventRel resultRel (ITree.step t) (ITree.step s) :=
  (step_left h).step_right

/-- Strip one silent step from the right endpoint of a relational tree. -/
theorem step_absorb_right {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {t : ITree E α} {s : ITree F β}
    (c : PUnit.{uFB + 1} → ITree F β) (h : CrossSignatureWeakBisim eventRel resultRel t s)
    (hstep : shape' s = ⟨.step, c⟩) :
    CrossSignatureWeakBisim eventRel resultRel t (c PUnit.unit) := by
  refine coinduct eventRel resultRel
    (fun x z => CrossSignatureWeakBisim eventRel resultRel x z ∨
      ∃ (s' : ITree F β) (c' : PUnit.{uFB + 1} → ITree F β),
        CrossSignatureWeakBisim eventRel resultRel x s' ∧
          shape' s' = ⟨.step, c'⟩ ∧ z = c' PUnit.unit)
    ?_ (Or.inr ⟨s, c, h, hstep, rfl⟩)
  intro a b hab
  rcases hab with hab | ⟨s', c', hab, hstep', rfl⟩
  · obtain ⟨a', b', ha, hb, M⟩ := hab.dest
    exact ⟨a', b', ha, hb, M.mono (fun _ _ hxy => Or.inl hxy)⟩
  · obtain ⟨a', s₁, ha, hs, M⟩ := hab.dest
    rcases TauSteps.step_cases c' hstep' hs with hs_eq | hs_strict
    · subst hs_eq
      cases M with
      | pure _ _ _ _ hs_bad => exfalso; rw [hstep'] at hs_bad; cases hs_bad
      | query _ _ _ _ _ _ hs_bad _ =>
          exfalso; rw [hstep'] at hs_bad; cases hs_bad
      | tau ct cs ht_a hs_a hr =>
          have hcc : cs = c' := TauSteps.cont_eq hs_a hstep'
          subst hcc
          rcases hsh : shape' (cs PUnit.unit) with ⟨sh, cc⟩
          cases sh with
          | pure r =>
              have hsh' : shape' (cs PUnit.unit) =
                  ⟨Shape.pure r, PEmpty.elim⟩ := by
                rw [hsh]
                congr 1
                funext z
                exact z.elim
              obtain ⟨X, Y, hX, hY, MXY⟩ := hr.dest
              have hYeq : Y = cs PUnit.unit :=
                TauSteps.rigid_of_pure r hsh' hY
              subst hYeq
              cases MXY with
              | pure x y hxy hX' hY' =>
                  have heq : (⟨Shape.pure y, PEmpty.elim⟩ :
                      (Poly F β).Obj (ITree F β)) =
                      ⟨Shape.pure r, PEmpty.elim⟩ := hY'.symm.trans hsh'
                  have hyr : y = r := Shape.pure.inj (Sigma.mk.inj heq).1
                  subst y
                  refine ⟨X, cs PUnit.unit,
                    ha.trans ((TauSteps.one ct ht_a).trans hX), .refl _, ?_⟩
                  exact CrossSignatureWeakBisim.HeadMatch.pure x r hxy hX' hsh'
              | query _ _ _ _ _ _ hY' _ =>
                  exfalso; rw [hY'] at hsh'; cases hsh'
              | tau _ _ _ hY' _ =>
                  exfalso; rw [hY'] at hsh'; cases hsh'
          | step =>
              refine ⟨a', cs PUnit.unit, ha, .refl _, ?_⟩
              refine CrossSignatureWeakBisim.HeadMatch.tau ct cc ht_a hsh ?_
              exact Or.inr ⟨cs PUnit.unit, cc, hr, hsh, rfl⟩
          | query eventF =>
              obtain ⟨X, Y, hX, hY, MXY⟩ := hr.dest
              have hYeq : Y = cs PUnit.unit :=
                TauSteps.rigid_of_query eventF cc hsh hY
              subst hYeq
              cases MXY with
              | pure _ _ _ _ hY' => exfalso; rw [hY'] at hsh; cases hsh
              | query eventE eventF' hevents cX cY hX' hY' hcont =>
                  have heq : (⟨Shape.query eventF', cY⟩ :
                      (Poly F β).Obj (ITree F β)) =
                      ⟨Shape.query eventF, cc⟩ := hY'.symm.trans hsh
                  have hevent : eventF' = eventF :=
                    Shape.query.inj (Sigma.mk.inj heq).1
                  subst eventF'
                  have hc : cY = cc := eq_of_heq (Sigma.mk.inj heq).2
                  subst cY
                  refine ⟨X, cs PUnit.unit,
                    ha.trans ((TauSteps.one ct ht_a).trans hX), .refl _, ?_⟩
                  exact CrossSignatureWeakBisim.HeadMatch.query
                    eventE eventF hevents cX cc hX' hsh
                    (fun x y hxy => Or.inl (hcont x y hxy))
              | tau _ _ _ hY' _ => exfalso; rw [hY'] at hsh; cases hsh
    · exact ⟨a', s₁, ha, hs_strict,
        M.mono (fun _ _ hxy => Or.inl hxy)⟩

/-- Strip finitely many silent steps from the right endpoint. -/
theorem absorb_tauSteps_right
    {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {t : ITree E α} {s s' : ITree F β}
    (h : CrossSignatureWeakBisim eventRel resultRel t s)
    (hstrip : TauSteps s s') :
    CrossSignatureWeakBisim eventRel resultRel t s' := by
  induction hstrip generalizing t with
  | refl _ => exact h
  | @step _ _ c ht hr ih => exact ih (step_absorb_right c h ht)

/-- Symmetry, with the event, reply, and return relations reversed. -/
theorem symm {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {t : ITree E α} {s : ITree F β} (h : CrossSignatureWeakBisim eventRel resultRel t s) :
    CrossSignatureWeakBisim eventRel.flip (fun y x => resultRel x y) s t := by
  obtain ⟨treeRel, hcl, hts⟩ := h
  refine coinduct eventRel.flip (fun y x => resultRel x y) (fun s t => treeRel t s) ?_ hts
  intro s t hst
  obtain ⟨t', s', ht, hs, hm⟩ := hcl t s hst
  exact ⟨s', t', hs, ht, hm.swap⟩

/-- Strip finitely many silent steps from the left endpoint. -/
theorem tauSteps_left
    {eventRel : EventSignatureRel E F} {resultRel : α → β → Prop}
    {t t' : ITree E α} {s : ITree F β}
    (h : CrossSignatureWeakBisim eventRel resultRel t s)
    (hstrip : TauSteps t t') :
    CrossSignatureWeakBisim eventRel resultRel t' s := by
  have hs := absorb_tauSteps_right (eventRel := eventRel.flip)
    (resultRel := fun y x => resultRel x y) h.symm hstrip
  exact hs.symm

/-- Monotonicity in the relation on return values. -/
theorem mono_result {eventRel : EventSignatureRel E F} {resultRel outputRel : α → β → Prop}
    (hmono : ∀ x y, resultRel x y → outputRel x y)
    {t : ITree E α} {s : ITree F β} (h : CrossSignatureWeakBisim eventRel resultRel t s) :
    CrossSignatureWeakBisim eventRel outputRel t s := by
  obtain ⟨treeRel, hcl, hts⟩ := h
  exact ⟨treeRel, fun x y hxy => (hcl x y hxy).mono_result hmono, hts⟩

/-- Change the event relation along a variance-correct signature-relation map. -/
theorem mono_eventRel {source target : EventSignatureRel E F}
    (map : EventSignatureRel.Hom source target) {resultRel : α → β → Prop}
    {t : ITree E α} {s : ITree F β} (h : CrossSignatureWeakBisim source resultRel t s) :
    CrossSignatureWeakBisim target resultRel t s := by
  obtain ⟨treeRel, hcl, hts⟩ := h
  exact ⟨treeRel, fun x y hxy => by
    obtain ⟨x', y', hx, hy, hm⟩ := hcl x y hxy
    exact ⟨x', y', hx, hy, hm.mono_eventRel map⟩, hts⟩

/-- Related events yield relationally related single-event trees. -/
theorem lift (a : E.A) (b : F.A) (hab : eventRel.event a b) :
    CrossSignatureWeakBisim eventRel (eventRel.reply a b hab) (ITree.lift a) (ITree.lift b) := by
  unfold ITree.lift
  apply query a b hab ITree.pure ITree.pure
  intro x y hxy
  exact pure hxy

/-! ### Compatibility with same-signature weak bisimulation -/

/-- Identity-signature head matches convert to ordinary relational head
matches. -/
theorem identity_headMatch_to_matchRel
    {treeRel : ITree E α → ITree E β → Prop} {t : ITree E α} {s : ITree E β}
    (h : CrossSignatureWeakBisim.HeadMatch
      (EventSignatureRel.eq E) resultRel treeRel t s) :
    MatchRel resultRel treeRel t s := by
  cases h with
  | pure x y hxy ht hs => exact .pure x y hxy ht hs
  | query a b hab ct cs ht hs hcont =>
      change a = b at hab
      subst b
      exact .query a ct cs ht hs (fun x => hcont x x HEq.rfl)
  | tau ct cs ht hs hcont => exact .tau ct cs ht hs hcont

/-- Ordinary relational head matches embed into identity-signature matches. -/
theorem matchRel_to_identity_headMatch
    {treeRel : ITree E α → ITree E β → Prop} {t : ITree E α} {s : ITree E β}
    (h : MatchRel resultRel treeRel t s) :
    CrossSignatureWeakBisim.HeadMatch
      (EventSignatureRel.eq E) resultRel treeRel t s := by
  cases h with
  | pure x y hxy ht hs => exact .pure x y hxy ht hs
  | query a ct cs ht hs hcont =>
      refine .query a a rfl ct cs ht hs ?_
      intro x y hxy
      change HEq x y at hxy
      have : x = y := eq_of_heq hxy
      subst y
      exact hcont x
  | tau ct cs ht hs hcont => exact .tau ct cs ht hs hcont

/-- `CrossSignatureWeakBisim` specializes exactly to `WeakBisimRel` for the
identity event-signature relation. -/
theorem eq_iff_weakBisimRel {t : ITree E α} {s : ITree E β} :
    CrossSignatureWeakBisim (EventSignatureRel.eq E) resultRel t s ↔
      WeakBisimRel resultRel t s := by
  constructor
  · intro h
    obtain ⟨treeRel, hcl, hts⟩ := h
    refine WeakBisimRel.coinduct resultRel treeRel ?_ hts
    intro x y hxy
    obtain ⟨x', y', hx, hy, hm⟩ := hcl x y hxy
    exact ⟨x', y', hx, hy, identity_headMatch_to_matchRel hm⟩
  · intro h
    obtain ⟨treeRel, hcl, hts⟩ := h
    refine coinduct (EventSignatureRel.eq E) resultRel treeRel ?_ hts
    intro x y hxy
    obtain ⟨x', y', hx, hy, hm⟩ := hcl x y hxy
    exact ⟨x', y', hx, hy, matchRel_to_identity_headMatch hm⟩

/-- Reflexivity for the identity relations on events, replies, and return
values. -/
@[refl] theorem refl (t : ITree E α) :
    CrossSignatureWeakBisim (EventSignatureRel.eq E) Eq t t :=
  eq_iff_weakBisimRel.mpr (WeakBisim.refl t)

/-! ### Monad congruence -/

/-- Two-sided relational congruence for `bind` across event signatures. -/
theorem bind {resultRel : α → β → Prop} {outputRel : γ → δ → Prop}
    {u : ITree E α} {v : ITree F β}
    {f : α → ITree E γ} {g : β → ITree F δ}
    (trees_related : CrossSignatureWeakBisim eventRel resultRel u v)
    (continuations_related : ∀ x y, resultRel x y →
      CrossSignatureWeakBisim eventRel outputRel (f x) (g y)) :
    CrossSignatureWeakBisim eventRel outputRel (ITree.bind u f) (ITree.bind v g) := by
  refine coinduct eventRel outputRel
    (fun x y =>
      (∃ u v, CrossSignatureWeakBisim eventRel resultRel u v ∧
        x = ITree.bind u f ∧ y = ITree.bind v g) ∨
      CrossSignatureWeakBisim eventRel outputRel x y) ?_
    (Or.inl ⟨u, v, trees_related, rfl, rfl⟩)
  rintro x y (⟨u, v, trees_related, rfl, rfl⟩ | hxy)
  · obtain ⟨u', v', hu, hv, hm⟩ := trees_related.dest
    cases hm with
    | pure x y hxy hu' hv' =>
        have hut : u' = ITree.pure x := by
          apply PFunctor.M.eq_of_dest_eq
          change shape' u' = shape' (ITree.pure x)
          exact hu'.trans (shape'_pure x).symm
        have hvt : v' = ITree.pure y := by
          apply PFunctor.M.eq_of_dest_eq
          change shape' v' = shape' (ITree.pure y)
          exact hv'.trans (shape'_pure y).symm
        subst hut
        subst hvt
        obtain ⟨x', y', hx, hy, hm⟩ := (continuations_related x y hxy).dest
        refine ⟨x', y', ?_, ?_, hm.mono (fun _ _ h => Or.inr h)⟩
        · have huf : TauSteps (ITree.bind u f) (f x) := by
            simpa only [bind_pure_left] using hu.bind f
          exact huf.trans hx
        · have hvg : TauSteps (ITree.bind v g) (g y) := by
            simpa only [bind_pure_left] using hv.bind g
          exact hvg.trans hy
    | query a b hab cu cv hu' hv' hcont =>
        refine ⟨ITree.bind u' f, ITree.bind v' g, hu.bind f, hv.bind g, ?_⟩
        refine CrossSignatureWeakBisim.HeadMatch.query a b hab (fun x => ITree.bind (cu x) f)
          (fun y => ITree.bind (cv y) g)
          (dest_bind_query f u' a cu hu') (dest_bind_query g v' b cv hv') ?_
        intro x y hxy
        exact Or.inl ⟨cu x, cv y, hcont x y hxy, rfl, rfl⟩
    | tau cu cv hu' hv' hcont =>
        refine ⟨ITree.bind u' f, ITree.bind v' g, hu.bind f, hv.bind g, ?_⟩
        refine CrossSignatureWeakBisim.HeadMatch.tau (fun _ => ITree.bind (cu PUnit.unit) f)
          (fun _ => ITree.bind (cv PUnit.unit) g)
          (dest_bind_step f u' cu hu') (dest_bind_step g v' cv hv') ?_
        exact Or.inl ⟨cu PUnit.unit, cv PUnit.unit, hcont, rfl, rfl⟩
  · obtain ⟨x', y', hx, hy, hm⟩ := hxy.dest
    exact ⟨x', y', hx, hy, hm.mono (fun _ _ h => Or.inr h)⟩

/-- Relational congruence for `ITree.map` across event signatures. -/
theorem map {outputRel : γ → δ → Prop} (f : α → γ) (g : β → δ)
    {u : ITree E α} {v : ITree F β}
    (trees_related : CrossSignatureWeakBisim eventRel resultRel u v)
    (continuations_related : ∀ x y, resultRel x y → outputRel (f x) (g y)) :
    CrossSignatureWeakBisim eventRel outputRel (ITree.map f u) (ITree.map g v) := by
  unfold ITree.map
  exact trees_related.bind (fun x y hxy => pure (continuations_related x y hxy))

end CrossSignatureWeakBisim

end ITree
