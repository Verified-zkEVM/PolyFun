/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Construct

/-! # Bisimulation for Interaction Trees

This module defines the two equivalences on `ITree F α` used throughout the
algebraic theory:

* `ITree.Bisim t s` — *strong* (a.k.a. structural) bisimulation. Two ITrees
  are strongly bisimilar iff their one-step shapes match and the
  continuations are pointwise bisimilar. By the universal property of
  `PFunctor.M`, strong bisimulation coincides with Lean equality;
  for that reason we set `Bisim = (· = ·)`.

* `ITree.WeakBisimRel RR t s` — relational weak bisimulation (Coq `euttR`).
  The trees share an event signature, but their return types and universes are
  independent; pure leaves are compared by `RR`.

* `ITree.WeakBisim t s` — the equality-specialized weak bisimulation (Coq
  `eutt`). Two ITrees are
  weakly bisimilar iff, after stripping any *finitely many* leading `step`
  nodes from each side, their observable heads agree (pure leaves, visible
  queries, or paired silent steps) and continuations are pointwise weakly
  bisimilar. This is the intended notion of ITree equivalence for
  reasoning about programs.

## Design

The naive coinductive definition with `tauL` / `tauR` constructors
directly appearing in a coinductive predicate is **unsound**: it admits
`WeakBisim (pure r) diverge` via repeated `tauR` applications, because
the greatest fixed point closes under the (unbounded) coinductive
stripping. The fix follows Xia et al. (POPL 2020): wrap τ-stripping in
an *inductive* relation `TauSteps` (so each stripping chain is finite),
and let each coinductive "step" of `WeakBisim` consist of stripping
finitely many τ's from each side and then matching observable heads via
the `Match` functor.

We define `WeakBisimRel` as the Tarski greatest fixed point of the
one-step functor packaged by `TauSteps` + `MatchRel`, i.e. as the largest
relation `R` that is closed under the functor. This `∃ R, …` form is
used because Lean's `coinductive` keyword requires syntactic
monotonicity, which does not see through the separately-declared
`MatchRel` inductive.

## Implementation notes

Lean supports `coinductive` *predicates*, but the monotonicity
checker is syntactic. We therefore use the explicit Tarski formulation
`∃ R, R t s ∧ closure`. The coinduction principle is then the
constructor itself (`WeakBisimRel.coinduct`), and the standard algebraic
laws for the equality specialization are recovered by exhibiting an
appropriate witness relation `R` in each case.

All event-position, event-direction, and result universes are independent.
The two trees in `WeakBisimRel` deliberately share one event signature;
relating different signatures is the separate relational-simulation layer.
-/

@[expose] public section

universe uFA uFB uα uβ

namespace ITree

variable {F : PFunctor.{uFA, uFB}} {α : Type uα} {β : Type uβ}

/-! ### Strong bisimulation -/

/-- Strong bisimulation on interaction trees. Two ITrees are strongly
bisimilar iff they are equal as elements of the M-type `PFunctor.M (Poly F α)`,
which by `PFunctor.M.bisim` is the same as having matching one-step shapes
with pointwise-bisimilar continuations. -/
@[reducible]
def Bisim (t s : ITree F α) : Prop := t = s

@[inherit_doc] scoped infix:50 " ≅ " => ITree.Bisim

namespace Bisim

variable {t s u : ITree F α}

@[refl] theorem refl' (t : ITree F α) : t ≅ t := rfl

@[symm] theorem symm' (h : t ≅ s) : s ≅ t := Eq.symm h

@[trans] theorem trans' (h₁ : t ≅ s) (h₂ : s ≅ u) : t ≅ u := Eq.trans h₁ h₂

/-- One-step characterisation: two ITrees are strongly bisimilar iff their
`shape'` agrees. Provable by `PFunctor.M.bisim`. -/
theorem dest (h : t ≅ s) : shape' t = shape' s := by
  cases h; rfl

end Bisim

/-! ### Finite τ-stripping

`TauSteps t t'` captures the (deterministic, partial) operation of
stripping finitely many leading silent-step nodes from `t` to reach `t'`.
Being an inductive family, every derivation has a finite length. -/

/-- `TauSteps t t'` iff `t'` is obtained from `t` by stripping finitely
many leading `step` nodes. -/
inductive TauSteps : ITree F α → ITree F α → Prop where
  /-- Strip zero steps: `t` is reachable from itself. -/
  | refl (t : ITree F α) : TauSteps t t
  /-- Strip one step from a step-headed tree and continue stripping. -/
  | step {t t' : ITree F α} (c : PUnit.{uFB + 1} → ITree F α)
      (ht : shape' t = ⟨.step, c⟩) (hr : TauSteps (c PUnit.unit) t') :
      TauSteps t t'

namespace TauSteps

/-- Transitivity of τ-stripping. -/
theorem trans {t s u : ITree F α} (h₁ : TauSteps t s) (h₂ : TauSteps s u) :
    TauSteps t u := by
  induction h₁ with
  | refl _ => exact h₂
  | step c ht _ ih => exact .step c ht (ih h₂)

/-- Stripping one step is available when the head is a step. -/
theorem one {t : ITree F α} (c : PUnit.{uFB + 1} → ITree F α)
    (ht : shape' t = ⟨.step, c⟩) : TauSteps t (c PUnit.unit) :=
  TauSteps.step (t' := c PUnit.unit) c ht (TauSteps.refl _)

/-- The `.step` relation is deterministic on step-headed trees. -/
theorem cont_eq {t : ITree F α} {c c' : PUnit.{uFB + 1} → ITree F α}
    (h : shape' t = ⟨.step, c⟩) (h' : shape' t = ⟨.step, c'⟩) : c = c' := by
  have hmk := h.symm.trans h'
  exact eq_of_heq (Sigma.mk.inj hmk).2

/-- `TauSteps` is linear: any two strippings from the same tree are
comparable. Uses determinism of `shape'`. -/
theorem linear {t a b : ITree F α}
    (ha : TauSteps t a) (hb : TauSteps t b) :
    TauSteps a b ∨ TauSteps b a := by
  induction ha generalizing b with
  | refl _ => exact Or.inl hb
  | @step t t' c ht hr ih =>
      cases hb with
      | refl _ => exact Or.inr (TauSteps.step (t' := t') c ht hr)
      | @step _ _ c' ht' hr' =>
          have hcc : c = c' := cont_eq ht ht'
          subst hcc
          exact ih hr'

end TauSteps

/-! ### Relational head matching

`MatchRel RR R t s` pins two trees whose observable heads agree. Pure
leaves are compared by `RR`; visible queries share an event and compare
their continuations pointwise by `R`; paired silent steps also continue
through `R`. There is no τ-stripping here: stripping happens separately
via `TauSteps` before invoking `MatchRel`. -/

/-- One-step observable head match for trees with potentially different
return types. -/
inductive MatchRel (RR : α → β → Prop)
    (R : ITree F α → ITree F β → Prop) :
    ITree F α → ITree F β → Prop where
  /-- Both heads are pure leaves carrying `RR`-related values. -/
  | pure {t : ITree F α} {s : ITree F β} (r : α) (r' : β) (hrr : RR r r')
      (ht : shape' t = ⟨.pure r, PEmpty.elim⟩)
      (hs : shape' s = ⟨.pure r', PEmpty.elim⟩) :
      MatchRel RR R t s
  /-- Both heads are visible queries on the same event. -/
  | query {t : ITree F α} {s : ITree F β} (a : F.A)
      (c : F.B a → ITree F α) (c' : F.B a → ITree F β)
      (ht : shape' t = ⟨.query a, c⟩) (hs : shape' s = ⟨.query a, c'⟩)
      (h : ∀ b, R (c b) (c' b)) :
      MatchRel RR R t s
  /-- Both heads are silent steps, with continuations related by `R`. -/
  | tau {t : ITree F α} {s : ITree F β}
      (ct : PUnit.{uFB + 1} → ITree F α)
      (cs : PUnit.{uFB + 1} → ITree F β)
      (ht : shape' t = ⟨.step, ct⟩) (hs : shape' s = ⟨.step, cs⟩)
      (h : R (ct PUnit.unit) (cs PUnit.unit)) :
      MatchRel RR R t s

namespace MatchRel

/-- Monotonicity in the continuation relation. -/
theorem mono {RR : α → β → Prop}
    {R R' : ITree F α → ITree F β → Prop}
    (h : ∀ a b, R a b → R' a b) {t : ITree F α} {s : ITree F β}
    (hM : MatchRel RR R t s) : MatchRel RR R' t s := by
  cases hM with
  | pure r r' hrr ht hs => exact .pure r r' hrr ht hs
  | query a c c' ht hs hcc => exact .query a c c' ht hs (fun b => h _ _ (hcc b))
  | tau ct cs ht hs hr => exact .tau ct cs ht hs (h _ _ hr)

/-- Monotonicity in the return-value relation. -/
theorem mono_result {RR RR' : α → β → Prop}
    (h : ∀ a b, RR a b → RR' a b)
    {R : ITree F α → ITree F β → Prop} {t : ITree F α} {s : ITree F β}
    (hM : MatchRel RR R t s) : MatchRel RR' R t s := by
  cases hM with
  | pure r r' hrr ht hs => exact .pure r r' (h _ _ hrr) ht hs
  | query a c c' ht hs hcc => exact .query a c c' ht hs hcc
  | tau ct cs ht hs hr => exact .tau ct cs ht hs hr

/-- Swap the two trees and both component relations. -/
theorem swap {RR : α → β → Prop} {R : ITree F α → ITree F β → Prop}
    {t : ITree F α} {s : ITree F β} (hM : MatchRel RR R t s) :
    MatchRel (fun b a => RR a b) (fun y x => R x y) s t := by
  cases hM with
  | pure r r' hrr ht hs => exact .pure r' r hrr hs ht
  | query a c c' ht hs hcc => exact .query a c' c hs ht (fun b => hcc b)
  | tau ct cs ht hs hr => exact .tau cs ct hs ht hr

end MatchRel

/-! ### Equality-specialized head match compatibility view

`Match R t s` pins two trees whose observable heads agree. There is no
τ-stripping here: stripping happens separately via `TauSteps` before
invoking `Match`. -/

/-- One-step observable head match. Two trees have matching heads iff
both are pure leaves carrying the same value, both are queries with the
same event name and pointwise `R`-related continuations, or both are
step-headed with `R`-related step continuations. -/
inductive Match (R : ITree F α → ITree F α → Prop) :
    ITree F α → ITree F α → Prop where
  /-- Both heads are pure leaves with the same value. -/
  | pure {t s : ITree F α} (r : α)
      (ht : shape' t = ⟨.pure r, PEmpty.elim⟩)
      (hs : shape' s = ⟨.pure r, PEmpty.elim⟩) :
      Match R t s
  /-- Both heads are visible queries on the same event. -/
  | query {t s : ITree F α} (a : F.A) (c c' : F.B a → ITree F α)
      (ht : shape' t = ⟨.query a, c⟩) (hs : shape' s = ⟨.query a, c'⟩)
      (h : ∀ b, R (c b) (c' b)) :
      Match R t s
  /-- Both heads are silent steps, with continuations related by `R`. -/
  | tau {t s : ITree F α} (ct cs : PUnit.{uFB + 1} → ITree F α)
      (ht : shape' t = ⟨.step, ct⟩) (hs : shape' s = ⟨.step, cs⟩)
      (h : R (ct PUnit.unit) (cs PUnit.unit)) :
      Match R t s

namespace Match

/-- Monotonicity: `Match` is monotone in its relation parameter. -/
theorem mono {R R' : ITree F α → ITree F α → Prop}
    (h : ∀ a b, R a b → R' a b) {t s : ITree F α}
    (hM : Match R t s) : Match R' t s := by
  cases hM with
  | pure r ht hs => exact .pure r ht hs
  | query a c c' ht hs hcc => exact .query a c c' ht hs (fun b => h _ _ (hcc b))
  | tau ct cs ht hs hr => exact .tau ct cs ht hs (h _ _ hr)

/-- `Match` is symmetric in the two sides when `R` is swapped. -/
theorem swap {R : ITree F α → ITree F α → Prop} {t s : ITree F α}
    (hM : Match R t s) : Match (fun x y => R y x) s t := by
  cases hM with
  | pure r ht hs => exact .pure r hs ht
  | query a c c' ht hs hcc => exact .query a c' c hs ht (fun b => hcc b)
  | tau ct cs ht hs hr => exact .tau cs ct hs ht hr

end Match

/-- Embed the equality-specialized compatibility view into `MatchRel`. -/
theorem Match.toMatchRel {R : ITree F α → ITree F α → Prop}
    {t s : ITree F α} (hM : Match R t s) : MatchRel Eq R t s := by
  cases hM with
  | pure r ht hs => exact .pure r r rfl ht hs
  | query a c c' ht hs hcc => exact .query a c c' ht hs hcc
  | tau ct cs ht hs hr => exact .tau ct cs ht hs hr

/-- Recover the compatibility `Match` view from an equality-specialized
relational head match. -/
theorem MatchRel.toMatch {R : ITree F α → ITree F α → Prop}
    {t s : ITree F α} (hM : MatchRel Eq R t s) : Match R t s := by
  cases hM with
  | pure r r' hrr ht hs =>
      subst r'
      exact .pure r ht hs
  | query a c c' ht hs hcc => exact .query a c c' ht hs hcc
  | tau ct cs ht hs hr => exact .tau ct cs ht hs hr

/-! ### Relational weak bisimulation -/

/-- One-step unfolding functor for relational weak bisimulation. -/
def WeakBisimRelF (RR : α → β → Prop)
    (R : ITree F α → ITree F β → Prop)
    (t : ITree F α) (s : ITree F β) : Prop :=
  ∃ t' : ITree F α, ∃ s' : ITree F β,
    TauSteps t t' ∧ TauSteps s s' ∧ MatchRel RR R t' s'

namespace WeakBisimRelF

/-- Monotonicity in the continuation relation. -/
theorem mono {RR : α → β → Prop}
    {R R' : ITree F α → ITree F β → Prop}
    (h : ∀ a b, R a b → R' a b) {t : ITree F α} {s : ITree F β}
    (hF : WeakBisimRelF RR R t s) : WeakBisimRelF RR R' t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := hF
  exact ⟨t', s', ht, hs, hm.mono h⟩

/-- Monotonicity in the return-value relation. -/
theorem mono_result {RR RR' : α → β → Prop}
    (h : ∀ a b, RR a b → RR' a b)
    {R : ITree F α → ITree F β → Prop} {t : ITree F α} {s : ITree F β}
    (hF : WeakBisimRelF RR R t s) : WeakBisimRelF RR' R t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := hF
  exact ⟨t', s', ht, hs, hm.mono_result h⟩

end WeakBisimRelF

/-- Relational weak bisimulation (`euttR`). The trees share an event
signature but may have return types in different universes. -/
def WeakBisimRel (RR : α → β → Prop) (t : ITree F α) (s : ITree F β) : Prop :=
  ∃ R : ITree F α → ITree F β → Prop,
    (∀ a b, R a b → WeakBisimRelF RR R a b) ∧ R t s

@[inherit_doc] scoped notation:50 t " ≈[" RR "] " s => ITree.WeakBisimRel RR t s

namespace WeakBisimRel

/-- Coinduction principle for relational weak bisimulation. -/
theorem coinduct (RR : α → β → Prop) (R : ITree F α → ITree F β → Prop)
    (h : ∀ a b, R a b → WeakBisimRelF RR R a b)
    {a : ITree F α} {b : ITree F β} (hab : R a b) : WeakBisimRel RR a b :=
  ⟨R, h, hab⟩

/-- Relational weak bisimulation is closed under its one-step functor. -/
theorem unfold {RR : α → β → Prop} {t : ITree F α} {s : ITree F β}
    (h : WeakBisimRel RR t s) : WeakBisimRelF RR (WeakBisimRel RR) t s := by
  obtain ⟨R, hcl, hR⟩ := h
  obtain ⟨t', s', ht, hs, hm⟩ := hcl _ _ hR
  exact ⟨t', s', ht, hs, hm.mono (fun x y hxy => ⟨R, hcl, hxy⟩)⟩

/-- Extract the stripped-heads relational match witness. -/
theorem dest {RR : α → β → Prop} {t : ITree F α} {s : ITree F β}
    (h : WeakBisimRel RR t s) :
    ∃ t' : ITree F α, ∃ s' : ITree F β,
      TauSteps t t' ∧ TauSteps s s' ∧ MatchRel RR (WeakBisimRel RR) t' s' :=
  unfold h

/-- Folding rule for relational weak bisimulation. -/
theorem fold {RR : α → β → Prop} {t : ITree F α} {s : ITree F β}
    (h : WeakBisimRelF RR (WeakBisimRel RR) t s) : WeakBisimRel RR t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := h
  refine coinduct RR (fun a b => WeakBisimRel RR a b ∨ (a = t ∧ b = s))
    ?_ (Or.inr ⟨rfl, rfl⟩)
  rintro a b (hab | ⟨rfl, rfl⟩)
  · exact (unfold hab).mono (fun x y hxy => Or.inl hxy)
  · exact ⟨t', s', ht, hs, hm.mono (fun x y hxy => Or.inl hxy)⟩

/-- Monotonicity in the relation used to compare pure leaves. -/
theorem mono_result {RR RR' : α → β → Prop}
    (hRR : ∀ a b, RR a b → RR' a b) {t : ITree F α} {s : ITree F β}
    (h : WeakBisimRel RR t s) : WeakBisimRel RR' t s := by
  obtain ⟨R, hcl, hR⟩ := h
  exact ⟨R, fun a b hab => (hcl a b hab).mono_result hRR, hR⟩

end WeakBisimRel

/-! ### Equality-specialized weak bisimulation -/

/-- One-step unfolding functor for weak bisimulation: strip finitely many
τ's from each side (via `TauSteps`) and then match observable heads (via
`Match`). `WeakBisim` is the Tarski greatest fixed point of this functor. -/
def WeakBisimF (R : ITree F α → ITree F α → Prop) (t s : ITree F α) : Prop :=
  ∃ t' s' : ITree F α, TauSteps t t' ∧ TauSteps s s' ∧ Match R t' s'

/-- `WeakBisimF` is monotone in its relation parameter. -/
theorem WeakBisimF.mono {R R' : ITree F α → ITree F α → Prop}
    (h : ∀ a b, R a b → R' a b) {t s : ITree F α}
    (hF : WeakBisimF R t s) : WeakBisimF R' t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := hF
  exact ⟨t', s', ht, hs, hm.mono h⟩

/-- Convert the compatibility one-step view to the relational functor. -/
theorem WeakBisimF.toWeakBisimRelF {R : ITree F α → ITree F α → Prop}
    {t s : ITree F α} (hF : WeakBisimF R t s) : WeakBisimRelF Eq R t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := hF
  exact ⟨t', s', ht, hs, hm.toMatchRel⟩

/-- Convert the equality-specialized relational functor to its compatibility
view. -/
theorem WeakBisimRelF.toWeakBisimF {R : ITree F α → ITree F α → Prop}
    {t s : ITree F α} (hF : WeakBisimRelF Eq R t s) : WeakBisimF R t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := hF
  exact ⟨t', s', ht, hs, hm.toMatch⟩

/-- Weak bisimulation (Coq `eutt`). Two trees are weakly bisimilar iff
there exists a relation `R` containing the pair that is closed under
one-step unfolding into `WeakBisimF`. Equivalently, `WeakBisim` is the
largest such relation (Tarski greatest fixed point). -/
abbrev WeakBisim (t s : ITree F α) : Prop :=
  WeakBisimRel Eq t s

@[inherit_doc] scoped infix:50 " ≈ " => ITree.WeakBisim

namespace WeakBisim

/-- Coinduction principle: any relation closed under `WeakBisimF` is
contained in `WeakBisim`. This is the Tarski greatest fixed point
characterization. -/
theorem coinduct (R : ITree F α → ITree F α → Prop)
    (h : ∀ a b, R a b → WeakBisimF R a b)
    {a b : ITree F α} (hab : R a b) : a ≈ b :=
  WeakBisimRel.coinduct Eq R (fun a b hR => (h a b hR).toWeakBisimRelF) hab

/-- `WeakBisim` is closed under `WeakBisimF`. -/
theorem unfold {t s : ITree F α} (h : t ≈ s) : WeakBisimF WeakBisim t s := by
  exact (WeakBisimRel.unfold h).toWeakBisimF

/-- Extract the stripped-heads match witness. -/
theorem dest {t s : ITree F α} (h : t ≈ s) :
    ∃ t' s' : ITree F α, TauSteps t t' ∧ TauSteps s s' ∧ Match WeakBisim t' s' :=
  unfold h

/-- Folding rule: supplying a `WeakBisimF WeakBisim`-match recovers
`WeakBisim`. -/
theorem fold {t s : ITree F α} (h : WeakBisimF WeakBisim t s) : t ≈ s := by
  obtain ⟨t', s', ht, hs, hm⟩ := h
  refine coinduct (fun a b => a ≈ b ∨
      (a = t ∧ b = s)) ?_ (Or.inr ⟨rfl, rfl⟩)
  rintro a b (hab | ⟨rfl, rfl⟩)
  · exact (unfold hab).mono (fun x y hxy => Or.inl hxy)
  · exact ⟨t', s', ht, hs, hm.mono (fun x y hxy => Or.inl hxy)⟩

end WeakBisim

end ITree
