/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support

/-!
# Charged Monadic Folds

`MonadAttach.chargedFoldlM step charge events state` runs a monadic transition system along a
list of events, as `List.foldlM` does, and also returns the accumulated charge of the events, each
read at the state where it fires. Forgetting the charge recovers the fold
(`map_fst_chargedFoldlM`); under exact support every result of the fold has a charged counterpart
(`canReturn_foldlM_iff_chargedFoldlM`).

`chargedFoldlM_induction` proves a property of every possible result by induction along the
events. The support lemmas below are its instances:

* `chargedFoldlM_le` is the potential method: if a potential pays each event's charge out of its
  decrease plus a per-event grant, then the charge of every possible result plus its final
  potential is at most the initial potential plus the grants of the events;
* `le_chargedFoldlM` is the matching lower bound from a per-event lower bound on the charge;
* `chargedFoldlM_const` counts the events under a constant charge;
* `chargedFoldlM_ledger` bounds the charge by the growth of a ledger that records at least each
  event's charge, and `chargedFoldlM_bounded` bounds the growth of a quantity that rises by at most
  a grant per event.

This is the support-level reading of a charge: it bounds what an interpretation can actually
return. `OpSpec.charge` in `PolyFun/PFunctor/Free/WP/Charge.lean` instead reads a charge off the
syntax of a free program, as the worst case over every branch.
-/

@[expose] public section

universe u v w

namespace MonadAttach

variable {m : Type u → Type v} [Monad m] {σ : Type u} {E : Type w}

/-- Run a monadic transition system along a list of events, accumulating the charge of each
event read at the state where it fires. -/
def chargedFoldlM (step : E → σ → m σ) (charge : E → σ → ℕ) : List E → σ → m (σ × ℕ)
  | [], s => pure (s, 0)
  | e :: es, s => step e s >>= fun s' =>
      (fun r : σ × ℕ => (r.1, charge e s + r.2)) <$> chargedFoldlM step charge es s'

/-- Forgetting the charge recovers the plain monadic fold. -/
theorem map_fst_chargedFoldlM [LawfulMonad m] (step : E → σ → m σ) (charge : E → σ → ℕ)
    (es : List E) (s : σ) :
    Prod.fst <$> chargedFoldlM step charge es s = es.foldlM (fun s e => step e s) s := by
  induction es generalizing s with
  | nil => simp [chargedFoldlM]
  | cons e es ih =>
    simp only [chargedFoldlM, map_bind, Functor.map_map, List.foldlM_cons]
    exact bind_congr fun s' => ih s'

section Lawful

variable [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]

/-- **Induction over possible results.** A property of the empty run that is preserved by
prepending one possible step holds of every possible result of a charged fold. -/
theorem chargedFoldlM_induction {step : E → σ → m σ} {charge : E → σ → ℕ}
    (motive : List E → σ → σ → ℕ → Prop)
    (nil : ∀ s, motive [] s s 0)
    (cons : ∀ e es s mid fin w, CanReturn (step e s) mid → motive es mid fin w →
      motive (e :: es) s fin (charge e s + w)) :
    ∀ (es : List E) (s fin : σ) (w : ℕ),
      CanReturn (chargedFoldlM step charge es s) (fin, w) → motive es s fin w := by
  intro es
  induction es with
  | nil =>
    intro s fin w h
    have heq := LawfulMonadAttach.eq_of_canReturn_pure h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact nil _
  | cons e es ih =>
    intro s fin w h
    obtain ⟨mid, hmid, hrest⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    obtain ⟨⟨fin', w'⟩, hrun, heq⟩ := LawfulMonadAttach.canReturn_map_imp' hrest
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact cons e es s mid _ _ hmid (ih mid _ _ hrun)

/-- **The potential method.** If, from every invariant state, each possible step keeps the
invariant and the potential pays the step's charge out of its decrease plus a grant, then every
possible result's charge plus its final potential is at most the initial potential plus the
grants of the events. -/
theorem chargedFoldlM_le {step : E → σ → m σ} {charge : E → σ → ℕ}
    (inv : σ → Prop) (Φ : σ → ℕ) (grant : E → ℕ)
    (hstep : ∀ e s s', inv s → CanReturn (step e s) s' →
      inv s' ∧ Φ s' + charge e s ≤ Φ s + grant e) :
    ∀ (es : List E) (s s' : σ) (w : ℕ), inv s →
      CanReturn (chargedFoldlM step charge es s) (s', w) →
        inv s' ∧ w + Φ s' ≤ Φ s + (es.map grant).sum := by
  intro es s s' w hs h
  refine chargedFoldlM_induction
    (motive := fun es s s' w => inv s → inv s' ∧ w + Φ s' ≤ Φ s + (es.map grant).sum)
    (fun _ hs => by simpa using hs) (fun e es s mid fin w hmid ih hs => ?_) es s s' w h hs
  obtain ⟨hinv, hpay⟩ := hstep e s mid hs hmid
  obtain ⟨hfin, hrec⟩ := ih hinv
  refine ⟨hfin, ?_⟩
  simp only [List.map_cons, List.sum_cons]
  omega

/-- **Lower bound.** If every possible step from an invariant state keeps the invariant and is
charged at least `lb e`, every possible result's charge is at least the sum of the lower
bounds. -/
theorem le_chargedFoldlM {step : E → σ → m σ} {charge : E → σ → ℕ}
    (inv : σ → Prop) (lb : E → ℕ)
    (hstep : ∀ e s s', inv s → CanReturn (step e s) s' → inv s' ∧ lb e ≤ charge e s) :
    ∀ (es : List E) (s s' : σ) (w : ℕ), inv s →
      CanReturn (chargedFoldlM step charge es s) (s', w) → (es.map lb).sum ≤ w := by
  intro es s s' w hs h
  refine chargedFoldlM_induction (motive := fun es s _ w => inv s → (es.map lb).sum ≤ w)
    (fun _ _ => by simp) (fun e es s mid fin w hmid ih hs => ?_) es s s' w h hs
  obtain ⟨hinv, hlb⟩ := hstep e s mid hs hmid
  have := ih hinv
  simp only [List.map_cons, List.sum_cons]
  omega

/-- Under a constant charge, every possible result's charge counts the events. -/
theorem chargedFoldlM_const {step : E → σ → m σ} (c : ℕ) :
    ∀ (es : List E) (s s' : σ) (w : ℕ),
      CanReturn (chargedFoldlM step (fun _ _ => c) es s) (s', w) → w = c * es.length :=
  chargedFoldlM_induction (motive := fun es _ _ w => w = c * es.length) (fun _ => by simp)
    fun _ _ _ _ _ _ _ ih => by
      rw [ih, List.length_cons, Nat.mul_succ]
      omega

/-- **Ledger bound.** If every possible step from an invariant state keeps the invariant and a
ledger grows by at least the step's charge, every possible result's charge is at most the ledger's
growth. -/
theorem chargedFoldlM_ledger {step : E → σ → m σ} {charge : E → σ → ℕ}
    (inv : σ → Prop) (Ψ : σ → ℕ)
    (hstep : ∀ e s s', inv s → CanReturn (step e s) s' → inv s' ∧ Ψ s + charge e s ≤ Ψ s') :
    ∀ (es : List E) (s s' : σ) (w : ℕ), inv s →
      CanReturn (chargedFoldlM step charge es s) (s', w) → inv s' ∧ w + Ψ s ≤ Ψ s' := by
  intro es
  induction es with
  | nil =>
    intro s s' w hs h
    have heq := LawfulMonadAttach.eq_of_canReturn_pure h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simpa using hs
  | cons e es ih =>
    intro s s' w hs h
    obtain ⟨mid, hmid, hrest⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    obtain ⟨⟨fin, w'⟩, hrun, heq⟩ := LawfulMonadAttach.canReturn_map_imp' hrest
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hinv, hpay⟩ := hstep e s mid hs hmid
    obtain ⟨hfin, hrec⟩ := ih mid fin w' hinv hrun
    exact ⟨hfin, by omega⟩

/-- **Growth bound.** If every possible step from an invariant state keeps the invariant and a
quantity rises by at most a grant, every possible result's final quantity is at most the initial
one plus the grants of the events. -/
theorem chargedFoldlM_bounded {step : E → σ → m σ} {charge : E → σ → ℕ}
    (inv : σ → Prop) (Φ : σ → ℕ) (grant : E → ℕ)
    (hstep : ∀ e s s', inv s → CanReturn (step e s) s' → inv s' ∧ Φ s' ≤ Φ s + grant e) :
    ∀ (es : List E) (s s' : σ) (w : ℕ), inv s →
      CanReturn (chargedFoldlM step charge es s) (s', w) →
        inv s' ∧ Φ s' ≤ Φ s + (es.map grant).sum := by
  intro es
  induction es with
  | nil =>
    intro s s' w hs h
    have heq := LawfulMonadAttach.eq_of_canReturn_pure h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simpa using hs
  | cons e es ih =>
    intro s s' w hs h
    obtain ⟨mid, hmid, hrest⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    obtain ⟨⟨fin, w'⟩, hrun, heq⟩ := LawfulMonadAttach.canReturn_map_imp' hrest
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hinv, hpay⟩ := hstep e s mid hs hmid
    obtain ⟨hfin, hrec⟩ := ih mid fin w' hinv hrun
    refine ⟨hfin, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    omega

end Lawful

/-- Under exact support, every result of the plain fold is the state of a charged result. -/
theorem canReturn_foldlM_iff_chargedFoldlM [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    (step : E → σ → m σ) (charge : E → σ → ℕ) (es : List E) (s s' : σ) :
    CanReturn (es.foldlM (fun s e => step e s) s) s' ↔
      ∃ w, CanReturn (chargedFoldlM step charge es s) (s', w) := by
  rw [← map_fst_chargedFoldlM step charge, canReturn_map_iff]
  constructor
  · rintro ⟨⟨t, w⟩, h, rfl⟩
    exact ⟨w, h⟩
  · rintro ⟨w, h⟩
    exact ⟨(s', w), h, rfl⟩

end MonadAttach
