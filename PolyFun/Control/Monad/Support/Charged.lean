/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Support

/-!
# Charged Monadic Folds

`MonadAttach.chargedRun step charge events state` runs a monadic transition system along a list
of events, as `List.foldlM` does, and also returns the accumulated charge of the events, each
read at the state where it fires. Forgetting the charge recovers the fold
(`map_fst_chargedRun`); under exact support every result of the fold has a charged counterpart
(`canReturn_foldlM_iff_chargedRun`).

The support lemmas bound the charge of every possible result:

* `chargedRun_le` is the potential method: if a potential pays each event's charge out of its
  decrease plus a per-event grant, then the charge of every possible result plus its final
  potential is at most the initial potential plus the grants of the events;
* `le_chargedRun` is the matching lower bound from a per-event lower bound on the charge;
* `chargedRun_const` counts the events under a constant charge.
-/

@[expose] public section

universe u v w

namespace MonadAttach

variable {m : Type u → Type v} [Monad m] {σ : Type u} {E : Type w}

/-- Run a monadic transition system along a list of events, accumulating the charge of each
event read at the state where it fires. -/
def chargedRun (step : E → σ → m σ) (charge : E → σ → ℕ) : List E → σ → m (σ × ℕ)
  | [], s => pure (s, 0)
  | e :: es, s => step e s >>= fun s' =>
      (fun r : σ × ℕ => (r.1, charge e s + r.2)) <$> chargedRun step charge es s'

/-- Forgetting the charge recovers the plain monadic fold. -/
theorem map_fst_chargedRun [LawfulMonad m] (step : E → σ → m σ) (charge : E → σ → ℕ)
    (es : List E) (s : σ) :
    Prod.fst <$> chargedRun step charge es s = es.foldlM (fun s e => step e s) s := by
  induction es generalizing s with
  | nil => simp [chargedRun]
  | cons e es ih =>
    simp only [chargedRun, map_bind, Functor.map_map, List.foldlM_cons]
    exact bind_congr fun s' => ih s'

section Lawful

variable [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]

/-- **The potential method.** If, from every invariant state, each possible step keeps the
invariant and the potential pays the step's charge out of its decrease plus a grant, then every
possible result's charge plus its final potential is at most the initial potential plus the
grants of the events. -/
theorem chargedRun_le {step : E → σ → m σ} {charge : E → σ → ℕ}
    (inv : σ → Prop) (Φ : σ → ℕ) (grant : E → ℕ)
    (hstep : ∀ e s s', inv s → CanReturn (step e s) s' →
      inv s' ∧ Φ s' + charge e s ≤ Φ s + grant e) :
    ∀ (es : List E) (s s' : σ) (w : ℕ), inv s →
      CanReturn (chargedRun step charge es s) (s', w) →
        inv s' ∧ w + Φ s' ≤ Φ s + (es.map grant).sum := by
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

/-- **Lower bound.** If every possible step from an invariant state keeps the invariant and is
charged at least `lb e`, every possible result's charge is at least the sum of the lower
bounds. -/
theorem le_chargedRun {step : E → σ → m σ} {charge : E → σ → ℕ}
    (inv : σ → Prop) (lb : E → ℕ)
    (hstep : ∀ e s s', inv s → CanReturn (step e s) s' → inv s' ∧ lb e ≤ charge e s) :
    ∀ (es : List E) (s s' : σ) (w : ℕ), inv s →
      CanReturn (chargedRun step charge es s) (s', w) → (es.map lb).sum ≤ w := by
  intro es
  induction es with
  | nil => intro _ _ _ _ _; simp
  | cons e es ih =>
    intro s s' w hs h
    obtain ⟨mid, hmid, hrest⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    obtain ⟨⟨fin, w'⟩, hrun, heq⟩ := LawfulMonadAttach.canReturn_map_imp' hrest
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hinv, hlb⟩ := hstep e s mid hs hmid
    have := ih mid fin w' hinv hrun
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Under a constant charge, every possible result's charge counts the events. -/
theorem chargedRun_const {step : E → σ → m σ} (c : ℕ) :
    ∀ (es : List E) (s s' : σ) (w : ℕ),
      CanReturn (chargedRun step (fun _ _ => c) es s) (s', w) → w = c * es.length := by
  intro es
  induction es with
  | nil =>
    intro s s' w h
    have heq := LawfulMonadAttach.eq_of_canReturn_pure h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp
  | cons e es ih =>
    intro s s' w h
    obtain ⟨mid, _, hrest⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    obtain ⟨⟨fin, w'⟩, hrun, heq⟩ := LawfulMonadAttach.canReturn_map_imp' hrest
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [ih mid fin w' hrun, List.length_cons, Nat.mul_succ]
    omega

end Lawful

/-- Under exact support, every result of the plain fold is the state of a charged result. -/
theorem canReturn_foldlM_iff_chargedRun [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    (step : E → σ → m σ) (charge : E → σ → ℕ) (es : List E) (s s' : σ) :
    CanReturn (es.foldlM (fun s e => step e s) s) s' ↔
      ∃ w, CanReturn (chargedRun step charge es s) (s', w) := by
  rw [← map_fst_chargedRun step charge, canReturn_map_iff]
  constructor
  · rintro ⟨⟨t, w⟩, h, rfl⟩
    exact ⟨w, h⟩
  · rintro ⟨w, h⟩
    exact ⟨(s', w), h, rfl⟩

end MonadAttach
