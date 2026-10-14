/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.WP.Upstream
public import PolyFun.PFunctor.Bound
public import Mathlib.Data.ENat.Lattice

/-!
# Charges: worst-case cost as a weakest-precondition fold

`OpSpec.charge c` reads a call at `a` as costing `c a`, followed by its worst continuation:
`c a + ⨆ b, k b`. Its fold `wpFold (OpSpec.charge c) x post` is the worst-case charge-to-go of
`x`, where `post` gives the cost of each leaf.

* `isRollBound_iff_wpFold_charge`: subtractive per-position budgets
  (`IsRollBound x n (fun a b => c a ≤ b) (fun a b => b - c a)`) are exactly upper bounds on the
  charge fold in `ℕ∞`, with no progress condition. `isTotalRollBound_iff_wpFold_charge` is the
  unit-charge case.
* `wpFold_charge_liftM_le`: a program simulated through a handler costs at most the program with
  each call charged its handler's worst case (`handlerCost`). This is `wpFold_liftM` for the
  charge reading, with `wpFold_charge_le` splitting off the continuation.
* `triple_liftM_ranked`: the same budget as a core triple. If every call at `a` turns a
  rank-`(k + c a)` precondition into a rank-`k` one, then any program within budget `k` maps rank
  `k` to rank `0`. The budget sits in the precondition rather than under a supremum, which is the
  shape `vcgen` decomposes call by call; with a rank family carrying a bad-event indicator plus
  the remaining budget, it is the union bound over the calls.

Under the upper-bound reading `(OpSpec.charge c).toUpperWPMonad (OpSpec.charge_mono c)`, a triple
`⦃ toDual t ⦄ x ⦃ post ⦄` states that the charge-to-go of `x` is at most `t`.
`PolyFun.PFunctor.Free.Do` registers the operation rule `Spec.lift_upper`. It decomposes one call:
the continuation stays under the supremum, and rewriting with `OpSpec.toUpperWPMonad_wp` returns
the remaining condition to the fold.
-/

@[expose] public section

universe uA uB uA₂ v w z

open Std.WP

namespace PFunctor

namespace OpSpec

variable {P : PFunctor.{uA, uB}}

/-- The worst-case charge reading: a call at `a` costs `c a`, followed by the worst
continuation. -/
noncomputable def charge {R : Type w} [CompleteLattice R] [Add R] (c : P.A → R) : OpSpec P R :=
  fun a k => c a + ⨆ b, k b

@[simp]
theorem charge_apply {R : Type w} [CompleteLattice R] [Add R] (c : P.A → R) (a : P.A)
    (k : P.B a → R) :
    charge c a k = c a + ⨆ b, k b :=
  rfl

/-- The charge reading is monotone whenever addition is. -/
theorem charge_mono {R : Type w} [CompleteLattice R] [Add R] [AddLeftMono R] (c : P.A → R) :
    (charge c).Mono := by
  intro a k k' hk
  change c a + ⨆ b, k b ≤ c a + ⨆ b, k' b
  gcongr with b
  exact hk b

end OpSpec

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type uB}

/-! ## Budgets are charge bounds -/

/-- Subtractive per-position budgets are exactly upper bounds on the worst-case charge fold. -/
theorem isRollBound_iff_wpFold_charge (c : P.A → ℕ) (x : FreeM P α) (n : ℕ) :
    IsRollBound x n (fun a b => c a ≤ b) (fun a b => b - c a) ↔
      wpFold (OpSpec.charge fun a => (c a : ℕ∞)) x (fun _ => 0) ≤ n := by
  induction x generalizing n with
  | pure x => exact iff_of_true trivial (by simp)
  | lift_bind a r ih =>
    rw [isRollBound_lift_bind_iff]
    change _ ↔ ((c a : ℕ∞) + ⨆ b, wpFold _ (r b) fun _ => 0) ≤ (n : ℕ∞)
    constructor
    · rintro ⟨hc, hr⟩
      have hsup : (⨆ b, wpFold (OpSpec.charge fun a => (c a : ℕ∞)) (r b) fun _ => 0) ≤
          ((n - c a : ℕ) : ℕ∞) := iSup_le fun b => (ih b (n - c a)).1 (hr b)
      calc (c a : ℕ∞) + ⨆ b, wpFold _ (r b) (fun _ => 0)
          ≤ (c a : ℕ∞) + ((n - c a : ℕ) : ℕ∞) := by gcongr
        _ = n := by rw [← Nat.cast_add, Nat.add_sub_cancel' hc]
    · intro h
      have hc : c a ≤ n := by
        have : (c a : ℕ∞) ≤ n := le_trans le_self_add h
        exact_mod_cast this
      refine ⟨hc, fun b => (ih b (n - c a)).2 ?_⟩
      have hb : wpFold (OpSpec.charge fun a => (c a : ℕ∞)) (r b) (fun _ => 0) ≤
          ⨆ b, wpFold (OpSpec.charge fun a => (c a : ℕ∞)) (r b) fun _ => 0 :=
        le_iSup (fun b => wpFold (OpSpec.charge fun a => (c a : ℕ∞)) (r b) fun _ => 0) b
      have h' : (c a : ℕ∞) + wpFold (OpSpec.charge fun a => (c a : ℕ∞)) (r b) (fun _ => 0) ≤
          (c a : ℕ∞) + ((n - c a : ℕ) : ℕ∞) := by
        rw [← Nat.cast_add, Nat.add_sub_cancel' hc]
        exact le_trans (by gcongr) h
      exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).1 h'

/-- Total roll bounds are unit-charge bounds. -/
theorem isTotalRollBound_iff_wpFold_charge (x : FreeM P α) (n : ℕ) :
    IsTotalRollBound x n ↔ wpFold (OpSpec.charge fun _ => (1 : ℕ∞)) x (fun _ => 0) ≤ n := by
  have := isRollBound_iff_wpFold_charge (fun _ => 1) x n
  simpa [IsTotalRollBound, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using this

/-! ## Simulation overhead -/

/-- The charge fold splits off the continuation: the charge-to-go is at most the program's own
charge plus the worst continuation value. -/
theorem wpFold_charge_le {Q : PFunctor.{uA₂, uB}} (c : Q.A → ℕ∞) {β : Type uB} (y : FreeM Q β)
    (k : β → ℕ∞) :
    wpFold (OpSpec.charge c) y k ≤ wpFold (OpSpec.charge c) y (fun _ => 0) + ⨆ b, k b := by
  induction y with
  | pure b => simpa using le_iSup k b
  | lift_bind a r ih =>
    change c a + (⨆ u, wpFold _ (r u) k) ≤ (c a + ⨆ u, wpFold _ (r u) fun _ => 0) + ⨆ b, k b
    rw [add_assoc]
    gcongr
    refine iSup_le fun u => (ih u).trans ?_
    gcongr
    exact le_iSup (fun u => wpFold (OpSpec.charge c) (r u) fun _ => 0) u

/-- The worst-case charge of a handler's implementation of the call at `a`. -/
noncomputable def handlerCost {Q : PFunctor.{uA₂, uB}} (c : Q.A → ℕ∞)
    (handler : (a : P.A) → FreeM Q (P.B a)) (a : P.A) : ℕ∞ :=
  wpFold (OpSpec.charge c) (handler a) fun _ => 0

/-- **Simulation overhead.** A program simulated through a handler costs at most the program with
each call at `a` charged the handler's worst-case cost at `a`. -/
theorem wpFold_charge_liftM_le {Q : PFunctor.{uA₂, uB}} (c : Q.A → ℕ∞)
    (handler : (a : P.A) → FreeM Q (P.B a)) (x : FreeM P α) :
    wpFold (OpSpec.charge c) (x.liftM handler) (fun _ => 0) ≤
      wpFold (OpSpec.charge (handlerCost c handler)) x (fun _ => 0) := by
  rw [wpFold_liftM]
  induction x with
  | pure x => exact le_rfl
  | lift_bind a r ih =>
    change wpFold (OpSpec.charge c) (handler a) (fun u => wpFold _ (r u) _) ≤
      handlerCost c handler a + ⨆ u, wpFold _ (r u) _
    exact (wpFold_charge_le c (handler a) _).trans (add_le_add (le_refl _) (iSup_mono ih))

/-! ## Ranked simulation triples -/

section Ranked

variable {n : Type uB → Type w} [Monad n] {Pred : Type v} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]

/-- **Ranked simulation.** If every call at `a` consumes `c a` units of rank, then a program
within budget `k` maps rank `k` to rank `0`, after dropping unspent rank. -/
theorem triple_liftM_ranked (handler : (a : P.A) → n (P.B a)) (c : P.A → ℕ)
    (Φ : ℕ → Pred) (E : EPred)
    (hstep : ∀ a k, Triple (handler a) (Φ (k + c a)) (fun _ => Φ k) E)
    (hdrop : ∀ k, Lean.Order.PartialOrder.rel (Φ k) (Φ 0))
    (x : FreeM P α) (k : ℕ)
    (hx : IsRollBound x k (fun a b => c a ≤ b) (fun a b => b - c a)) :
    Triple (x.liftM handler) (Φ k) (fun _ => Φ 0) E := by
  induction x generalizing k with
  | pure x => exact Triple.pure x (hdrop k)
  | lift_bind a r ih =>
    rw [isRollBound_lift_bind_iff] at hx
    obtain ⟨hc, hr⟩ := hx
    obtain ⟨j, rfl⟩ : ∃ j, k = j + c a := ⟨k - c a, (Nat.sub_add_cancel hc).symm⟩
    change Triple (handler a >>= fun u => (r u).liftM handler) _ _ E
    exact Triple.bind _ _ _ (hstep a j) fun u => ih u j (by simpa using hr u)

/-- Ranked simulation with unit charges, under a total roll bound. -/
theorem triple_liftM_ranked_total (handler : (a : P.A) → n (P.B a)) (Φ : ℕ → Pred) (E : EPred)
    (hstep : ∀ a k, Triple (handler a) (Φ (k + 1)) (fun _ => Φ k) E)
    (hdrop : ∀ k, Lean.Order.PartialOrder.rel (Φ k) (Φ 0))
    (x : FreeM P α) (k : ℕ) (hx : IsTotalRollBound x k) :
    Triple (x.liftM handler) (Φ k) (fun _ => Φ 0) E := by
  refine triple_liftM_ranked handler (fun _ => 1) Φ E hstep hdrop x k ?_
  simpa [IsTotalRollBound, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using hx

end Ranked

end FreeM

end PFunctor
