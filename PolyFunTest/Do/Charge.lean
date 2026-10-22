/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.WP.Charge
public import PolyFun.PFunctor.Free.Do

/-!
# Charges, budgets and upper-bound triples on free programs

Checks for `PolyFun.PFunctor.Free.WP.Charge` and `Spec.lift_upper` on a coin interface:

* two flips have unit-charge fold `2`, so they have total roll bound `2` and not `1`;
* implementing each flip by two flips at most doubles the charge (`wpFold_charge_liftM_le`);
* under the upper-bound reading of the unit charge, `vcgen` decomposes the first flip and the
  remaining condition closes on the fold;
* the ranked triple, read in that same upper-bound reading, bounds the charge of a simulated
  program by twice its budget;
* over a counting `StateT` handler, `triple_liftM_invariant` carries the parity of the counter
  through every simulated program, and `triple_liftM_of_isRollBound` bounds the counter by a budget
  that charges only the metered operation, alone or paired with a total bound by
  `IsRollBound.prod`.
-/

public section

open Std.WP OrderDual

set_option experimental.vcgen true

namespace PFunctor.ChargeTest

/-- A coin interface: one operation with Boolean answers. -/
abbrev Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- Two coin flips. -/
def twoFlips : FreeM Coin Bool := do
  let b ← FreeM.lift (P := Coin) ()
  let c ← FreeM.lift (P := Coin) ()
  pure (b && c)

/-- Two flips cost two units. -/
theorem wpFold_twoFlips :
    FreeM.wpFold (OpSpec.charge fun _ => (1 : ℕ∞)) twoFlips (fun _ => 0) = 2 := by
  simp [twoFlips, FreeM.wpFold_bind, one_add_one_eq_two]

example : FreeM.IsTotalRollBound twoFlips 2 :=
  (FreeM.isTotalRollBound_iff_wpFold_charge twoFlips 2).2 (by rw [wpFold_twoFlips]; rfl)

example : ¬ FreeM.IsTotalRollBound twoFlips 1 := by
  rw [FreeM.isTotalRollBound_iff_wpFold_charge, wpFold_twoFlips]
  decide

/-- Each flip is implemented by two flips, keeping the second. -/
def doubled : (a : Coin.A) → FreeM Coin (Coin.B a) := fun _ => do
  let _ ← FreeM.lift (P := Coin) ()
  FreeM.lift (P := Coin) ()

/-- The doubled handler costs two units per call. -/
theorem handlerCost_doubled (a : Coin.A) :
    FreeM.handlerCost (fun _ => (1 : ℕ∞)) doubled a = 2 := by
  simp [FreeM.handlerCost, doubled, FreeM.wpFold_bind, one_add_one_eq_two]

example :
    FreeM.wpFold (OpSpec.charge fun _ => (1 : ℕ∞)) (twoFlips.liftM doubled) (fun _ => 0) ≤ 4 := by
  refine (FreeM.wpFold_charge_liftM_le _ doubled twoFlips).trans ?_
  simp only [selfMonomial_A, twoFlips, selfMonomial_B, bind_pure_comp, FreeM.wpFold_bind,
    FreeM.wpFold_map, FreeM.wpFold_lift, OpSpec.charge_apply, handlerCost_doubled, ciSup_const,
    add_zero]
  decide

/-- The upper-bound reading of the unit charge on coin programs. -/
noncomputable abbrev coinCost : WPMonad (FreeM Coin) ℕ∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  (OpSpec.charge (P := Coin) fun _ => (1 : ℕ∞)).toUpperWPMonad (OpSpec.charge_mono _)

attribute [local instance] coinCost

/- `vcgen` decomposes the first flip by `Spec.lift_upper`; the second stays under the supremum, and
the remaining condition closes on the fold. -/
example : ⦃ toDual (2 : ℕ∞) ⦄ twoFlips ⦃ fun (_ : Bool) => toDual (0 : ℕ∞) ⦄ := by
  unfold twoFlips
  vcgen
  simp only [binderNameHint, Lean.Order.rel_eq_le, toDual_le_toDual,
    ExactWPMonad.wp_bind, ExactWPMonad.wp_pure]
  rw [OpSpec.toUpperWPMonad_wp]
  simp [one_add_one_eq_two]

/- Ranked simulation in the upper-bound reading: a program with total roll bound `k`, simulated
through the doubled handler, has charge at most `2 * k`. -/
example (x : FreeM Coin Bool) (k : ℕ) (hx : FreeM.IsTotalRollBound x k) :
    ⦃ toDual ((2 * k : ℕ) : ℕ∞) ⦄ (x.liftM doubled) ⦃ fun _ => toDual (0 : ℕ∞) ⦄ := by
  refine FreeM.triple_liftM_ranked_total doubled (fun j => toDual ((2 * j : ℕ) : ℕ∞)) _ ?_ ?_ x k
    hx
  · intro a j
    refine ⟨?_⟩
    rw [OpSpec.toUpperWPMonad_wp]
    simp only [Lean.Order.rel_eq_le, toDual_le_toDual, ofDual_toDual, doubled,
      FreeM.wpFold_bind, FreeM.wpFold_lift, OpSpec.charge_apply, iSup_const]
    exact_mod_cast (by omega : 1 + (1 + 2 * j) ≤ 2 * (j + 1))
  · intro j
    simp only [Lean.Order.rel_eq_le, toDual_le_toDual]
    exact_mod_cast (by omega : 2 * 0 ≤ 2 * j)

/-! ## Handlers with state -/

/-- Each flip advances a counter by two and answers `true`. -/
def countTwice : (a : Coin.A) → StateT ℕ Id (Coin.B a) := fun _ => do
  modify (· + 2)
  pure true

/- The parity of the counter is an invariant of every simulated coin program. -/
example (x : FreeM Coin Bool) :
    ⦃ fun s => Even s ⦄ (x.liftM countTwice) ⦃ fun _ s => Even s ⦄ :=
  FreeM.triple_liftM_invariant countTwice (fun s => Even s) _
    (fun _ => by
      vcgen [countTwice]
      grind)
    x

/-- An interface with a metered and an unmetered operation, both answering `Bool`. -/
abbrev Metered : PFunctor.{0, 0} := ⟨Bool, fun _ => Bool⟩

/-- A budget that admits an unmetered call at every budget and charges a metered call one unit. -/
abbrev MeteredBound (x : FreeM Metered Bool) (k : ℕ) : Prop :=
  FreeM.IsRollBound x k (fun a b => a = true → 0 < b) (fun a b => if a then b - 1 else b)

/-- The handler counts the metered calls only. -/
def countMetered : (a : Metered.A) → StateT ℕ Id (Metered.B a) := fun a => do
  if a then modify (· + 1)
  pure a

/-- The metered calls of a program within budget `k` advance the counter by at most `k`. -/
theorem countMetered_le (x : FreeM Metered Bool) (k : ℕ) (hx : MeteredBound x k) :
    ⦃ fun s => s + k ≤ k ⦄ (x.liftM countMetered) ⦃ fun _ s => s ≤ k ⦄ := by
  refine FreeM.triple_liftM_of_isRollBound countMetered (fun b s => s + b ≤ k) (fun s => s ≤ k)
    _ (fun a b hb => ?_) (fun b s hs => by omega) x k hx
  cases a
  · vcgen [countMetered]
    all_goals simp_all
  · vcgen [countMetered]
    all_goals simp_all
    omega

/- Started at `0`, the counter ends at most the budget. -/
example (x : FreeM Metered Bool) (k : ℕ) (hx : MeteredBound x k) :
    ⦃ fun s => s = 0 ⦄ (x.liftM countMetered) ⦃ fun _ s => s ≤ k ⦄ :=
  ⟨Triple.entails_wp_of_pre (countMetered_le x k hx) fun s hs => by simp [hs]⟩

/- The metered budget paired with a total bound is a product budget, and the ranked triple
over it reads only the metered component. -/
example (x : FreeM Metered Bool) (k n : ℕ) (hx : MeteredBound x k)
    (hn : FreeM.IsTotalRollBound x n) :
    ⦃ fun s => s + k ≤ k ⦄ (x.liftM countMetered) ⦃ fun _ s => s ≤ k ⦄ := by
  refine FreeM.triple_liftM_of_isRollBound countMetered (fun p s => s + p.1 ≤ k)
    (fun s => s ≤ k) _ (fun a p hp => ?_) (fun p s hs => by omega) x (k, n) (hx.prod hn)
  cases a
  · vcgen [countMetered]
    all_goals simp_all
  · vcgen [countMetered]
    all_goals simp_all
    omega

end PFunctor.ChargeTest
