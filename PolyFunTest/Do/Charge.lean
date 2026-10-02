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
  program by twice its budget.
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

end PFunctor.ChargeTest
