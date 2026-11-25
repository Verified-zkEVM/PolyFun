/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.WP.Charge

/-!
# Charge folds over allowed answers

Boundary cases for the fold rules of `OpSpec.chargeUnder`:

* a call whose answers are all excluded charges only itself, so ignoring the answer is not enough
  for the continuation to be charged;
* the budget of a call is exact at a nonzero postcondition, and a bind charges its continuation
  only at the results the first program can return;
* the priced fold can be strictly below the priced vector fold, when the branches use different
  resources.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargeUnder

abbrev Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A second flip after tails only. -/
@[expose] def again : FreeM Coin Bool :=
  FreeM.liftBind () fun b => if b then FreeM.pure b else FreeM.liftBind () FreeM.pure

/-! ## Calls -/

/-- With no answer allowed, a call that ignores its answer charges itself and not its
continuation. -/
example : wpFold (OpSpec.chargeUnder (fun _ => (1 : ℕ∞)) fun _ _ => False)
    (FreeM.liftBind (P := Coin) () fun _ => again) (fun _ => 0) = 1 := by
  rw [wpFold_liftBind, OpSpec.chargeUnder_apply]
  simp

/-- With heads allowed, the same call charges its continuation too. -/
example : wpFold (OpSpec.chargeUnder (fun _ => (1 : ℕ∞)) fun _ b => b = true)
    (FreeM.liftBind (P := Coin) () fun _ => again) (fun _ => 5) =
      1 + wpFold (OpSpec.chargeUnder (fun _ => (1 : ℕ∞)) fun _ b => b = true) again
        (fun _ => 5) :=
  wpFold_chargeUnder_liftBind_const (P := Coin) (fun _ => (1 : ℕ∞)) (fun _ b => b = true) ()
    (b := true) rfl again _

/-- Over heads, one flip and a postcondition of five cost exactly six. -/
example (n : ℕ) : wpFold (OpSpec.chargeUnder (fun _ => ((1 : ℕ) : ℕ∞)) fun _ b => b = true)
    again (fun _ => 5) ≤ n ↔ 6 ≤ n := by
  rw [again, wpFold_chargeUnder_liftBind_le_iff (fun _ => 1)]
  simp only [forall_eq]
  change 1 ≤ n ∧ (5 : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) ↔ 6 ≤ n
  rw [Nat.ofNat_le_cast]
  omega

/-- Over all answers the second flip counts, and the same program costs exactly seven. -/
example (n : ℕ) : wpFold (OpSpec.chargeUnder (fun _ => ((1 : ℕ) : ℕ∞)) fun _ _ => True)
    again (fun _ => 5) ≤ n ↔ 7 ≤ n := by
  rw [again, wpFold_chargeUnder_liftBind_le_iff (fun _ => 1)]
  simp only [forall_const, Bool.forall_bool, Bool.false_eq_true, reduceIte]
  rw [wpFold_chargeUnder_liftBind_le_iff (fun _ => 1)]
  change 1 ≤ n ∧ (1 ≤ n - 1 ∧ ∀ b : Bool, True → (5 : ℕ∞) ≤ ((n - 1 - 1 : ℕ) : ℕ∞)) ∧
    (5 : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) ↔ 7 ≤ n
  simp only [forall_const, Nat.ofNat_le_cast]
  omega

/-! ## Sequencing -/

/-- Over heads, the continuation is charged only at heads: the branch after tails may cost more
than the bound. -/
example : wpFold (OpSpec.chargeUnder (fun _ => ((1 : ℕ) : ℕ∞)) fun _ b => b = true)
    ((FreeM.lift (P := Coin) ()).bind fun b =>
      if b then FreeM.pure b else (FreeM.lift (P := Coin) ()).bind fun _ => FreeM.lift ())
    (fun _ => 5) ≤ ((1 + 5 : ℕ) : ℕ∞) := by
  refine wpFold_chargeUnder_bind_le_add (P := Coin) (fun _ => 1) (fun _ b => b = true) _ _
    (· = true) 1 5 ?_ ?_ fun _ hb => hb
  · exact wpFold_chargeUnder_liftBind_le (P := Coin) (fun _ => 1) (fun _ b => b = true) ()
      FreeM.pure 1 0 le_rfl fun _ _ => le_rfl
  · rintro _ rfl
    exact le_rfl

/-! ## Prices -/

/-- A free choice of one of two resources, and one call to it. -/
abbrev Choose : PFunctor.{0, 0} := ⟨Option Bool, fun _ => Bool⟩

@[expose] def useOne : FreeM Choose Bool :=
  FreeM.liftBind none fun b => FreeM.liftBind (some b) FreeM.pure

@[expose] def count (a : Option Bool) (i : Bool) : ℕ∞ := if a = some i then 1 else 0

/-- Each branch uses one resource, so at unit prices the program costs one. -/
theorem useOne_priced :
    wpFold (OpSpec.chargeUnder (fun a => ∑ i, 1 * count a i) fun _ _ => True) useOne
      (fun _ => 0) = 1 := by
  change (∑ i, 1 * count none i) + ⨆ b, ⨆ (_ : True), ((∑ i, 1 * count (some b) i) +
    ⨆ _ : Bool, ⨆ (_ : True), (0 : ℕ∞)) = 1
  simp [count, iSup_bool_eq]

/-- The worst case over both resources is one of each, and its price is two. -/
theorem useOne_vector :
    ∑ i, 1 * wpFold (OpSpec.chargeUnder count fun _ _ => True) useOne (fun _ _ => 0) i = 2 := by
  simp only [wpFold_chargeUnder_pi_apply]
  change ∑ i, 1 * (count none i + ⨆ b, ⨆ (_ : True), (count (some b) i +
    ⨆ _ : Bool, ⨆ (_ : True), (0 : ℕ∞))) = 2
  simp [count, iSup_bool_eq, one_add_one_eq_two]

/-- The priced fold is strictly below the priced vector fold. -/
example : wpFold (OpSpec.chargeUnder (fun a => ∑ i, 1 * count a i) fun _ _ => True) useOne
      (fun _ => 0) <
    ∑ i, 1 * wpFold (OpSpec.chargeUnder count fun _ _ => True) useOne (fun _ _ => 0) i := by
  rw [useOne_priced, useOne_vector]
  exact_mod_cast (one_lt_two : (1 : ℕ) < 2)

/-! ## Universes -/

/-- The result universe of a call is independent of the interface's. -/
example {P : PFunctor.{1, 2}} {α : Type 3} (c : P.A → ℕ) (allows : (a : P.A) → P.B a → Prop)
    (a : P.A) (r : P.B a → FreeM P α) (n : ℕ) {post : α → ℕ∞} :
    wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (FreeM.liftBind a r) post ≤ n ↔
      c a ≤ n ∧ ∀ b, allows a b →
        wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (r b) post ≤
          ((n - c a : ℕ) : ℕ∞) :=
  wpFold_chargeUnder_liftBind_le_iff c allows a r n

/-- The two results of a bind live in independent universes. -/
example {P : PFunctor.{1, 2}} {X : Type 3} {Y : Type 4} (c : P.A → ℕ)
    (allows : (a : P.A) → P.B a → Prop) (x : FreeM P X) (f : X → FreeM P Y) (m n : ℕ)
    (hx : wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) x (fun _ => 0) ≤ (m : ℕ∞))
    (hf : ∀ a, wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (f a) (fun _ => 0) ≤
      (n : ℕ∞)) (hI : wpFold (OpSpec.demonicUnder allows) x fun _ => True) :
    wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (x.bind f) (fun _ => 0) ≤
      ((m + n : ℕ) : ℕ∞) :=
  wpFold_chargeUnder_bind_le_add c allows x f _ m n hx (fun a _ => hf a) hI

end PolyFunTest.ChargeUnder
