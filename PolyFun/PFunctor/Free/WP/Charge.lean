/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.WP.Upstream
public import PolyFun.PFunctor.Free.Cost.Value
public import Mathlib.Data.ENat.Lattice

/-!
# Charges: worst-case cost as a weakest-precondition fold

`OpSpec.charge c` (`PolyFun.PFunctor.Free.Cost.Value`) reads a call at `a` as costing `c a`,
followed by its worst continuation: `c a + ⨆ b, k b`. Its fold `wpFold (OpSpec.charge c) x post`
is the worst-case charge-to-go of `x` (`FreeM.costWith`), where `post` gives the cost of each
leaf. This module states its `ℕ∞` laws in fold form and connects roll budgets to core triples.

* `isRollBound_iff_wpFold_charge`: subtractive per-position budgets
  (`IsRollBound x n (fun a b => c a ≤ b) (fun a b => b - c a)`) are exactly upper bounds on the
  charge fold in `ℕ∞`, with no progress condition. `isTotalRollBound_iff_wpFold_charge` is the
  unit-charge case.
* `wpFold_charge_liftM_le`: a program simulated through a handler costs at most the program with
  each call charged its handler's worst case (`handlerCost`). This is `wpFold_liftM` for the
  charge reading, with `wpFold_charge_le` splitting off the continuation.
* `triple_liftM_of_isRollBound`: a roll budget as a core triple. If a call at `a` admitted at
  budget `b` turns rank `Φ b` into rank `Φ (cost a b)`, then any program within budget `b` maps
  rank `Φ b` to the final assertion. The budget sits in the precondition rather than under a
  supremum, which is the shape `vcgen` decomposes call by call; with a rank family carrying a
  bad-event indicator plus the remaining budget, it is the union bound over the calls.
  `triple_liftM_ranked` is the subtractive natural-number budget (a call at `a` consumes `c a`)
  and `triple_liftM_ranked_total` the unit-charge one.
* `triple_liftM_of_isChargeBound`: the same over a charge bound in any cost type, with ranks
  indexed by the amount spent.
* `triple_liftM_invariant`: the unranked case, in which every call preserves one assertion.
* `wpFold_chargeUnder_liftBind_le_iff`, `wpFold_chargeUnder_liftBind_const`,
  `wpFold_chargeUnder_liftBind_const_add`: the fold of `OpSpec.chargeUnder c allows` at a call,
  at a general postcondition; `isRollBound_iff_wpFold_chargeUnder_true` is the case of every
  answer allowed.
* `wpFold_chargeUnder_pure_le`, `wpFold_chargeUnder_liftBind_le`,
  `wpFold_chargeUnder_bind_le_add`, `wpFold_ite_le_max_enat`, `wpFold_dite_le_max_enat`: the
  clauses of a fold rule whose bounds are natural numbers cast to `ℕ∞`.
* `wpFold_demonicUnder_liftBind_const`: a call whose continuation ignores the answer keeps the
  leaf invariant of the continuation.
* `wpFold_charge_eq_chargeUnder_true`: the worst-case charge fold is the fold of `chargeUnder`
  with every answer allowed.
* `wpFold_chargeUnder_pi_apply`, `wpFold_chargeUnder_pi_le_iff`,
  `wpFold_chargeUnder_price_le_sum`, `wpFold_chargeUnder_price_le`: vector charges fold
  componentwise, and a price turns a vector bound into a scalar one.
* `OpSpec.chargeUnder_eq`, `OpSpec.demonicUnder_eq`, `wpFold_chargeUnder_eq_restrict`: the
  readings over allowed answers are the readings of the restriction `P.restrict allows`.

Under the upper-bound reading `(OpSpec.charge c).toUpperWPMonad (OpSpec.charge_mono c)`, a triple
`⦃ toDual t ⦄ x ⦃ post ⦄` states that the charge-to-go of `x` is at most `t`.
`PolyFun.PFunctor.Free.Do` registers the operation rule `Spec.lift_upper`. It decomposes one call:
the continuation stays under the supremum, and rewriting with `OpSpec.toUpperWPMonad_wp` returns
the remaining condition to the fold.
-/

@[expose] public section

universe uA uB uA₂ uB₂ v w z

open Std.WP

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type uB}

/-! ## Budgets are charge bounds -/

/-- Subtractive per-position budgets are exactly upper bounds on the worst-case charge fold: the
natural-number case of `isChargeBound_iff_cost_natCast_le`. -/
theorem isRollBound_iff_wpFold_charge (c : P.A → ℕ) (x : FreeM P α) (n : ℕ) :
    IsRollBound x n (fun a b => c a ≤ b) (fun a b => b - c a) ↔
      wpFold (OpSpec.charge fun a => (c a : ℕ∞)) x (fun _ => 0) ≤ n :=
  (isChargeBound_iff_isRollBound_nat x c n).symm.trans isChargeBound_iff_cost_natCast_le

/-- Total roll bounds are unit-charge bounds. -/
theorem isTotalRollBound_iff_wpFold_charge (x : FreeM P α) (n : ℕ) :
    IsTotalRollBound x n ↔ wpFold (OpSpec.charge fun _ => (1 : ℕ∞)) x (fun _ => 0) ≤ n := by
  have := isRollBound_iff_wpFold_charge (fun _ => 1) x n
  simpa [IsTotalRollBound, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using this

/-! ## Simulation overhead -/

/-- The charge fold splits off the continuation: the charge-to-go is at most the program's own
charge plus the worst continuation value. This is `costWith_le_cost_add` in `ℕ∞`. -/
theorem wpFold_charge_le {Q : PFunctor.{uA₂, uB₂}} (c : Q.A → ℕ∞) {β : Type v} (y : FreeM Q β)
    (k : β → ℕ∞) :
    wpFold (OpSpec.charge c) y k ≤ wpFold (OpSpec.charge c) y (fun _ => 0) + ⨆ b, k b :=
  costWith_le_cost_add y k

/-- **Simulation overhead.** A program simulated through a handler costs at most the program with
each call at `a` charged the handler's worst-case cost at `a`. This is `cost_liftM_le` in `ℕ∞`. -/
theorem wpFold_charge_liftM_le {Q : PFunctor.{uA₂, uB₂}} (c : Q.A → ℕ∞)
    (handler : (a : P.A) → FreeM Q (P.B a)) (x : FreeM P α) :
    wpFold (OpSpec.charge c) (x.liftM handler) (fun _ => 0) ≤
      wpFold (OpSpec.charge (handlerCost c handler)) x (fun _ => 0) :=
  cost_liftM_le c handler x

/-! ## Ranked simulation triples -/

section Ranked

variable {n : Type uB → Type w} [Monad n] {Pred : Type v} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WPMonad n Pred EPred]

/-- **Invariant simulation.** If every call of the handler preserves an assertion, then every
program simulated through it preserves that assertion. -/
theorem triple_liftM_invariant (handler : (a : P.A) → n (P.B a)) (I : Pred) (E : EPred)
    (hstep : ∀ a, Triple (handler a) I (fun _ => I) E) (x : FreeM P α) :
    Triple (x.liftM handler) I (fun _ => I) E := by
  induction x with
  | pure x => exact Triple.pure x Lean.Order.PartialOrder.rel_refl
  | lift_bind a r ih =>
    change Triple (handler a >>= fun u => (r u).liftM handler) _ _ E
    exact Triple.bind _ _ _ (hstep a) ih

/-- **Ranked simulation** over any roll budget. If a call at `a` admitted at budget `b` turns rank
`Φ b` into rank `Φ (cost a b)`, and every rank entails the final assertion `Φ₀`, then a program
within budget `b` (`IsRollBound x b canRoll cost`) maps rank `Φ b` to `Φ₀`. The budget type, the
admission test and the cost are those of the roll bound; `triple_liftM_ranked` is the subtractive
natural-number budget, `triple_liftM_ranked_total` the unit-charge one, and `IsRollBound.prod` and
`IsRollBound.pi` combine budgets. -/
theorem triple_liftM_of_isRollBound {B : Type*} (handler : (a : P.A) → n (P.B a))
    {canRoll : P.A → B → Prop} {cost : P.A → B → B} (Φ : B → Pred) (Φ₀ : Pred) (E : EPred)
    (hstep : ∀ a b, canRoll a b → Triple (handler a) (Φ b) (fun _ => Φ (cost a b)) E)
    (hdrop : ∀ b, Lean.Order.PartialOrder.rel (Φ b) Φ₀)
    (x : FreeM P α) (b : B) (hx : IsRollBound x b canRoll cost) :
    Triple (x.liftM handler) (Φ b) (fun _ => Φ₀) E := by
  induction x generalizing b with
  | pure x => exact Triple.pure x (hdrop b)
  | lift_bind a r ih =>
    rw [isRollBound_lift_bind_iff] at hx
    change Triple (handler a >>= fun u => (r u).liftM handler) _ _ E
    exact Triple.bind _ _ _ (hstep a b hx.1) fun u => ih u (cost a b) (hx.2 u)

/-- **Ranked simulation over a charge bound**, in spent-amount form and over any cost type. If a
call at `a` admitted with `s` spent turns rank `Φ s` into rank `Φ (s + c a)`, and every rank
within budget entails the final assertion `Φ₀`, then a program within budget `B`, starting from
`s` spent, maps rank `Φ s` to `Φ₀`. With `Φ s` reading "the handler state records at most `s`"
this bounds the state of a counting handler by the budget. -/
theorem triple_liftM_of_isChargeBound {ω : Type*} [Add ω] [LE ω] [Zero ω]
    (handler : (a : P.A) → n (P.B a)) {c : P.A → ω} {B : ω} (Φ : ω → Pred) (Φ₀ : Pred)
    (E : EPred) (hstep : ∀ a s, s + c a ≤ B → Triple (handler a) (Φ s) (fun _ => Φ (s + c a)) E)
    (hdrop : ∀ s, s ≤ B → Lean.Order.PartialOrder.rel (Φ s) Φ₀)
    (x : FreeM P α) (s : ω) (hx : x.IsChargeBound c B s) :
    Triple (x.liftM handler) (Φ s) (fun _ => Φ₀) E := by
  induction x using FreeM.rec generalizing s with
  | pure x => exact Triple.pure x (hdrop s hx)
  | liftBind a r ih =>
    change Triple (handler a >>= fun u => (r u).liftM handler) _ _ E
    exact Triple.bind _ _ _ (hstep a s hx.1) fun u => ih u (s + c a) (hx.2 u)

/-- **Ranked simulation.** If every call at `a` consumes `c a` units of rank, then a program
within budget `k` maps rank `k` to rank `0`, after dropping unspent rank. -/
theorem triple_liftM_ranked (handler : (a : P.A) → n (P.B a)) (c : P.A → ℕ)
    (Φ : ℕ → Pred) (E : EPred)
    (hstep : ∀ a k, Triple (handler a) (Φ (k + c a)) (fun _ => Φ k) E)
    (hdrop : ∀ k, Lean.Order.PartialOrder.rel (Φ k) (Φ 0))
    (x : FreeM P α) (k : ℕ)
    (hx : IsRollBound x k (fun a b => c a ≤ b) (fun a b => b - c a)) :
    Triple (x.liftM handler) (Φ k) (fun _ => Φ 0) E := by
  refine triple_liftM_of_isRollBound handler Φ (Φ 0) E (fun a b hb => ?_) hdrop x k hx
  obtain ⟨j, rfl⟩ : ∃ j, b = j + c a := ⟨b - c a, (Nat.sub_add_cancel hb).symm⟩
  rw [Nat.add_sub_cancel]
  exact hstep a j

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

/-! ## The charge reading over allowed answers as a reading of the restriction -/

namespace OpSpec

variable {P : PFunctor.{uA, uB}}

/-- `chargeUnder c allows` is the charge reading of the restriction, with the continuation read
through the inclusion of directions. -/
theorem chargeUnder_eq {R : Type w} [CompleteLattice R] [Add R] (c : P.A → R)
    (allows : (a : P.A) → P.B a → Prop) :
    chargeUnder c allows =
      fun a k => charge (P := P.restrict allows) c a (k ∘ Subtype.val) := by
  funext a k
  rw [chargeUnder_apply]
  exact congrArg (c a + ·) iSup_subtype'

/-- `demonicUnder allows` is the demonic reading of the restriction, with the continuation read
through the inclusion of directions. -/
theorem demonicUnder_eq (allows : (a : P.A) → P.B a → Prop) :
    demonicUnder allows = fun a k => demonic (P.restrict allows) a (k ∘ Subtype.val) := by
  funext a k
  exact propext ⟨fun h b => h b.1 b.2, fun h b hb => h ⟨b, hb⟩⟩

end OpSpec

namespace FreeM

variable {P : PFunctor.{uA, uB}}

/-! ## The charge fold over allowed answers -/

section Under

variable {α : Type v}

/-- A natural-number budget `n` bounds the charge fold of a call at `a` iff `c a ≤ n` and
`n - c a` bounds the charge fold of the continuation at every allowed answer. -/
theorem wpFold_chargeUnder_liftBind_le_iff (c : P.A → ℕ) (allows : (a : P.A) → P.B a → Prop)
    (a : P.A) (r : P.B a → FreeM P α) (n : ℕ) {post : α → ℕ∞} :
    wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (FreeM.liftBind a r) post ≤ n ↔
      c a ≤ n ∧ ∀ b, allows a b →
        wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (r b) post ≤
          ((n - c a : ℕ) : ℕ∞) := by
  rw [wpFold_liftBind, OpSpec.chargeUnder_apply]
  constructor
  · intro h
    have hc : c a ≤ n := by exact_mod_cast le_self_add.trans h
    refine ⟨hc, fun b hb => ?_⟩
    have h' : (c a : ℕ∞) + wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (r b) post ≤
        (c a : ℕ∞) + ((n - c a : ℕ) : ℕ∞) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hc]
      refine le_trans ?_ h
      gcongr
      exact le_iSup₂_of_le (f := fun b (_ : allows a b) =>
        wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (r b) post) b hb le_rfl
    exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).1 h'
  · rintro ⟨hc, hr⟩
    calc _ ≤ (c a : ℕ∞) + ((n - c a : ℕ) : ℕ∞) := by gcongr; exact iSup₂_le hr
      _ = n := by rw [← Nat.cast_add, Nat.add_sub_cancel' hc]

/-- A call at `a` whose continuation ignores the answer costs `c a` plus the continuation, when
`a` has an allowed answer. This is `costUnder_liftBind_const` at a general postcondition. -/
theorem wpFold_chargeUnder_liftBind_const {R : Type w} [CompleteLattice R] [Add R]
    (c : P.A → R) (allows : (a : P.A) → P.B a → Prop) (a : P.A) {b : P.B a} (hb : allows a b)
    (y : FreeM P α) (post : α → R) :
    wpFold (OpSpec.chargeUnder c allows) (FreeM.liftBind a fun _ => y) post =
      c a + wpFold (OpSpec.chargeUnder c allows) y post := by
  rw [wpFold_liftBind, OpSpec.chargeUnder_apply]
  exact congrArg (c a + ·)
    (le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le b hb le_rfl))

/-- Ticks merge: a call at `a` with charge `c a₁ + c a₂` whose continuation ignores the answer
has the fold of a call at `a₁` followed by a call at `a₂`, when each has an allowed answer. -/
theorem wpFold_chargeUnder_liftBind_const_add {R : Type w} [CompleteLattice R] [AddSemigroup R]
    (c : P.A → R) (allows : (a : P.A) → P.B a → Prop) {a a₁ a₂ : P.A}
    (hc : c a = c a₁ + c a₂) {b : P.B a} (hb : allows a b) {b₁ : P.B a₁} (hb₁ : allows a₁ b₁)
    {b₂ : P.B a₂} (hb₂ : allows a₂ b₂) (y : FreeM P α) (post : α → R) :
    wpFold (OpSpec.chargeUnder c allows) (FreeM.liftBind a fun _ => y) post =
      wpFold (OpSpec.chargeUnder c allows)
        (FreeM.liftBind a₁ fun _ => FreeM.liftBind a₂ fun _ => y) post := by
  rw [wpFold_chargeUnder_liftBind_const c allows a hb,
    wpFold_chargeUnder_liftBind_const c allows a₁ hb₁,
    wpFold_chargeUnder_liftBind_const c allows a₂ hb₂, hc, add_assoc]

/-- With every answer allowed, a bound on the charge fold is the subtractive roll bound: the
`chargeUnder` form of `isRollBound_iff_wpFold_charge`. -/
theorem isRollBound_iff_wpFold_chargeUnder_true {α : Type uB} (c : P.A → ℕ) (x : FreeM P α)
    (n : ℕ) :
    IsRollBound x n (fun a b => c a ≤ b) (fun a b => b - c a) ↔
      wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) fun _ _ => True) x (fun _ => 0) ≤
        n := by
  rw [OpSpec.chargeUnder_true, isRollBound_iff_wpFold_charge]

end Under

/-! ## The clauses of the fold rule

Each clause bounds the charge fold of a program by a natural number cast to `ℕ∞` from the
bounds of its parts, so that a bound computed clause by clause is a term of `ℕ`. -/

section Rule

variable {X : Type v} {Y : Type z}

/-- A return charges nothing. -/
theorem wpFold_chargeUnder_pure_le (c : P.A → ℕ) (allows : (a : P.A) → P.B a → Prop) (x : X)
    (n : ℕ) :
    wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (FreeM.pure x : FreeM P X)
      (fun _ => 0) ≤ (n : ℕ∞) :=
  zero_le

/-- A call at `a` is bounded by a bound `m` of its charge plus a bound `n` of its continuation at
every allowed answer. -/
theorem wpFold_chargeUnder_liftBind_le (c : P.A → ℕ) (allows : (a : P.A) → P.B a → Prop)
    (a : P.A) (r : P.B a → FreeM P X) (m n : ℕ) {post : X → ℕ∞} (hc : c a ≤ m)
    (hr : ∀ b, allows a b →
      wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (r b) post ≤ (n : ℕ∞)) :
    wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (FreeM.liftBind a r) post ≤
      ((m + n : ℕ) : ℕ∞) := by
  rw [wpFold_liftBind, OpSpec.chargeUnder_apply, Nat.cast_add]
  exact add_le_add (by exact_mod_cast hc) (iSup₂_le hr)

/-- The bind clause with natural-number bounds: a bound `m` of `x` and a bound `n` of `f a` at
every return `a` satisfying the leaf invariant `I` of `x` add to a bound of `x.bind f`. Only `x`
is bounded at the postcondition `0`. -/
theorem wpFold_chargeUnder_bind_le_add (c : P.A → ℕ) (allows : (a : P.A) → P.B a → Prop)
    (x : FreeM P X) (f : X → FreeM P Y) (I : X → Prop) (m n : ℕ) {post : Y → ℕ∞}
    (hx : wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) x (fun _ => 0) ≤ (m : ℕ∞))
    (hf : ∀ a, I a →
      wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (f a) post ≤ (n : ℕ∞))
    (hI : wpFold (OpSpec.demonicUnder allows) x I) :
    wpFold (OpSpec.chargeUnder (fun a => (c a : ℕ∞)) allows) (x.bind f) post ≤
      ((m + n : ℕ) : ℕ∞) := by
  rw [wpFold_bind', Nat.cast_add]
  exact (wpFold_chargeUnder_le_costUnder_add hI _).trans (add_le_add hx (iSup₂_le hf))

/-- A call whose continuation ignores the answer keeps the leaf invariant of the continuation. -/
theorem wpFold_demonicUnder_liftBind_const (allows : (a : P.A) → P.B a → Prop) (a : P.A)
    {y : FreeM P X} {I : X → Prop} (h : wpFold (OpSpec.demonicUnder allows) y I) :
    wpFold (OpSpec.demonicUnder allows) (FreeM.liftBind a fun _ => y) I :=
  fun _ _ => h

/-- An `if` of programs is bounded in `ℕ∞` by the maximum of the bounds of its branches. -/
theorem wpFold_ite_le_max_enat (Φ : OpSpec P ℕ∞) (p : Prop) [Decidable p] (x y : FreeM P X)
    (post : X → ℕ∞) {m n : ℕ} (hx : wpFold Φ x post ≤ (m : ℕ∞)) (hy : wpFold Φ y post ≤ (n : ℕ∞)) :
    wpFold Φ (if p then x else y) post ≤ ((max m n : ℕ) : ℕ∞) := by
  split
  · exact hx.trans (by exact_mod_cast le_max_left m n)
  · exact hy.trans (by exact_mod_cast le_max_right m n)

/-- A dependent `if` of programs is bounded in `ℕ∞` by the maximum of the bounds of its
branches. -/
theorem wpFold_dite_le_max_enat (Φ : OpSpec P ℕ∞) (p : Prop) [Decidable p] (x : p → FreeM P X)
    (y : ¬p → FreeM P X) (post : X → ℕ∞) {m n : ℕ} (hx : ∀ h, wpFold Φ (x h) post ≤ (m : ℕ∞))
    (hy : ∀ h, wpFold Φ (y h) post ≤ (n : ℕ∞)) :
    wpFold Φ (if h : p then x h else y h) post ≤ ((max m n : ℕ) : ℕ∞) := by
  split
  · exact (hx _).trans (by exact_mod_cast le_max_left m n)
  · exact (hy _).trans (by exact_mod_cast le_max_right m n)

/-- The worst-case charge fold is the charge fold with every answer allowed: the `wpFold` form of
`OpSpec.chargeUnder_true`. -/
theorem wpFold_charge_eq_chargeUnder_true {R : Type w} [CompleteLattice R] [Add R]
    (c : P.A → R) (x : FreeM P X) (post : X → R) :
    wpFold (OpSpec.charge c) x post = wpFold (OpSpec.chargeUnder c fun _ _ => True) x post := by
  rw [OpSpec.chargeUnder_true]

end Rule

/-! ## Vector charges and prices

A charge `c : P.A → ι → R` with values in the pointwise lattice `ι → R` counts one resource per
index `i`. Suprema and sums in `ι → R` are pointwise, so the component `i` of the charge fold is
the scalar charge fold at `fun a => c a i`. Pricing the components by `p : ι → ℕ∞` turns a vector
bound `u` into the scalar bound `∑ i, p i * u i` on the fold at the priced charge. -/

section Vector

variable {α : Type v}

/-- The component `i` of the charge fold at a vector charge is the charge fold at the component
`i` of the charge, with the component `i` of the postcondition. -/
theorem wpFold_chargeUnder_pi_apply {ι : Type*} {R : Type w} [CompleteLattice R] [Add R]
    (c : P.A → ι → R) (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) (post : α → ι → R)
    (i : ι) :
    wpFold (OpSpec.chargeUnder c allows) x post i =
      wpFold (OpSpec.chargeUnder (fun a => c a i) allows) x (fun r => post r i) := by
  induction x with
  | pure r => rfl
  | lift_bind a r ih =>
    change (c a + ⨆ b, ⨆ (_ : allows a b), wpFold (OpSpec.chargeUnder c allows) (r b) post) i =
      c a i + ⨆ b, ⨆ (_ : allows a b),
        wpFold (OpSpec.chargeUnder (fun a => c a i) allows) (r b) (fun r => post r i)
    simp only [Pi.add_apply, iSup_apply, ih]

/-- A vector bound on the charge fold is the family of the component bounds, each a bound on the
scalar charge fold at the component of the charge. -/
theorem wpFold_chargeUnder_pi_le_iff {ι : Type*} {R : Type w} [CompleteLattice R] [Add R]
    (c : P.A → ι → R) (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) (post : α → ι → R)
    (u : ι → R) :
    wpFold (OpSpec.chargeUnder c allows) x post ≤ u ↔
      ∀ i, wpFold (OpSpec.chargeUnder (fun a => c a i) allows) x (fun r => post r i) ≤ u i := by
  simp only [Pi.le_def, wpFold_chargeUnder_pi_apply]

/-- The fold at a priced charge is at most the priced vector fold: at the price `p`, the charge
`fun a => ∑ i, p i * c a i` folds to at most `∑ i, p i * (fold at c) i`. -/
theorem wpFold_chargeUnder_price_le_sum {ι : Type*} [Fintype ι] (c : P.A → ι → ℕ∞)
    (allows : (a : P.A) → P.B a → Prop) (p : ι → ℕ∞) (x : FreeM P α) (post : α → ι → ℕ∞) :
    wpFold (OpSpec.chargeUnder (fun a => ∑ i, p i * c a i) allows) x
        (fun r => ∑ i, p i * post r i) ≤
      ∑ i, p i * wpFold (OpSpec.chargeUnder c allows) x post i := by
  induction x with
  | pure r => exact le_rfl
  | lift_bind a r ih =>
    change (∑ i, p i * c a i) + ⨆ b, ⨆ (_ : allows a b),
        wpFold (OpSpec.chargeUnder (fun a => ∑ i, p i * c a i) allows) (r b)
          (fun r => ∑ i, p i * post r i) ≤
      ∑ i, p i * (c a + ⨆ b, ⨆ (_ : allows a b),
        wpFold (OpSpec.chargeUnder c allows) (r b) post) i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    refine add_le_add le_rfl (iSup₂_le fun b hb => (ih b).trans ?_)
    refine Finset.sum_le_sum fun i _ => mul_le_mul_right ?_ (p i)
    exact le_iSup₂_of_le (f := fun b (_ : allows a b) =>
      wpFold (OpSpec.chargeUnder c allows) (r b) post) b hb le_rfl i

/-- **Pricing a vector bound.** If the charge fold at the vector charge `c` is at most `u`, then
at every price `p` the charge fold at `fun a => ∑ i, p i * c a i` is at most
`∑ i, p i * u i`. -/
theorem wpFold_chargeUnder_price_le {ι : Type*} [Fintype ι] (c : P.A → ι → ℕ∞)
    (allows : (a : P.A) → P.B a → Prop) (p : ι → ℕ∞) {x : FreeM P α} {u : ι → ℕ∞}
    (hu : wpFold (OpSpec.chargeUnder c allows) x (fun _ => 0) ≤ u) :
    wpFold (OpSpec.chargeUnder (fun a => ∑ i, p i * c a i) allows) x (fun _ => 0) ≤
      ∑ i, p i * u i := by
  simpa using (wpFold_chargeUnder_price_le_sum c allows p x (fun _ => 0)).trans
    (Finset.sum_le_sum fun i _ => mul_le_mul_right (hu i) (p i))

/-- The charge fold over the allowed answers is the charge fold of the restricted tree. -/
theorem wpFold_chargeUnder_eq_restrict {R : Type w} [CompleteLattice R] [Add R] (c : P.A → R)
    (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) (post : α → R) :
    wpFold (OpSpec.chargeUnder c allows) x post =
      wpFold (OpSpec.charge (P := P.restrict allows) c) (x.restrict allows) post := by
  rw [FreeM.restrict, wpFold_mapLens, OpSpec.chargeUnder_eq]
  rfl

end Vector

end FreeM

end PFunctor
