/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.WP
public import PolyFun.PFunctor.Bound
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Order.Sub.Prod
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Charge bounds on free programs

A *charge* `c : P.A → ω` prices each call of an interface `P` in an ordered additive monoid `ω`.
It is paid when the call is made, before its answer arrives. `IsChargeBound x c B s` says that,
with `s` already spent, the amount spent along every branch of `x : FreeM P α`, call by call,
stays at most `B`. It is the fold of `OpSpec.budget c B`, whose carrier is a predicate on the
amount spent so far, so a call at `a` asks `s + c a ≤ B` and no subtraction or existential is
involved. The spent amount defaults to `0`. The definition makes sense in any type with addition
and an order, including `ℕ`, vectors `ι → ℕ`, `ℤ` and records of counters; its laws hold in ordered
additive monoids.

## Relation to roll bounds

`IsRollBound x b canRoll cost` is the general budget automaton: an arbitrary state `b`, an
admission test and an update read off each call position. It is also a fold
(`isRollBound_iff_wpFold`, of `OpSpec.roll`). A charge bound is the additive instance whose state
is the amount spent (`isChargeBound_iff_isRollBound`), plus a check of the amount spent at each
leaf. With natural-number charges it is the subtractive budget on what remains
(`isChargeBound_iff_isRollBound_nat`, and `isChargeBound_iff_isRollBound_orderedSub` for vectors
and pairs), and unit charges give `IsTotalRollBound`. Roll bounds also express non-additive
protocols; charge bounds have additive laws with no side conditions:

* sequencing adds budgets (`IsChargeBound.bind`), and `IsChargeBound.bind_of_le` lets the
  continuation start from any amount spent within a bound;
* bounds are monotone in the budget, the charge and the amount spent;
* bounds push forward along monotone additive maps (`IsChargeBound.map`) and transfer both ways
  along additive order embeddings such as `ℕ ↪ ℕ∞` (`isChargeBound_comp_iff`);
* pairs and families of charges split componentwise (`isChargeBound_prod_iff`,
  `isChargeBound_pi_iff`);
* bounds transport along lenses (`IsChargeBound.mapLens`) and through free handlers whose
  implementation of each call stays within its charge (`IsChargeBound.liftM`).

A query whose answer type is empty is still charged: the bound counts the call itself, not only
the calls on completed paths.
-/

@[expose] public section

universe uA uB uA₂ uB₂ v v' w w'

namespace PFunctor

namespace OpSpec

variable {P : PFunctor.{uA, uB}}

/-- The budget reading of a charge, in spent-amount form. The carrier is a predicate on the
amount spent so far: a call at `a` is admitted when the amount spent after it, `s + c a`, is at
most `B`, and each continuation starts from that amount. -/
def budget {ω : Type w} [Add ω] [LE ω] (c : P.A → ω) (B : ω) : OpSpec P (ω → Prop) :=
  fun a k s => s + c a ≤ B ∧ ∀ b, k b (s + c a)

@[simp]
theorem budget_apply {ω : Type w} [Add ω] [LE ω] (c : P.A → ω) (B : ω) (a : P.A)
    (k : P.B a → ω → Prop) (s : ω) :
    budget c B a k s ↔ s + c a ≤ B ∧ ∀ b, k b (s + c a) :=
  Iff.rfl

/-- The budget reading is monotone in its continuation. -/
theorem budget_monotone {ω : Type w} [Add ω] [LE ω] (c : P.A → ω) (B : ω) :
    (budget c B).Monotone :=
  fun _ _ _ hk _ hs => ⟨hs.1, fun b => hk b _ (hs.2 b)⟩

/-- The fold of a roll bound: a call at `a` is admitted at state `b` when `canRoll a b`, and each
continuation starts from `cost a b`. -/
def roll {σ : Type w} (canRoll : P.A → σ → Prop) (cost : P.A → σ → σ) : OpSpec P (σ → Prop) :=
  fun a k b => canRoll a b ∧ ∀ y, k y (cost a b)

@[simp]
theorem roll_apply {σ : Type w} (canRoll : P.A → σ → Prop) (cost : P.A → σ → σ) (a : P.A)
    (k : P.B a → σ → Prop) (b : σ) :
    roll canRoll cost a k b ↔ canRoll a b ∧ ∀ y, k y (cost a b) :=
  Iff.rfl

/-- The budget reading restricted to allowed answers: a call at `a` is admitted when the amount
spent after it is at most `B`, and only the continuations at answers `b` with `allows a b` must stay
within budget. It is the budget counterpart of `demonicUnder`; with every answer allowed it is
`budget` (`budgetUnder_true`). -/
def budgetUnder {ω : Type w} [Add ω] [LE ω] (c : P.A → ω) (B : ω)
    (allows : (a : P.A) → P.B a → Prop) : OpSpec P (ω → Prop) :=
  fun a k s => s + c a ≤ B ∧ ∀ b, allows a b → k b (s + c a)

@[simp]
theorem budgetUnder_apply {ω : Type w} [Add ω] [LE ω] (c : P.A → ω) (B : ω)
    (allows : (a : P.A) → P.B a → Prop) (a : P.A) (k : P.B a → ω → Prop) (s : ω) :
    budgetUnder c B allows a k s ↔ s + c a ≤ B ∧ ∀ b, allows a b → k b (s + c a) :=
  Iff.rfl

theorem budgetUnder_true {ω : Type w} [Add ω] [LE ω] (c : P.A → ω) (B : ω) :
    budgetUnder c B (fun (_ : P.A) _ => True) = budget c B := by
  funext a k s
  simp [budgetUnder, budget]

theorem budgetUnder_monotone {ω : Type w} [Add ω] [LE ω] (c : P.A → ω) (B : ω)
    (allows : (a : P.A) → P.B a → Prop) : (budgetUnder c B allows).Monotone :=
  fun _ _ _ hk _ hs => ⟨hs.1, fun b hb => hk b _ (hs.2 b hb)⟩

/-- The roll reading restricted to allowed answers: a call at `a` is admitted at state `b` when
`canRoll a b`, and only the continuations at allowed answers start from `cost a b`. With every
answer allowed it is `roll` (`rollUnder_true`). -/
def rollUnder {σ : Type w} (canRoll : P.A → σ → Prop) (cost : P.A → σ → σ)
    (allows : (a : P.A) → P.B a → Prop) : OpSpec P (σ → Prop) :=
  fun a k b => canRoll a b ∧ ∀ y, allows a y → k y (cost a b)

@[simp]
theorem rollUnder_apply {σ : Type w} (canRoll : P.A → σ → Prop) (cost : P.A → σ → σ)
    (allows : (a : P.A) → P.B a → Prop) (a : P.A) (k : P.B a → σ → Prop) (b : σ) :
    rollUnder canRoll cost allows a k b ↔ canRoll a b ∧ ∀ y, allows a y → k y (cost a b) :=
  Iff.rfl

theorem rollUnder_true {σ : Type w} (canRoll : P.A → σ → Prop) (cost : P.A → σ → σ) :
    rollUnder canRoll cost (fun (_ : P.A) _ => True) = roll canRoll cost := by
  funext a k b
  simp [rollUnder, roll]

end OpSpec

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α β : Type v} {ω : Type w}

/-! ## Roll bounds as folds -/

section Roll

variable {σ : Type w}

/-- A roll bound is the fold of its admission test and update, with every leaf accepted. -/
theorem isRollBound_iff_wpFold (x : FreeM P α) (b : σ) (canRoll : P.A → σ → Prop)
    (cost : P.A → σ → σ) :
    IsRollBound x b canRoll cost ↔ wpFold (OpSpec.roll canRoll cost) x (fun _ _ => True) b := by
  induction x using FreeM.rec generalizing b with
  | pure a => exact iff_of_true trivial trivial
  | liftBind a r ih =>
    rw [isRollBound_liftBind_iff, wpFold_liftBind, OpSpec.roll_apply]
    exact and_congr_right fun _ => forall_congr' fun y => ih y _

end Roll

/-! ## Structural charge bounds -/

section Bound

variable [Add ω] [LE ω] [Zero ω]

/-- `x.IsChargeBound c B s`: with `s` already spent, every call of `x` keeps the amount spent at
most `B`, where a call at `a` costs `c a`, and every leaf is reached within `B`. The spent amount
defaults to `0`.

The bound is relative to an accounting boundary: it charges the calls of `x` and nothing else.
The code between calls, the answers and the handler or machine that produces them are free at
this layer, and are bounded one layer down (`docs/guides/cost.md`, "Accounting boundary"). Read as
a resource contract, it needs a canonically ordered cost type: with negative prices, refund calls
make any budget reachable. -/
def IsChargeBound (x : FreeM P α) (c : P.A → ω) (B : ω) (spent : ω := 0) : Prop :=
  wpFold (OpSpec.budget c B) x (fun _ s => s ≤ B) spent

variable {c : P.A → ω} {B s : ω}

@[simp, freeM_unfold]
theorem isChargeBound_pure_iff (a : α) :
    IsChargeBound (pure a : FreeM P α) c B s ↔ s ≤ B :=
  Iff.rfl

/-- `isChargeBound_pure_iff` for the constructor `FreeM.pure`, which `TypeTree.done` and the
recursor produce. -/
@[freeM_unfold]
theorem isChargeBound_freeM_pure_iff (a : α) :
    IsChargeBound (FreeM.pure a : FreeM P α) c B s ↔ s ≤ B :=
  Iff.rfl

@[freeM_unfold]
theorem isChargeBound_liftBind_iff (a : P.A) (r : P.B a → FreeM P α) :
    IsChargeBound (FreeM.liftBind a r) c B s ↔
      s + c a ≤ B ∧ ∀ b, IsChargeBound (r b) c B (s + c a) :=
  Iff.rfl

@[simp]
theorem isChargeBound_lift_bind_iff (a : P.A) (r : P.B a → FreeM P α) :
    IsChargeBound ((FreeM.lift a).bind (α := no_index (P.B a)) r) c B s ↔
      s + c a ≤ B ∧ ∀ b, IsChargeBound (r b) c B (s + c a) :=
  Iff.rfl

/-- `isChargeBound_lift_bind_iff` when results and directions share a universe. -/
theorem isChargeBound_lift_bind_iff' {α : Type uB} (a : P.A) (r : P.B a → FreeM P α) :
    IsChargeBound (Bind.bind (α := no_index (P.B a)) (FreeM.lift a) r) c B s ↔
      s + c a ≤ B ∧ ∀ b, IsChargeBound (r b) c B (s + c a) :=
  Iff.rfl

@[simp]
theorem isChargeBound_lift_iff (a : P.A) :
    IsChargeBound (α := no_index (P.B a)) (FreeM.lift a) c B s ↔ s + c a ≤ B :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ => h⟩⟩

/-- A lifted object (the form in which `MonadLift P (FreeM P)` issues a call) is one call. -/
theorem isChargeBound_liftObj_iff (x : P.Obj α) :
    IsChargeBound (FreeM.liftObj x) c B s ↔ s + c x.1 ≤ B :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ => h⟩⟩

/-- Sequencing, exactly: the continuation starts from whatever amount each branch of `x` has
spent. -/
theorem isChargeBound_bind_iff {γ : Type v'} (x : FreeM P α) (f : α → FreeM P γ) :
    IsChargeBound (FreeM.bind x f) c B s ↔
      wpFold (OpSpec.budget c B) x (fun a s' => IsChargeBound (f a) c B s') s := by
  unfold IsChargeBound
  rw [wpFold_bind']

@[simp]
theorem isChargeBound_bind_iff' (x : FreeM P α) (f : α → FreeM P β) :
    IsChargeBound (x >>= f) c B s ↔
      wpFold (OpSpec.budget c B) x (fun a s' => IsChargeBound (f a) c B s') s :=
  isChargeBound_bind_iff x f

@[simp]
theorem isChargeBound_map_iff {γ : Type v'} (f : α → γ) (x : FreeM P α) :
    IsChargeBound (FreeM.map f x) c B s ↔ IsChargeBound x c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact Iff.rfl
  | liftBind a r ih => exact and_congr_right fun _ => forall_congr' fun b => ih b

@[simp]
theorem isChargeBound_map_iff' (f : α → β) (x : FreeM P α) :
    IsChargeBound (f <$> x) c B s ↔ IsChargeBound x c B s :=
  isChargeBound_map_iff f x

@[simp]
theorem isChargeBound_ite (p : Prop) [Decidable p] (x y : FreeM P α) :
    IsChargeBound (if p then x else y) c B s ↔
      if p then IsChargeBound x c B s else IsChargeBound y c B s := by
  split <;> rfl

@[simp]
theorem isChargeBound_dite (p : Prop) [Decidable p] (x : p → FreeM P α) (y : ¬ p → FreeM P α) :
    IsChargeBound (if h : p then x h else y h) c B s ↔
      if h : p then IsChargeBound (x h) c B s else IsChargeBound (y h) c B s := by
  split <;> rfl

end Bound

section OrderedBound

variable [AddCommMonoid ω] [PartialOrder ω] {c c' : P.A → ω} {B B' s s' : ω}

/-- Starting from less spent keeps a program within budget. -/
theorem IsChargeBound.mono_spent [IsOrderedAddMonoid ω] {x : FreeM P α} (h : IsChargeBound x c B s)
    (hs : s' ≤ s) :
    IsChargeBound x c B s' := by
  induction x using FreeM.rec generalizing s s' with
  | pure a => exact hs.trans h
  | liftBind a r ih =>
    have hs' : s' + c a ≤ s + c a := add_le_add hs le_rfl
    exact ⟨hs'.trans h.1, fun b => ih b (h.2 b) hs'⟩

/-- A larger budget keeps a program within budget. -/
theorem IsChargeBound.mono {x : FreeM P α} (h : IsChargeBound x c B s) (hB : B ≤ B') :
    IsChargeBound x c B' s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact h.trans hB
  | liftBind a r ih => exact ⟨h.1.trans hB, fun b => ih b (h.2 b)⟩

/-- Cheaper calls keep a program within budget. -/
theorem IsChargeBound.mono_charge [IsOrderedAddMonoid ω] {x : FreeM P α} (h : IsChargeBound x c B s)
    (hc : ∀ a, c' a ≤ c a) : IsChargeBound x c' B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact h
  | liftBind a r ih =>
    have hs : s + c' a ≤ s + c a := add_le_add le_rfl (hc a)
    exact ⟨hs.trans h.1, fun b => (ih b (h.2 b)).mono_spent hs⟩

/-- Shifting the spent amount shifts the budget. -/
theorem IsChargeBound.add_left [IsOrderedAddMonoid ω] {x : FreeM P α} (h : IsChargeBound x c B s)
    (t : ω) :
    IsChargeBound x c (t + B) (t + s) := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact add_le_add le_rfl h
  | liftBind a r ih =>
    refine ⟨?_, fun b => ?_⟩
    · rw [add_assoc]; exact add_le_add le_rfl h.1
    · rw [add_assoc]; exact ih b (h.2 b)

/-- **Sequencing.** If `x` stays within `L ≤ B` and each continuation stays within `B` from any
amount at most `L`, then `x >>= f` stays within `B`. -/
theorem IsChargeBound.bind_of_le {γ : Type v'} {x : FreeM P α} {f : α → FreeM P γ} {L : ω}
    (hx : IsChargeBound x c L s) (hL : L ≤ B)
    (hf : ∀ a s', s' ≤ L → IsChargeBound (f a) c B s') :
    IsChargeBound (FreeM.bind x f) c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact hf a s hx
  | liftBind a r ih =>
    exact ⟨hx.1.trans hL, fun b => ih b (hx.2 b)⟩

end OrderedBound

section CanonicalBound

variable [AddCommMonoid ω] [PartialOrder ω] [CanonicallyOrderedAdd ω]
  {c : P.A → ω} {B B₁ B₂ s : ω}

theorem isChargeBound_pure (a : α) : IsChargeBound (pure a : FreeM P α) c B :=
  zero_le

/-- **Budgets add under sequencing.** -/
theorem IsChargeBound.bind [IsOrderedAddMonoid ω] {γ : Type v'} {x : FreeM P α} {f : α → FreeM P γ}
    (hx : IsChargeBound x c B₁ s) (hf : ∀ a, IsChargeBound (f a) c B₂) :
    IsChargeBound (FreeM.bind x f) c (B₁ + B₂) s := by
  refine hx.bind_of_le le_self_add fun a s' hs' => ?_
  have := (hf a).add_left s'
  rw [add_zero] at this
  exact this.mono (add_le_add hs' le_rfl)

/-- A charge bound in spent-amount form is a roll bound whose budget is the amount spent. -/
theorem isChargeBound_iff_isRollBound (x : FreeM P α) (c : P.A → ω) (B s : ω) :
    IsChargeBound x c B s ↔
      s ≤ B ∧ IsRollBound x s (fun a t => t + c a ≤ B) (fun a t => t + c a) := by
  induction x using FreeM.rec generalizing s with
  | pure a => simp
  | liftBind a r ih =>
    rw [isChargeBound_liftBind_iff, isRollBound_liftBind_iff]
    simp only [ih]
    exact ⟨fun h => ⟨le_self_add.trans h.1, h.1, fun b => (h.2 b).2⟩,
      fun h => ⟨h.2.1, fun b => ⟨h.2.1, h.2.2 b⟩⟩⟩

end CanonicalBound

/-! ### Natural-number budgets -/

/-- With natural-number charges, a charge bound is the subtractive roll bound: the remaining
budget `n - s` decreases by `c a` at each call. -/
theorem isChargeBound_iff_isRollBound_tsub (x : FreeM P α) (c : P.A → ℕ) (n s : ℕ) :
    IsChargeBound x c n s ↔
      s ≤ n ∧ IsRollBound x (n - s) (fun a b => c a ≤ b) (fun a b => b - c a) := by
  induction x using FreeM.rec generalizing s with
  | pure a => simp
  | liftBind a r ih =>
    rw [isChargeBound_liftBind_iff, isRollBound_liftBind_iff]
    simp only [ih]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨by omega, by omega, fun b => ?_⟩
      rw [show n - s - c a = n - (s + c a) by omega]
      exact (h₂ b).2
    · rintro ⟨_, hc, h₂⟩
      refine ⟨by omega, fun b => ⟨by omega, ?_⟩⟩
      rw [show n - (s + c a) = n - s - c a by omega]
      exact h₂ b

/-- In a canonically ordered monoid with truncated subtraction and cancellation, such as
`ι → ℕ` or `ℕ × ℕ`, a charge bound is the subtractive roll bound on the remaining budget. -/
theorem isChargeBound_iff_isRollBound_orderedSub {ω : Type w} [AddCommMonoid ω] [PartialOrder ω]
    [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω] [Sub ω] [OrderedSub ω] [AddLeftReflectLE ω]
    (x : FreeM P α) (c : P.A → ω) (B s : ω) :
    IsChargeBound x c B s ↔
      s ≤ B ∧ IsRollBound x (B - s) (fun a b => c a ≤ b) (fun a b => b - c a) := by
  induction x using FreeM.rec generalizing s with
  | pure a => simp
  | liftBind a r ih =>
    rw [isChargeBound_liftBind_iff, isRollBound_liftBind_iff]
    simp only [ih, tsub_tsub]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨le_self_add.trans h₁, (le_tsub_iff_left (le_self_add.trans h₁)).2 h₁,
        fun b => (h₂ b).2⟩
    · rintro ⟨hs, hc, h₂⟩
      have h₁ : s + c a ≤ B := (le_tsub_iff_left hs).1 hc
      exact ⟨h₁, fun b => ⟨h₁, h₂ b⟩⟩

/-- A natural-number charge bound from nothing spent is the subtractive roll bound. -/
theorem isChargeBound_iff_isRollBound_nat (x : FreeM P α) (c : P.A → ℕ) (n : ℕ) :
    IsChargeBound x c n ↔ IsRollBound x n (fun a b => c a ≤ b) (fun a b => b - c a) := by
  simpa using isChargeBound_iff_isRollBound_tsub x c n 0

/-- A unit-charge budget is a total roll bound. -/
theorem isChargeBound_one_iff_isTotalRollBound (x : FreeM P α) (n : ℕ) :
    IsChargeBound x (fun _ => (1 : ℕ)) n ↔ IsTotalRollBound x n := by
  rw [isChargeBound_iff_isRollBound_nat, isTotalRollBound_iff_isRollBound]
  exact isRollBound_congr (fun _ _ => Nat.one_le_iff_ne_zero.trans Nat.pos_iff_ne_zero.symm)
    fun _ _ => rfl

/-! ### Changing the cost type -/

section Transport

variable {ω' : Type w'} [AddCommMonoid ω] [PartialOrder ω] [AddCommMonoid ω'] [PartialOrder ω']
  {c : P.A → ω} {B s : ω}

/-- Charge bounds push forward along monotone additive maps. Indicator, unit and per-kind
charges are pushforwards of one vector charge. -/
theorem IsChargeBound.map {x : FreeM P α} (φ : ω →+o ω') (h : IsChargeBound x c B s) :
    IsChargeBound x (φ ∘ c) (φ B) (φ s) := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact φ.monotone' h
  | liftBind a r ih =>
    refine ⟨?_, fun b => ?_⟩
    · rw [Function.comp_apply, ← map_add]; exact φ.monotone' h.1
    · rw [Function.comp_apply, ← map_add]; exact ih b (h.2 b)

/-- Charge bounds transfer both ways along additive order embeddings, such as `ℕ ↪ ℕ∞`. -/
theorem isChargeBound_comp_iff {x : FreeM P α} (φ : ω →+ ω') (hφ : ∀ a b, φ a ≤ φ b ↔ a ≤ b) :
    IsChargeBound x (φ ∘ c) (φ B) (φ s) ↔ IsChargeBound x c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact hφ s B
  | liftBind a r ih =>
    rw [isChargeBound_liftBind_iff, isChargeBound_liftBind_iff, Function.comp_apply, ← map_add,
      hφ]
    exact and_congr_right fun _ => forall_congr' fun b => ih b

end Transport

/-- Natural-number budgets as budgets in any ordered semiring of characteristic zero, such as `ℕ∞`
or `ℝ≥0∞`. -/
theorem isChargeBound_natCast_iff {R : Type w'} [AddCommMonoidWithOne R] [PartialOrder R]
    [AddLeftMono R] [ZeroLEOneClass R] [CharZero R] {x : FreeM P α} {c : P.A → ℕ} {n s : ℕ} :
    IsChargeBound x (fun a => (c a : R)) n s ↔ IsChargeBound x c n s :=
  isChargeBound_comp_iff (Nat.castAddMonoidHom R) fun _ _ => Nat.cast_le

/-! ### Product and family budgets -/

section Product

variable {ω₁ : Type w} {ω₂ : Type w'} [Add ω₁] [LE ω₁] [Zero ω₁] [Add ω₂] [LE ω₂] [Zero ω₂]

/-- A bound with a pair of charges is a pair of bounds. -/
theorem isChargeBound_prod_iff {x : FreeM P α} {c₁ : P.A → ω₁} {c₂ : P.A → ω₂} {B₁ s₁ : ω₁}
    {B₂ s₂ : ω₂} :
    IsChargeBound x (fun a => (c₁ a, c₂ a)) (B₁, B₂) (s₁, s₂) ↔
      IsChargeBound x c₁ B₁ s₁ ∧ IsChargeBound x c₂ B₂ s₂ := by
  induction x using FreeM.rec generalizing s₁ s₂ with
  | pure a => exact Prod.mk_le_mk
  | liftBind a r ih =>
    simp only [isChargeBound_liftBind_iff, Prod.mk_add_mk, Prod.mk_le_mk, ih]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h⟩
      exact ⟨⟨h₁, fun b => (h b).1⟩, ⟨h₂, fun b => (h b).2⟩⟩
    · rintro ⟨⟨h₁, h₁'⟩, ⟨h₂, h₂'⟩⟩
      exact ⟨⟨h₁, h₂⟩, fun b => ⟨h₁' b, h₂' b⟩⟩

/-- A bound with a family of charges is a family of bounds. Per-index query budgets are the
instance with charges `Pi.single i 1`. -/
theorem isChargeBound_pi_iff {ι : Type*} {ω : ι → Type w} [∀ i, Add (ω i)] [∀ i, LE (ω i)]
    [∀ i, Zero (ω i)] {x : FreeM P α} {c : P.A → ∀ i, ω i} {B s : ∀ i, ω i} :
    IsChargeBound x c B s ↔ ∀ i, IsChargeBound x (fun a => c a i) (B i) (s i) := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact Pi.le_def
  | liftBind a r ih =>
    simp only [isChargeBound_liftBind_iff, Pi.le_def, Pi.add_apply, ih]
    exact ⟨fun h i => ⟨h.1 i, fun b => h.2 b i⟩, fun h => ⟨fun i => (h i).1, fun b i => (h i).2 b⟩⟩

/-- A bound holds in every coordinate of a constant family. -/
theorem IsChargeBound.const (ι : Type*) {x : FreeM P α} {c : P.A → ω₁} {B s : ω₁}
    (h : IsChargeBound x c B s) :
    IsChargeBound x (fun a (_ : ι) => c a) (fun _ => B) (fun _ => s) :=
  isChargeBound_pi_iff.2 fun _ => h

end Product

section Sum

variable {ι : Type*} [Fintype ι] [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]

/-- A bound on a family of charges sums to a bound on the total charge: per-index budgets give a
total budget. -/
theorem IsChargeBound.sum {x : FreeM P α} {c : P.A → ι → ω} {B s : ι → ω}
    (h : IsChargeBound x c B s) :
    IsChargeBound x (fun a => ∑ i, c a i) (∑ i, B i) (∑ i, s i) := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact Finset.sum_le_sum fun i _ => h i
  | liftBind a r ih =>
    have hsum : ∑ i, s i + ∑ i, c a i = ∑ i, (s + c a) i := by
      rw [← Finset.sum_add_distrib]; rfl
    refine ⟨?_, fun b => ?_⟩
    · rw [hsum]; exact Finset.sum_le_sum fun i _ => h.1 i
    · rw [hsum]; exact ih b (h.2 b)

end Sum

/-- Per-index budgets with unit charges are the subtractive per-index roll bound: a call at `a`
needs a positive budget at `a` and spends one unit there. -/
theorem isChargeBound_single_iff_isRollBound [DecidableEq P.A] (x : FreeM P α) (qb : P.A → ℕ) :
    x.IsChargeBound (fun a => Pi.single a 1) qb ↔
      x.IsRollBound qb (fun a b => 0 < b a) (fun a b => Function.update b a (b a - 1)) := by
  rw [isChargeBound_iff_isRollBound_orderedSub, tsub_zero]
  simp only [zero_le, true_and]
  refine isRollBound_congr (fun a b => ⟨fun h => ?_, fun h j => ?_⟩) fun a b => ?_
  · simpa [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using h a
  · by_cases hj : j = a
    · subst hj; simpa [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using h
    · simp [hj]
  · funext j
    by_cases hj : j = a
    · subst hj; simp
    · simp [hj]

/-! ### Lenses and free handlers -/

section Transfer

variable {Q : PFunctor.{uA₂, uB₂}} [AddCommMonoid ω] [PartialOrder ω] {B s : ω}

/-- A bound on `x` with the charge pulled back along `l` bounds the relabelled program. -/
theorem IsChargeBound.mapLens (l : Lens P Q) {x : FreeM P α} {c : Q.A → ω}
    (h : IsChargeBound x (c ∘ l.toFunA) B s) : IsChargeBound (x.mapLens l) c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact h
  | liftBind a r ih =>
    rw [FreeM.mapLens_liftBind, isChargeBound_liftBind_iff]
    exact ⟨h.1, fun d => ih _ (h.2 _)⟩

/-- When every answer of the target is reached by the lens, the bounds agree. -/
theorem isChargeBound_mapLens_iff (l : Lens P Q) (hl : ∀ a, Function.Surjective (l.toFunB a))
    {x : FreeM P α} {c : Q.A → ω} :
    IsChargeBound (x.mapLens l) c B s ↔ IsChargeBound x (c ∘ l.toFunA) B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact Iff.rfl
  | liftBind a r ih =>
    rw [FreeM.mapLens_liftBind, isChargeBound_liftBind_iff, isChargeBound_liftBind_iff]
    refine and_congr_right fun _ => ⟨fun h b => ?_, fun h d => (ih _).2 (h _)⟩
    obtain ⟨d, rfl⟩ := hl a b
    exact (ih _).1 (h d)

end Transfer

section Handler

variable {Q : PFunctor.{uA₂, uB}} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
  {α : Type uB} {B s : ω}

/-- **Free-handler transfer.** If the implementation of each call at `a` stays within `c a` under
the target charge `d`, then simulating a program within `B` under `c` stays within `B` under
`d`. -/
theorem IsChargeBound.liftM (handler : (a : P.A) → FreeM Q (P.B a)) {c : P.A → ω} {d : Q.A → ω}
    (hstep : ∀ a, IsChargeBound (handler a) d (c a)) {x : FreeM P α}
    (hx : IsChargeBound x c B s) : IsChargeBound (x.liftM handler) d B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact hx
  | liftBind a r ih =>
    change IsChargeBound (FreeM.bind (handler a) fun b => (r b).liftM handler) d B s
    have hh := (hstep a).add_left s
    rw [add_zero] at hh
    exact hh.bind_of_le hx.1 fun b s' hs' => (ih b (hx.2 b)).mono_spent hs'

/-- **Uniform-step transfer.** If every implementation stays within `k`, a program making at most
`n` calls is simulated within `n • k`. -/
theorem IsChargeBound.liftM_nsmul [CanonicallyOrderedAdd ω] (handler : (a : P.A) → FreeM Q (P.B a))
    {d : Q.A → ω} {k : ω} (hstep : ∀ a, (handler a).IsChargeBound d k) {x : FreeM P α} {n : ℕ}
    (hx : x.IsChargeBound (fun _ => (1 : ℕ)) n) : (x.liftM handler).IsChargeBound d (n • k) := by
  let scale : ℕ →+o ω :=
    { toFun := fun m => m • k, map_zero' := zero_nsmul k, map_add' := fun a b => add_nsmul k a b,
      monotone' := fun _ _ h => nsmul_le_nsmul_left zero_le h }
  have h := hx.map scale
  rw [map_zero] at h
  refine h.liftM handler fun a => ?_
  change (handler a).IsChargeBound d ((1 : ℕ) • k)
  rw [one_nsmul]
  exact hstep a

end Handler

/-! ### Restricted answers

A budget or roll bound can restrict the answers whose continuations it constrains, through a
relation `allows : (a : P.A) → P.B a → Prop`, as `demonicUnder` restricts the demonic reading. A
handler may return only some answers to a call, for example those in the support of a sampled
distribution; the continuations at the other answers are never run, so they need no budget. With
every answer allowed, the restricted bounds are the unrestricted ones (`isRollBoundUnder_true_iff`,
`isChargeBoundUnder_true_iff`), and a charge bound is a roll bound under the same restriction
(`isChargeBoundUnder_iff_isRollBoundUnder`). -/

section Under

variable {allows allows' : (a : P.A) → P.B a → Prop}

/-- The roll bound along allowed answers: `canRoll` must hold at each call, and the state is
updated by `cost`, only along the answers that `allows` admits. -/
def IsRollBoundUnder {σ : Type w} (x : FreeM P α) (b : σ) (canRoll : P.A → σ → Prop)
    (cost : P.A → σ → σ) (allows : (a : P.A) → P.B a → Prop) : Prop :=
  wpFold (OpSpec.rollUnder canRoll cost allows) x (fun _ _ => True) b

theorem isRollBoundUnder_liftBind_iff {σ : Type w} (a : P.A) (r : P.B a → FreeM P α) (b : σ)
    (canRoll : P.A → σ → Prop) (cost : P.A → σ → σ) :
    IsRollBoundUnder (FreeM.liftBind a r) b canRoll cost allows ↔
      canRoll a b ∧ ∀ y, allows a y → IsRollBoundUnder (r y) (cost a b) canRoll cost allows :=
  Iff.rfl

/-- With every answer allowed, the restricted roll bound is the roll bound. -/
theorem isRollBoundUnder_true_iff {σ : Type w} (x : FreeM P α) (b : σ)
    (canRoll : P.A → σ → Prop) (cost : P.A → σ → σ) :
    IsRollBoundUnder x b canRoll cost (fun _ _ => True) ↔ IsRollBound x b canRoll cost := by
  rw [isRollBound_iff_wpFold, IsRollBoundUnder, OpSpec.rollUnder_true]

variable [Add ω] [LE ω] [Zero ω] {c : P.A → ω} {B s : ω}

/-- `x.IsChargeBoundUnder c allows B s`: with `s` already spent, every call of `x` keeps the amount
spent at most `B`, and every leaf is reached within `B`, along the answers that `allows` admits. -/
def IsChargeBoundUnder (x : FreeM P α) (c : P.A → ω) (allows : (a : P.A) → P.B a → Prop) (B : ω)
    (spent : ω := 0) : Prop :=
  wpFold (OpSpec.budgetUnder c B allows) x (fun _ s => s ≤ B) spent

@[simp, freeM_unfold]
theorem isChargeBoundUnder_pure_iff (a : α) :
    IsChargeBoundUnder (pure a : FreeM P α) c allows B s ↔ s ≤ B :=
  Iff.rfl

@[freeM_unfold]
theorem isChargeBoundUnder_liftBind_iff (a : P.A) (r : P.B a → FreeM P α) :
    IsChargeBoundUnder (FreeM.liftBind a r) c allows B s ↔
      s + c a ≤ B ∧ ∀ b, allows a b → IsChargeBoundUnder (r b) c allows B (s + c a) :=
  Iff.rfl

@[simp]
theorem isChargeBoundUnder_lift_bind_iff (a : P.A) (r : P.B a → FreeM P α) :
    IsChargeBoundUnder ((FreeM.lift a).bind (α := no_index (P.B a)) r) c allows B s ↔
      s + c a ≤ B ∧ ∀ b, allows a b → IsChargeBoundUnder (r b) c allows B (s + c a) :=
  Iff.rfl

/-- With every answer allowed, the restricted charge bound is the charge bound. -/
theorem isChargeBoundUnder_true_iff (x : FreeM P α) :
    IsChargeBoundUnder x c (fun _ _ => True) B s ↔ IsChargeBound x c B s := by
  rw [IsChargeBoundUnder, OpSpec.budgetUnder_true]
  rfl

/-- A charge bound holds under every restriction of the answers. -/
theorem IsChargeBound.under {x : FreeM P α} (h : IsChargeBound x c B s)
    (allows : (a : P.A) → P.B a → Prop) : IsChargeBoundUnder x c allows B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact h
  | liftBind a r ih => exact ⟨h.1, fun b _ => ih b (h.2 b)⟩

/-- Allowing fewer answers keeps a program within budget. -/
theorem IsChargeBoundUnder.mono_allows {x : FreeM P α} (h : IsChargeBoundUnder x c allows B s)
    (hle : ∀ a b, allows' a b → allows a b) : IsChargeBoundUnder x c allows' B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact h
  | liftBind a r ih => exact ⟨h.1, fun b hb => ih b (h.2 b (hle a b hb))⟩

/-- `isChargeBoundUnder_lift_bind_iff` when results and directions share a universe. -/
@[simp]
theorem isChargeBoundUnder_lift_bind_iff' {α : Type uB} (a : P.A) (r : P.B a → FreeM P α) :
    IsChargeBoundUnder (Bind.bind (α := no_index (P.B a)) (FreeM.lift a) r) c allows B s ↔
      s + c a ≤ B ∧ ∀ b, allows a b → IsChargeBoundUnder (r b) c allows B (s + c a) :=
  Iff.rfl

@[simp]
theorem isChargeBoundUnder_lift_iff (a : P.A) :
    IsChargeBoundUnder (α := no_index (P.B a)) (FreeM.lift a) c allows B s ↔ s + c a ≤ B :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ => h⟩⟩

/-- Sequencing, exactly: the continuation starts from whatever amount each allowed branch of `x`
has spent. -/
theorem isChargeBoundUnder_bind_iff {γ : Type v'} (x : FreeM P α) (f : α → FreeM P γ) :
    IsChargeBoundUnder (FreeM.bind x f) c allows B s ↔
      wpFold (OpSpec.budgetUnder c B allows) x
        (fun a s' => IsChargeBoundUnder (f a) c allows B s') s := by
  unfold IsChargeBoundUnder
  rw [wpFold_bind']

@[simp]
theorem isChargeBoundUnder_bind_iff' (x : FreeM P α) (f : α → FreeM P β) :
    IsChargeBoundUnder (x >>= f) c allows B s ↔
      wpFold (OpSpec.budgetUnder c B allows) x
        (fun a s' => IsChargeBoundUnder (f a) c allows B s') s :=
  isChargeBoundUnder_bind_iff x f

@[simp]
theorem isChargeBoundUnder_ite (p : Prop) [Decidable p] (x y : FreeM P α) :
    IsChargeBoundUnder (if p then x else y) c allows B s ↔
      if p then IsChargeBoundUnder x c allows B s else IsChargeBoundUnder y c allows B s := by
  split <;> rfl

@[simp]
theorem isChargeBoundUnder_map_iff {γ : Type v'} (f : α → γ) (x : FreeM P α) :
    IsChargeBoundUnder (FreeM.map f x) c allows B s ↔ IsChargeBoundUnder x c allows B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact Iff.rfl
  | liftBind a r ih =>
    exact and_congr_right fun _ => forall_congr' fun b => imp_congr_right fun _ => ih b

@[simp]
theorem isChargeBoundUnder_map_iff' (f : α → β) (x : FreeM P α) :
    IsChargeBoundUnder (f <$> x) c allows B s ↔ IsChargeBoundUnder x c allows B s :=
  isChargeBoundUnder_map_iff f x

end Under

section OrderedUnder

variable [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] {c : P.A → ω} {B B' s s' : ω}
  {allows : (a : P.A) → P.B a → Prop}

omit [IsOrderedAddMonoid ω] in
/-- A larger budget keeps a program within budget. -/
theorem IsChargeBoundUnder.mono {x : FreeM P α} (h : IsChargeBoundUnder x c allows B s)
    (hB : B ≤ B') : IsChargeBoundUnder x c allows B' s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact h.trans hB
  | liftBind a r ih => exact ⟨h.1.trans hB, fun b hb => ih b (h.2 b hb)⟩

omit [IsOrderedAddMonoid ω] in
/-- **Sequencing along a demonic postcondition.** If `x` stays within `L ≤ B`, every result `x` can
return along allowed answers satisfies `post`, and from any amount at most `L` each continuation at
such a result stays within `B`, then `x >>= f` stays within `B`. -/
theorem IsChargeBoundUnder.bind_of_le {γ : Type v'} {x : FreeM P α} {f : α → FreeM P γ} {L : ω}
    {post : α → Prop} (hx : IsChargeBoundUnder x c allows L s)
    (hpost : wpFold (OpSpec.demonicUnder allows) x post) (hL : L ≤ B)
    (hf : ∀ a, post a → ∀ s', s' ≤ L → IsChargeBoundUnder (f a) c allows B s') :
    IsChargeBoundUnder (FreeM.bind x f) c allows B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact hf a hpost s hx
  | liftBind a r ih => exact ⟨hx.1.trans hL, fun b hb => ih b (hx.2 b hb) (hpost b hb)⟩


/-- Starting from less spent keeps a program within budget. -/
theorem IsChargeBoundUnder.mono_spent {x : FreeM P α} (h : IsChargeBoundUnder x c allows B s)
    (hs : s' ≤ s) : IsChargeBoundUnder x c allows B s' := by
  induction x using FreeM.rec generalizing s s' with
  | pure a => exact hs.trans h
  | liftBind a r ih =>
    have hs' : s' + c a ≤ s + c a := add_le_add hs le_rfl
    exact ⟨hs'.trans h.1, fun b hb => ih b (h.2 b hb) hs'⟩

/-- Shifting the spent amount shifts the budget. -/
theorem IsChargeBoundUnder.add_left {x : FreeM P α} (h : IsChargeBoundUnder x c allows B s)
    (t : ω) : IsChargeBoundUnder x c allows (t + B) (t + s) := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact add_le_add le_rfl h
  | liftBind a r ih =>
    refine ⟨?_, fun b hb => ?_⟩
    · rw [add_assoc]; exact add_le_add le_rfl h.1
    · rw [add_assoc]; exact ih b (h.2 b hb)

/-- **Transfer through a free handler with restricted answers.** If each implementation stays
within its call's charge along the target's allowed answers, and every result it can return along
those answers is an allowed source answer, then simulating a program within `B` along the source's
allowed answers stays within `B` along the target's. -/
theorem IsChargeBoundUnder.liftM {Q : PFunctor.{uA₂, uB}} {γ : Type uB}
    (handler : (a : P.A) → FreeM Q (P.B a)) {d : Q.A → ω} {allowsQ : (q : Q.A) → Q.B q → Prop}
    (hstep : ∀ a, IsChargeBoundUnder (handler a) d allowsQ (c a))
    (hout : ∀ a, wpFold (OpSpec.demonicUnder allowsQ) (handler a) (allows a))
    {x : FreeM P γ} (hx : IsChargeBoundUnder x c allows B s) :
    IsChargeBoundUnder (x.liftM handler) d allowsQ B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact hx
  | liftBind a r ih =>
    change IsChargeBoundUnder (FreeM.bind (handler a) fun b => (r b).liftM handler) d allowsQ B s
    have hh := (hstep a).add_left s
    rw [add_zero] at hh
    exact hh.bind_of_le (hout a) hx.1 fun b hb s' hs' => (ih b (hx.2 b hb)).mono_spent hs'

end OrderedUnder

section CanonicalUnder

variable [AddCommMonoid ω] [PartialOrder ω] [CanonicallyOrderedAdd ω] {c : P.A → ω} {B s : ω}
  {allows : (a : P.A) → P.B a → Prop}

/-- A restricted charge bound in spent-amount form is a restricted roll bound whose state is the
amount spent. -/
theorem isChargeBoundUnder_iff_isRollBoundUnder (x : FreeM P α) :
    IsChargeBoundUnder x c allows B s ↔
      s ≤ B ∧ IsRollBoundUnder x s (fun a t => t + c a ≤ B) (fun a t => t + c a) allows := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | liftBind a r ih =>
    rw [isChargeBoundUnder_liftBind_iff, isRollBoundUnder_liftBind_iff]
    simp only [ih]
    exact ⟨fun h => ⟨le_self_add.trans h.1, h.1, fun b hb => (h.2 b hb).2⟩,
      fun h => ⟨h.2.1, fun b hb => ⟨h.2.1, h.2.2 b hb⟩⟩⟩

end CanonicalUnder

end FreeM

end PFunctor
