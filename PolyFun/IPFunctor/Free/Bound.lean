/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Indexed
public import PolyFun.PFunctor.Bound

/-!
# Roll Bounds for the State-Indexed Free Monad

`IPFunctor.IFreeM.IsRollBound x budget canRoll cost` is the state-indexed analogue of
`PFunctor.FreeM.IsRollBound`. It bounds the `liftBind` constructors that a tree
`x : IFreeM P X s` unfolds along every branch, and is parameterized by:
- `B` — the budget type, which does not depend on the state;
- `budget : B` — the initial budget;
- `canRoll : (s : I) → P.A s → B → Prop` — whether a `liftBind` at shape `a : P.A s` is allowed
  under budget `b`;
- `cost : (s : I) → P.A s → B → B` — how the budget is updated after that `liftBind`.

`pure` satisfies any bound, and `liftBind a r` at state `s` satisfies the bound when
`canRoll s a b` holds and each continuation `r y` satisfies the bound at `cost s a b`. The bound
is the plain `PFunctor.FreeM.IsRollBound` of the Σ-bundled erasure `IFreeM.toSigmaFreeM`, whose
positions carry the state (`isRollBound_toSigmaFreeM_iff`).

Two specializations have natural-number budgets that add under `IFreeM.bind`, including binds
whose continuation changes the universe of the leaf family:
* `IsChargeBound x c n`: along every branch, the charges `c s a` of the rolled shapes add up to
  at most `n`. This is the subtractive per-position budget of
  `PFunctor.FreeM.isRollBound_iff_wpFold_charge`, with a charge that may read the state.
* `IsTotalRollBound x n`: every branch rolls at most `n` times. It is the unit charge bound.

`FreeM` and `FreeM₂` inherit the predicates through their defining `IFreeM` trees; the
abbreviations `FreeM.IsRollBound`, `FreeM₂.IsRollBound` and their specializations provide dot
notation on those types.
-/

public section

universe uI uA uB v w

namespace IPFunctor.IFreeM

variable {I : Type uI} {P : Endo.{uI, uA, uB} I} {X : I → Type v} {B : Type*} {s : I}

/-- Generalized roll bound on `IFreeM P X` parameterized by a budget type `B`, a validity check
`canRoll`, and a cost function `cost`, both of which see the state of the rolled shape. `pure`
satisfies any bound; `liftBind a r` at state `s` satisfies the bound when `canRoll s a b` holds
and every continuation satisfies the bound at `cost s a b`. -/
@[expose] def IsRollBound (x : IFreeM P X s) (budget : B)
    (canRoll : (s : I) → P.A s → B → Prop) (cost : (s : I) → P.A s → B → B) : Prop :=
  (toSigmaFreeM P x).IsRollBound budget (fun a => canRoll a.1 a.2) (fun a => cost a.1 a.2)

variable {canRoll : (s : I) → P.A s → B → Prop} {cost : (s : I) → P.A s → B → B}

@[simp, grind .]
lemma isRollBound_pure (x : X s) (b : B) :
    IsRollBound (IFreeM.pure (P := P) x) b canRoll cost := trivial

@[simp, grind =]
lemma isRollBound_liftBind_iff (a : P.A s) (r : (y : P.B s a) → IFreeM P X (P.src s a y))
    (b : B) :
    IsRollBound (IFreeM.liftBind a r) b canRoll cost ↔
      canRoll s a b ∧ ∀ y, IsRollBound (r y) (cost s a b) canRoll cost :=
  Iff.rfl

@[simp, grind =]
lemma isRollBound_imap_iff {Y : I → Type w} (f : ∀ s, X s → Y s) (x : IFreeM P X s) (b : B) :
    IsRollBound (x.imap f) b canRoll cost ↔ IsRollBound x b canRoll cost := by
  unfold IsRollBound
  rw [toSigmaFreeM_imap, PFunctor.FreeM.isRollBound_map_iff]

/-- Transport along an equality of states, such as the source-index law of a lens, does not
change the bound. -/
@[simp]
lemma isRollBound_cast {s' : I} (h : s = s') (x : IFreeM P X s) (b : B) :
    IsRollBound (h ▸ x) b canRoll cost ↔ IsRollBound x b canRoll cost := by
  subst h
  rfl

lemma isRollBound_congr {x : IFreeM P X s} {b : B}
    {canRoll₁ canRoll₂ : (s : I) → P.A s → B → Prop} {cost₁ cost₂ : (s : I) → P.A s → B → B}
    (hcan : ∀ s a b, canRoll₁ s a b ↔ canRoll₂ s a b)
    (hcost : ∀ s a b, cost₁ s a b = cost₂ s a b) :
    IsRollBound x b canRoll₁ cost₁ ↔ IsRollBound x b canRoll₂ cost₂ :=
  PFunctor.FreeM.isRollBound_congr (fun a => hcan a.1 a.2) (fun a => hcost a.1 a.2)

/-- Project an `IsRollBound` along a budget projection `proj : B → B'`, as
`PFunctor.FreeM.IsRollBound.proj`:
* `h_can` — a step allowed in the source is allowed in the projection;
* `h_cost` — the projection commutes with the cost step on the allowed branch. -/
lemma IsRollBound.proj {B' : Type*} (proj : B → B') {x : IFreeM P X s} {b : B}
    {canRoll' : (s : I) → P.A s → B' → Prop} {cost' : (s : I) → P.A s → B' → B'}
    (h_can : ∀ s a b', canRoll s a b' → canRoll' s a (proj b'))
    (h_cost : ∀ s a b', canRoll s a b' → proj (cost s a b') = cost' s a (proj b'))
    (h : IsRollBound x b canRoll cost) :
    IsRollBound x (proj b) canRoll' cost' :=
  PFunctor.FreeM.IsRollBound.proj proj (fun a => h_can a.1 a.2)
    (fun a => h_cost a.1 a.2) h

/-- A roll bound is monotone in the budget for any relation `R` that is preserved by the
validity check and by the cost step. With `R := (· ≤ ·)` this is budget enlargement. -/
lemma IsRollBound.mono_of_rel (R : B → B → Prop) {x : IFreeM P X s} {b b' : B}
    (h_can : ∀ s a b b', R b b' → canRoll s a b → canRoll s a b')
    (h_cost : ∀ s a b b', R b b' → canRoll s a b → R (cost s a b) (cost s a b'))
    (h : IsRollBound x b canRoll cost) (hb : R b b') :
    IsRollBound x b' canRoll cost :=
  PFunctor.FreeM.IsRollBound.mono_of_rel R (fun a => h_can a.1 a.2)
    (fun a => h_cost a.1 a.2) h hb

/-- Weakening the validity check, at a fixed cost function. -/
lemma IsRollBound.mono_canRoll {canRoll' : (s : I) → P.A s → B → Prop}
    {x : IFreeM P X s} {b : B} (h_can : ∀ s a b, canRoll s a b → canRoll' s a b)
    (h : IsRollBound x b canRoll cost) : IsRollBound x b canRoll' cost :=
  h.proj id h_can fun _ _ _ _ => rfl

/-- Generic bind composition for `IsRollBound`, as `PFunctor.FreeM.isRollBound_bind`. The
continuation's leaf family may live in another universe. The side conditions are universally
quantified so they survive recursion:
* `h_can` — extending a validated budget on either side via `combine` keeps the roll valid;
* `h_cost` — `cost` distributes left and right over `combine` on validated budgets. -/
lemma isRollBound_bind {Y : I → Type w} {x : IFreeM P X s} {g : ∀ s', X s' → IFreeM P Y s'}
    (combine : B → B → B) {b₁ b₂ : B}
    (h_can : ∀ s a b₁' b₂' b, canRoll s a b →
      canRoll s a (combine b₁' b) ∧ canRoll s a (combine b b₂'))
    (h_cost : ∀ s a b₁' b₂' b, canRoll s a b →
      combine b₁' (cost s a b) = cost s a (combine b₁' b) ∧
      cost s a (combine b b₂') = combine (cost s a b) b₂')
    (h₁ : IsRollBound x b₁ canRoll cost)
    (h₂ : ∀ s' y, IsRollBound (g s' y) b₂ canRoll cost) :
    IsRollBound (x.bind g) (combine b₁ b₂) canRoll cost := by
  unfold IsRollBound
  rw [toSigmaFreeM_bind]
  exact PFunctor.FreeM.isRollBound_bind combine (fun a => h_can a.1 a.2)
    (fun a => h_cost a.1 a.2) h₁ (fun value => h₂ value.1 value.2)

/-! ## Σ-bundled erasure -/

/-- The indexed roll bound is the plain roll bound of the Σ-bundled erasure, whose positions
`Σ s, P.A s` carry the state of each rolled shape. -/
theorem isRollBound_toSigmaFreeM_iff (x : IFreeM P X s) (b : B) :
    (toSigmaFreeM P x).IsRollBound b (fun a => canRoll a.1 a.2) (fun a => cost a.1 a.2) ↔
      IsRollBound x b canRoll cost :=
  Iff.rfl

/-! ## Charge bounds -/

/-- A charge bound: along every branch of `x`, the charges `c s a` of the rolled shapes add up
to at most `n`. A roll at `a : P.A s` is allowed when `c s a` fits in the remaining budget, which
then decreases by `c s a`. -/
@[expose] def IsChargeBound (x : IFreeM P X s) (c : (s : I) → P.A s → ℕ) (n : ℕ) : Prop :=
  IsRollBound x n (fun s a b => c s a ≤ b) (fun s a b => b - c s a)

variable {c : (s : I) → P.A s → ℕ}

theorem isChargeBound_iff_isRollBound (x : IFreeM P X s) (n : ℕ) :
    IsChargeBound x c n ↔ IsRollBound x n (fun s a b => c s a ≤ b) (fun s a b => b - c s a) :=
  Iff.rfl

@[simp, grind .]
lemma isChargeBound_pure (x : X s) (n : ℕ) : IsChargeBound (IFreeM.pure (P := P) x) c n :=
  trivial

@[simp, grind =]
lemma isChargeBound_liftBind_iff (a : P.A s) (r : (y : P.B s a) → IFreeM P X (P.src s a y))
    (n : ℕ) :
    IsChargeBound (IFreeM.liftBind a r) c n ↔
      c s a ≤ n ∧ ∀ y, IsChargeBound (r y) c (n - c s a) :=
  Iff.rfl

/-- A charge bound remains valid when its budget is increased. -/
lemma IsChargeBound.mono {x : IFreeM P X s} {n₁ n₂ : ℕ} (h : IsChargeBound x c n₁)
    (hle : n₁ ≤ n₂) : IsChargeBound x c n₂ :=
  IsRollBound.mono_of_rel (· ≤ ·) (fun _ _ _ _ => le_trans') (fun _ _ _ _ _ _ => by grind)
    h hle

/-- Charge bounds add under sequencing, also when the continuation changes the universe of the
leaf family. -/
lemma isChargeBound_bind {Y : I → Type w} {x : IFreeM P X s} {g : ∀ s', X s' → IFreeM P Y s'}
    {n₁ n₂ : ℕ} (h₁ : IsChargeBound x c n₁) (h₂ : ∀ s' y, IsChargeBound (g s' y) c n₂) :
    IsChargeBound (x.bind g) c (n₁ + n₂) := by
  refine isRollBound_bind (· + ·) ?_ ?_ h₁ h₂ <;> grind

/-- Multiplying both the charge and the budget by a natural number preserves a bound. -/
lemma IsChargeBound.mul {x : IFreeM P X s} {n : ℕ} (h : x.IsChargeBound c n) (k : ℕ) :
    x.IsChargeBound (fun s a => k * c s a) (k * n) := by
  induction x using IFreeM.inductionOn generalizing n with
  | pure _ _ => exact isChargeBound_pure _ _
  | liftBind s a next ih =>
      rw [isChargeBound_liftBind_iff]
      refine ⟨Nat.mul_le_mul_left k h.1, fun b => ?_⟩
      simpa only [Nat.mul_sub_left_distrib] using ih b (h.2 b)

/-! ## Total roll bounds -/

/-- A total roll bound: `x` encounters at most `n` `IFreeM.liftBind` constructors along every
branch. Each roll consumes one unit of a natural-number budget, independently of its state and
shape. -/
@[expose] def IsTotalRollBound (x : IFreeM P X s) (n : ℕ) : Prop :=
  IsRollBound x n (fun _ _ b => 0 < b) (fun _ _ b => b - 1)

theorem isTotalRollBound_iff_isRollBound (x : IFreeM P X s) (n : ℕ) :
    IsTotalRollBound x n ↔ IsRollBound x n (fun _ _ b => 0 < b) (fun _ _ b => b - 1) :=
  Iff.rfl

/-- The total roll bound is the unit charge bound, definitionally. -/
theorem isTotalRollBound_iff_isChargeBound (x : IFreeM P X s) (n : ℕ) :
    IsTotalRollBound x n ↔ IsChargeBound x (fun _ _ => 1) n :=
  Iff.rfl

@[simp, grind .]
lemma isTotalRollBound_pure (x : X s) (n : ℕ) : IsTotalRollBound (IFreeM.pure (P := P) x) n :=
  trivial

@[simp, grind =]
lemma isTotalRollBound_liftBind_iff (a : P.A s) (r : (y : P.B s a) → IFreeM P X (P.src s a y))
    (n : ℕ) :
    IsTotalRollBound (IFreeM.liftBind a r) n ↔ 0 < n ∧ ∀ y, IsTotalRollBound (r y) (n - 1) :=
  Iff.rfl

/-- A total roll bound remains valid when its budget is increased. -/
lemma IsTotalRollBound.mono {x : IFreeM P X s} {n₁ n₂ : ℕ} (h : IsTotalRollBound x n₁)
    (hle : n₁ ≤ n₂) : IsTotalRollBound x n₂ :=
  IsChargeBound.mono h hle

/-- Total roll bounds add under sequencing, also when the continuation changes the universe of
the leaf family. -/
lemma isTotalRollBound_bind {Y : I → Type w} {x : IFreeM P X s}
    {g : ∀ s', X s' → IFreeM P Y s'} {n₁ n₂ : ℕ} (h₁ : IsTotalRollBound x n₁)
    (h₂ : ∀ s' y, IsTotalRollBound (g s' y) n₂) :
    IsTotalRollBound (x.bind g) (n₁ + n₂) :=
  isChargeBound_bind h₁ h₂

/-- The total roll bound is the total roll bound of the Σ-bundled erasure. -/
theorem isTotalRollBound_toSigmaFreeM_iff (x : IFreeM P X s) (n : ℕ) :
    (toSigmaFreeM P x).IsTotalRollBound n ↔ IsTotalRollBound x n :=
  isRollBound_toSigmaFreeM_iff (canRoll := fun _ _ b => 0 < b) (cost := fun _ _ b => b - 1) x n

end IPFunctor.IFreeM

/-! ## Constant-family specialization -/

namespace IPFunctor.FreeM

variable {I : Type uI} {P : Endo.{uI, uA, uB} I} {α β : Type v} {B : Type*} {s : I}
  {canRoll : (s : I) → P.A s → B → Prop} {cost : (s : I) → P.A s → B → B}

/-- `IFreeM.IsRollBound` on the constant-family tree underlying `x`. -/
abbrev IsRollBound (x : FreeM P s α) (b : B) (canRoll : (s : I) → P.A s → B → Prop)
    (cost : (s : I) → P.A s → B → B) : Prop :=
  IFreeM.IsRollBound (X := fun _ => α) x b canRoll cost

/-- `IFreeM.IsChargeBound` on the constant-family tree underlying `x`. -/
abbrev IsChargeBound (x : FreeM P s α) (c : (s : I) → P.A s → ℕ) (n : ℕ) : Prop :=
  IFreeM.IsChargeBound (X := fun _ => α) x c n

/-- `IFreeM.IsTotalRollBound` on the constant-family tree underlying `x`. -/
abbrev IsTotalRollBound (x : FreeM P s α) (n : ℕ) : Prop :=
  IFreeM.IsTotalRollBound (X := fun _ => α) x n

@[simp]
lemma isRollBound_pure (x : α) (b : B) :
    (FreeM.pure (P := P) s x).IsRollBound b canRoll cost :=
  trivial

@[simp]
lemma isRollBound_liftBind_iff (a : P.A s) (r : (y : P.B s a) → FreeM P (P.src s a y) α)
    (b : B) :
    (FreeM.liftBind s a r).IsRollBound b canRoll cost ↔
      canRoll s a b ∧ ∀ y, (r y).IsRollBound (cost s a b) canRoll cost :=
  Iff.rfl

lemma isRollBound_bind {x : FreeM P s α} {g : (s' : I) → α → FreeM P s' β}
    (combine : B → B → B) {b₁ b₂ : B}
    (h_can : ∀ s a b₁' b₂' b, canRoll s a b →
      canRoll s a (combine b₁' b) ∧ canRoll s a (combine b b₂'))
    (h_cost : ∀ s a b₁' b₂' b, canRoll s a b →
      combine b₁' (cost s a b) = cost s a (combine b₁' b) ∧
      cost s a (combine b b₂') = combine (cost s a b) b₂')
    (h₁ : x.IsRollBound b₁ canRoll cost) (h₂ : ∀ s' y, (g s' y).IsRollBound b₂ canRoll cost) :
    (x.bind g).IsRollBound (combine b₁ b₂) canRoll cost :=
  IFreeM.isRollBound_bind combine h_can h_cost h₁ h₂

lemma isChargeBound_bind {c : (s : I) → P.A s → ℕ} {x : FreeM P s α}
    {g : (s' : I) → α → FreeM P s' β} {n₁ n₂ : ℕ} (h₁ : x.IsChargeBound c n₁)
    (h₂ : ∀ s' y, (g s' y).IsChargeBound c n₂) :
    (x.bind g).IsChargeBound c (n₁ + n₂) :=
  IFreeM.isChargeBound_bind h₁ h₂

lemma isTotalRollBound_bind {x : FreeM P s α} {g : (s' : I) → α → FreeM P s' β} {n₁ n₂ : ℕ}
    (h₁ : x.IsTotalRollBound n₁) (h₂ : ∀ s' y, (g s' y).IsTotalRollBound n₂) :
    (x.bind g).IsTotalRollBound (n₁ + n₂) :=
  IFreeM.isTotalRollBound_bind h₁ h₂

/-- The constant-family bound is the plain roll bound of `FreeM.toSigmaFreeM`. -/
theorem isRollBound_toSigmaFreeM_iff (x : FreeM P s α) (b : B) :
    (toSigmaFreeM P x).IsRollBound b (fun a => canRoll a.1 a.2) (fun a => cost a.1 a.2) ↔
      x.IsRollBound b canRoll cost := by
  induction x using FreeM.inductionOn generalizing b with
  | pure _ _ => exact iff_of_true trivial trivial
  | liftBind _ _ _ ih => exact and_congr_right fun _ => forall_congr' fun y => ih y _

/-- The constant-family total roll bound is the total roll bound of `FreeM.toSigmaFreeM`. -/
theorem isTotalRollBound_toSigmaFreeM_iff (x : FreeM P s α) (n : ℕ) :
    (toSigmaFreeM P x).IsTotalRollBound n ↔ x.IsTotalRollBound n :=
  isRollBound_toSigmaFreeM_iff (canRoll := fun _ _ b => 0 < b) (cost := fun _ _ b => b - 1) x n

end IPFunctor.FreeM

/-! ## Terminal-state-marker specialization -/

namespace IPFunctor.FreeM₂

variable {I : Type uI} {P : Endo.{uI, uA, uB} I} {α β : Type v} {B : Type*} {s t u : I}
  {canRoll : (s : I) → P.A s → B → Prop} {cost : (s : I) → P.A s → B → B}

/-- `IFreeM.IsRollBound` on the terminal-state-marker tree underlying `x`. -/
abbrev IsRollBound (x : FreeM₂ P s t α) (b : B) (canRoll : (s : I) → P.A s → B → Prop)
    (cost : (s : I) → P.A s → B → B) : Prop :=
  IFreeM.IsRollBound (X := fun u => PSigma fun _ : u = t => α) x b canRoll cost

/-- `IFreeM.IsChargeBound` on the terminal-state-marker tree underlying `x`. -/
abbrev IsChargeBound (x : FreeM₂ P s t α) (c : (s : I) → P.A s → ℕ) (n : ℕ) : Prop :=
  IFreeM.IsChargeBound (X := fun u => PSigma fun _ : u = t => α) x c n

/-- `IFreeM.IsTotalRollBound` on the terminal-state-marker tree underlying `x`. -/
abbrev IsTotalRollBound (x : FreeM₂ P s t α) (n : ℕ) : Prop :=
  IFreeM.IsTotalRollBound (X := fun u => PSigma fun _ : u = t => α) x n

@[simp]
lemma isRollBound_pure (x : α) (b : B) :
    (FreeM₂.pure (P := P) (s := s) x).IsRollBound b canRoll cost :=
  trivial

@[simp]
lemma isRollBound_liftBind_iff (a : P.A s) (r : (y : P.B s a) → FreeM₂ P (P.src s a y) t α)
    (b : B) :
    (FreeM₂.liftBind a r).IsRollBound b canRoll cost ↔
      canRoll s a b ∧ ∀ y, (r y).IsRollBound (cost s a b) canRoll cost :=
  Iff.rfl

/-- Roll bounds compose under the `IndexedMonad` bind of `FreeM₂`. The leaf payload carries the
equality witness that the generic `IFreeM` lemma discharges. -/
lemma isRollBound_bind {x : FreeM₂ P s t α} {g : α → FreeM₂ P t u β}
    (combine : B → B → B) {b₁ b₂ : B}
    (h_can : ∀ s a b₁' b₂' b, canRoll s a b →
      canRoll s a (combine b₁' b) ∧ canRoll s a (combine b b₂'))
    (h_cost : ∀ s a b₁' b₂' b, canRoll s a b →
      combine b₁' (cost s a b) = cost s a (combine b₁' b) ∧
      cost s a (combine b b₂') = combine (cost s a b) b₂')
    (h₁ : x.IsRollBound b₁ canRoll cost) (h₂ : ∀ y, (g y).IsRollBound b₂ canRoll cost) :
    (x.bind g).IsRollBound (combine b₁ b₂) canRoll cost :=
  IFreeM.isRollBound_bind combine h_can h_cost h₁ fun _ ⟨h, a⟩ => by subst h; exact h₂ a

lemma isChargeBound_bind {c : (s : I) → P.A s → ℕ} {x : FreeM₂ P s t α}
    {g : α → FreeM₂ P t u β} {n₁ n₂ : ℕ} (h₁ : x.IsChargeBound c n₁)
    (h₂ : ∀ y, (g y).IsChargeBound c n₂) :
    (x.bind g).IsChargeBound c (n₁ + n₂) :=
  IFreeM.isChargeBound_bind h₁ fun _ ⟨h, a⟩ => by subst h; exact h₂ a

lemma isTotalRollBound_bind {x : FreeM₂ P s t α} {g : α → FreeM₂ P t u β} {n₁ n₂ : ℕ}
    (h₁ : x.IsTotalRollBound n₁) (h₂ : ∀ y, (g y).IsTotalRollBound n₂) :
    (x.bind g).IsTotalRollBound (n₁ + n₂) :=
  isChargeBound_bind h₁ h₂

end IPFunctor.FreeM₂
