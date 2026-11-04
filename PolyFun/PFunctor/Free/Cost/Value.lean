/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Cost
public import Mathlib.Data.ENat.Lattice

/-!
# Worst-case cost of free programs

`cost c x` is the worst-case cost of `x : FreeM P α` under a charge `c : P.A → ω`: the fold of
`OpSpec.charge c`, which reads a call at `a` as `c a` followed by its worst continuation, with
zero leaves. It lives in a complete lattice such as `ℕ∞`, `ℝ≥0∞` or `ι → ℕ∞`. `costWith c x k`
charges each leaf `a` the extra amount `k a`, which makes sequencing exact: `cost c (x >>= f)` is
`costWith c x fun a => cost c (f a)` (`cost_bind`).

The value form is the computational one: its equations reduce the cost of a concrete `do` program
to arithmetic by `simp` (see `cost_bound`). It relates to the budget `IsChargeBound` in canonically
ordered monoids: `isChargeBound_of_cost_le` holds in general, and `cost_le_of_isChargeBound` needs
addition to distribute over nonempty suprema (`AddSupDistrib`, which holds in `ℕ∞` and pointwise).
`isChargeBound_iff_cost_natCast_le` reads a natural-number budget as a bound on the cost in `ℕ∞`.

Costs transport along lenses (`cost_mapLens_le`, with equality when the lens reaches every answer)
and through free handlers, where each call is charged the worst case of its implementation
(`handlerCost`, `cost_liftM_le`).
-/

@[expose] public section

universe uA uB uA₂ uB₂ v v' w w'

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
    (charge c).Monotone := by
  intro a k k' hk
  change c a + ⨆ b, k b ≤ c a + ⨆ b, k' b
  gcongr with b
  exact hk b


end OpSpec

/-! ## Distributivity of addition over suprema -/

/-- Addition on the left distributes over suprema of nonempty sets. This is the hypothesis under
which a structural charge bound bounds the worst-case cost (`FreeM.cost_le_of_isChargeBound`): the
bound checks every branch separately, while the cost takes the supremum first. It holds in `ℕ∞`,
in `ℝ≥0∞` and pointwise in families. -/
class AddSupDistrib (ω : Type w) [Add ω] [CompleteLattice ω] : Prop where
  add_sSup_le (a : ω) {s : Set ω} (hs : s.Nonempty) : a + sSup s ≤ ⨆ b ∈ s, a + b

theorem add_iSup_le_iSup_add {ω : Type w} [Add ω] [CompleteLattice ω] [AddSupDistrib ω]
    {ι : Sort*} [Nonempty ι] (a : ω) (f : ι → ω) : a + ⨆ i, f i ≤ ⨆ i, a + f i := by
  rw [← sSup_range]
  refine (AddSupDistrib.add_sSup_le a (Set.range_nonempty f)).trans ?_
  exact iSup₂_le fun _ ⟨i, hi⟩ => hi ▸ le_iSup (fun i => a + f i) i

instance : AddSupDistrib ℕ∞ where
  add_sSup_le _ _ hs := (ENat.add_sSup hs).le

instance {ι : Type*} {ω : ι → Type w} [∀ i, Add (ω i)] [∀ i, CompleteLattice (ω i)]
    [∀ i, AddSupDistrib (ω i)] : AddSupDistrib (∀ i, ω i) where
  add_sSup_le a s hs i := by
    have : Nonempty s := hs.to_subtype
    rw [Pi.add_apply, sSup_apply, iSup_apply]
    refine (add_iSup_le_iSup_add (a i) fun f : s => (f : ∀ i, ω i) i).trans ?_
    refine iSup_le fun f => ?_
    refine le_trans ?_ (le_iSup _ (f : ∀ i, ω i))
    rw [iSup_apply]
    exact le_iSup (fun _ : (f : ∀ i, ω i) ∈ s => (a + f) i) f.2

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α β : Type v} {ω : Type w}

/-! ## Worst-case cost -/

section Cost

variable [AddCommMonoid ω] [CompleteLattice ω] {c c' : P.A → ω}

/-- The worst-case cost of `x` when each leaf `a` costs `k a` in addition to the calls on the way
to it: the fold of `OpSpec.charge c`. -/
noncomputable def costWith (c : P.A → ω) (x : FreeM P α) (k : α → ω) : ω :=
  wpFold (OpSpec.charge c) x k

/-- The worst-case cost of `x`: the largest total charge of the calls along a branch, where a
call at `a` costs `c a`. -/
noncomputable def cost (c : P.A → ω) (x : FreeM P α) : ω :=
  costWith c x fun _ => 0

theorem costWith_eq_wpFold (c : P.A → ω) (x : FreeM P α) (k : α → ω) :
    costWith c x k = wpFold (OpSpec.charge c) x k :=
  rfl

theorem cost_eq_costWith (c : P.A → ω) (x : FreeM P α) : cost c x = costWith c x fun _ => 0 :=
  rfl

@[simp, freeM_unfold]
theorem costWith_pure (a : α) (k : α → ω) : costWith c (pure a : FreeM P α) k = k a :=
  rfl

@[simp, freeM_unfold]
theorem costWith_freeM_pure (a : α) (k : α → ω) : costWith c (FreeM.pure a : FreeM P α) k = k a :=
  rfl

@[freeM_unfold]
theorem costWith_liftBind (a : P.A) (r : P.B a → FreeM P α) (k : α → ω) :
    costWith c (FreeM.liftBind a r) k = c a + ⨆ b, costWith c (r b) k :=
  rfl

@[simp]
theorem costWith_lift (a : P.A) (k : P.B a → ω) :
    costWith (α := no_index (P.B a)) c (FreeM.lift a) k = c a + ⨆ b, k b :=
  rfl

@[simp]
theorem costWith_liftObj (x : P.Obj α) (k : α → ω) :
    costWith c (FreeM.liftObj x) k = c x.1 + ⨆ b, k (x.2 b) :=
  rfl

@[simp]
theorem costWith_bind {γ : Type v'} (x : FreeM P α) (f : α → FreeM P γ) (k : γ → ω) :
    costWith c (FreeM.bind x f) k = costWith c x fun a => costWith c (f a) k :=
  wpFold_bind' _ x f k

@[simp]
theorem costWith_bind' (x : FreeM P α) (f : α → FreeM P β) (k : β → ω) :
    costWith c (x >>= f) k = costWith c x fun a => costWith c (f a) k :=
  wpFold_bind' _ x f k

@[simp]
theorem costWith_map {γ : Type v'} (f : α → γ) (x : FreeM P α) (k : γ → ω) :
    costWith c (FreeM.map f x) k = costWith c x (k ∘ f) := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih => exact congrArg (c a + ·) (iSup_congr ih)

@[simp]
theorem costWith_map' (f : α → β) (x : FreeM P α) (k : β → ω) :
    costWith c (f <$> x) k = costWith c x (k ∘ f) :=
  costWith_map f x k

@[simp]
theorem costWith_seq (g : FreeM P (α → β)) (x : FreeM P α) (k : β → ω) :
    costWith c (g <*> x) k = costWith c g fun f => costWith c x (k ∘ f) := by
  rw [seq_eq_bind_map, costWith_bind']
  simp only [costWith_map']

@[simp]
theorem costWith_seqLeft (x : FreeM P α) (y : FreeM P β) (k : α → ω) :
    costWith c (x <* y) k = costWith c x fun a => costWith c y fun _ => k a := by
  simp only [seqLeft_eq_bind, costWith_bind', costWith_pure]

@[simp]
theorem costWith_seqRight (x : FreeM P α) (y : FreeM P β) (k : β → ω) :
    costWith c (x *> y) k = costWith c x fun _ => costWith c y k := by
  rw [seqRight_eq_bind, costWith_bind']

@[simp]
theorem costWith_ite (p : Prop) [Decidable p] (x y : FreeM P α) (k : α → ω) :
    costWith c (if p then x else y) k = if p then costWith c x k else costWith c y k := by
  split <;> rfl

@[simp]
theorem costWith_dite (p : Prop) [Decidable p] (x : p → FreeM P α) (y : ¬ p → FreeM P α)
    (k : α → ω) :
    costWith c (if h : p then x h else y h) k =
      if h : p then costWith c (x h) k else costWith c (y h) k := by
  split <;> rfl

@[simp, freeM_unfold]
theorem cost_pure (a : α) : cost c (pure a : FreeM P α) = 0 :=
  rfl

@[simp, freeM_unfold]
theorem cost_freeM_pure (a : α) : cost c (FreeM.pure a : FreeM P α) = 0 :=
  rfl

@[freeM_unfold]
theorem cost_liftBind (a : P.A) (r : P.B a → FreeM P α) :
    cost c (FreeM.liftBind a r) = c a + ⨆ b, cost c (r b) :=
  rfl

/-- **Sequencing, exactly**: each leaf of `x` is charged the cost of its continuation. -/
@[simp]
theorem cost_bind {γ : Type v'} (x : FreeM P α) (f : α → FreeM P γ) :
    cost c (FreeM.bind x f) = costWith c x fun a => cost c (f a) :=
  costWith_bind x f _

@[simp]
theorem cost_bind' (x : FreeM P α) (f : α → FreeM P β) :
    cost c (x >>= f) = costWith c x fun a => cost c (f a) :=
  costWith_bind x f _

@[simp]
theorem cost_map {γ : Type v'} (f : α → γ) (x : FreeM P α) : cost c (FreeM.map f x) = cost c x :=
  costWith_map f x _

@[simp]
theorem cost_map' (f : α → β) (x : FreeM P α) : cost c (f <$> x) = cost c x :=
  costWith_map f x _

@[simp]
theorem cost_ite (p : Prop) [Decidable p] (x y : FreeM P α) :
    cost c (if p then x else y) = if p then cost c x else cost c y := by
  split <;> rfl

@[simp]
theorem cost_dite (p : Prop) [Decidable p] (x : p → FreeM P α) (y : ¬ p → FreeM P α) :
    cost c (if h : p then x h else y h) = if h : p then cost c (x h) else cost c (y h) := by
  split <;> rfl

section Ordered

variable [IsOrderedAddMonoid ω]

/-- The worst-case cost is monotone in the leaf costs. -/
@[gcongr]
theorem costWith_mono (x : FreeM P α) {k k' : α → ω} (hk : k ≤ k') :
    costWith c x k ≤ costWith c x k' :=
  wpFold_mono (OpSpec.charge_mono c) x hk

/-- The worst-case cost is monotone in the charge. -/
@[gcongr]
theorem costWith_mono_charge (hc : c ≤ c') (x : FreeM P α) (k : α → ω) :
    costWith c x k ≤ costWith c' x k := by
  induction x using FreeM.rec with
  | pure a => exact le_rfl
  | liftBind a r ih => exact add_le_add (hc a) (iSup_mono ih)

@[gcongr]
theorem cost_mono_charge (hc : c ≤ c') (x : FreeM P α) : cost c x ≤ cost c' x :=
  costWith_mono_charge hc x _

/-- The leaf costs split off: the cost-to-go is at most the cost plus the largest leaf cost. -/
theorem costWith_le_cost_add (x : FreeM P α) (k : α → ω) :
    costWith c x k ≤ cost c x + ⨆ a, k a := by
  induction x using FreeM.rec with
  | pure a => simpa using le_iSup k a
  | liftBind a r ih =>
    rw [costWith_liftBind, cost_liftBind, add_assoc]
    gcongr
    refine iSup_le fun b => (ih b).trans ?_
    gcongr
    exact le_iSup (fun b => cost c (r b)) b

/-- The cost of a sequence is at most the cost of the first part plus the worst continuation. -/
theorem cost_bind_le {γ : Type v'} (x : FreeM P α) (f : α → FreeM P γ) :
    cost c (FreeM.bind x f) ≤ cost c x + ⨆ a, cost c (f a) := by
  rw [cost_bind]
  exact costWith_le_cost_add x _

end Ordered

section Canonical

variable [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω]

omit [IsOrderedAddMonoid ω] in
@[simp]
theorem iSup_zero_eq_zero {ι : Sort*} : (⨆ _ : ι, (0 : ω)) = 0 := by
  rw [← bot_eq_zero, iSup_bot]

omit [IsOrderedAddMonoid ω] in
@[simp]
theorem cost_lift (a : P.A) : cost (α := no_index (P.B a)) c (FreeM.lift a) = c a := by
  change c a + ⨆ _ : P.B a, (0 : ω) = c a
  rw [iSup_zero_eq_zero, add_zero]

omit [IsOrderedAddMonoid ω] in
theorem cost_liftObj (x : P.Obj α) : cost c (FreeM.liftObj x) = c x.1 := by
  change c x.1 + ⨆ _ : P.B x.1, (0 : ω) = c x.1
  rw [iSup_zero_eq_zero, add_zero]

/-- **From the value to the budget.** A bound on the worst-case cost is a structural charge
bound. Together with `cost_le_of_isChargeBound`, this lets `simp` decide budgets by computing
costs. -/
theorem isChargeBound_of_cost_le {x : FreeM P α} {B s : ω} (h : s + cost c x ≤ B) :
    IsChargeBound x c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => simpa using h
  | liftBind a r ih =>
    rw [cost_liftBind, ← add_assoc] at h
    refine ⟨le_self_add.trans h, fun b => ih b ?_⟩
    exact le_trans (add_le_add le_rfl (le_iSup (fun b => cost c (r b)) b)) h

theorem IsChargeBound.of_cost_le {x : FreeM P α} {B : ω} (h : cost c x ≤ B) :
    IsChargeBound x c B :=
  isChargeBound_of_cost_le (by rwa [zero_add])

omit [IsOrderedAddMonoid ω] in
/-- **From the budget to the value**, where addition distributes over nonempty suprema. -/
theorem cost_le_of_isChargeBound [AddSupDistrib ω] {x : FreeM P α} {B s : ω}
    (h : IsChargeBound x c B s) : s + cost c x ≤ B := by
  induction x using FreeM.rec generalizing s with
  | pure a => simpa using h
  | liftBind a r ih =>
    rw [cost_liftBind, ← add_assoc]
    rcases isEmpty_or_nonempty (P.B a) with hb | hb
    · rw [iSup_of_empty, bot_eq_zero, add_zero]
      exact h.1
    · exact (add_iSup_le_iSup_add _ _).trans (iSup_le fun b => ih b (h.2 b))

theorem isChargeBound_iff_cost_le [AddSupDistrib ω] {x : FreeM P α} {B : ω} :
    IsChargeBound x c B ↔ cost c x ≤ B :=
  ⟨fun h => by simpa using cost_le_of_isChargeBound h, IsChargeBound.of_cost_le⟩

end Canonical

end Cost

/-- A natural-number budget is a bound on the worst-case cost in `ℕ∞`. -/
theorem isChargeBound_iff_cost_natCast_le {x : FreeM P α} {c : P.A → ℕ} {n : ℕ} :
    IsChargeBound x c n ↔ cost (fun a => (c a : ℕ∞)) x ≤ n := by
  rw [← isChargeBound_natCast_iff, Nat.cast_zero, isChargeBound_iff_cost_le]

section CostTransfer

variable [AddCommMonoid ω] [CompleteLattice ω] [IsOrderedAddMonoid ω]

/-- Relabelling along a lens costs at most the program with the pulled-back charge. -/
theorem costWith_mapLens_le {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q) (c : Q.A → ω)
    (x : FreeM P α) (k : α → ω) :
    costWith c (x.mapLens l) k ≤ costWith (c ∘ l.toFunA) x k := by
  induction x using FreeM.rec with
  | pure a => exact le_rfl
  | liftBind a r ih =>
    rw [FreeM.mapLens_liftBind, costWith_liftBind, costWith_liftBind]
    exact add_le_add le_rfl (iSup_le fun d =>
      (ih _).trans (le_iSup (fun b => costWith (c ∘ l.toFunA) (r b) k) _))

theorem cost_mapLens_le {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q) (c : Q.A → ω)
    (x : FreeM P α) : cost c (x.mapLens l) ≤ cost (c ∘ l.toFunA) x :=
  costWith_mapLens_le l c x _

omit [IsOrderedAddMonoid ω] in
/-- When every answer of the target is reached by the lens, relabelling preserves the cost. -/
theorem costWith_mapLens_of_surjective {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q)
    (hl : ∀ a, Function.Surjective (l.toFunB a)) (c : Q.A → ω) (x : FreeM P α) (k : α → ω) :
    costWith c (x.mapLens l) k = costWith (c ∘ l.toFunA) x k := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rw [FreeM.mapLens_liftBind, costWith_liftBind, costWith_liftBind]
    congr 1
    exact (hl a).iSup_comp (fun b => costWith (c ∘ l.toFunA) (r b) k) ▸
      iSup_congr fun d => ih _

omit [IsOrderedAddMonoid ω] in
theorem cost_mapLens_of_surjective {Q : PFunctor.{uA₂, uB₂}} (l : Lens P Q)
    (hl : ∀ a, Function.Surjective (l.toFunB a)) (c : Q.A → ω) (x : FreeM P α) :
    cost c (x.mapLens l) = cost (c ∘ l.toFunA) x :=
  costWith_mapLens_of_surjective l hl c x _

variable {Q : PFunctor.{uA₂, uB}} {α : Type uB}

/-- The worst-case cost of a handler's implementation of the call at `a`. -/
noncomputable def handlerCost (d : Q.A → ω) (handler : (a : P.A) → FreeM Q (P.B a)) (a : P.A) :
    ω :=
  cost d (handler a)

/-- **Simulation overhead.** A program simulated through a free handler costs at most the program
with each call charged the worst case of its implementation. -/
theorem costWith_liftM_le (d : Q.A → ω) (handler : (a : P.A) → FreeM Q (P.B a))
    (x : FreeM P α) (k : α → ω) :
    costWith d (x.liftM handler) k ≤ costWith (handlerCost d handler) x k :=
  wpFold_liftM_le handler (OpSpec.charge_mono _) (fun a k => costWith_le_cost_add (handler a) k)
    x k

theorem cost_liftM_le (d : Q.A → ω) (handler : (a : P.A) → FreeM Q (P.B a)) (x : FreeM P α) :
    cost d (x.liftM handler) ≤ cost (handlerCost d handler) x :=
  costWith_liftM_le d handler x _

end CostTransfer

end FreeM

end PFunctor
