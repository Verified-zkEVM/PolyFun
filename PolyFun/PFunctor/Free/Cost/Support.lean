/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Value

/-!
# Charges restricted to reachable results and to the calls made

Sequencing laws need the continuation only where `x` can return. `IsChargeBound.bind_of_le_supp`
and `IsChargeBound.bind_supp` take the continuation bound on the structural support `x.supp`, and
`costWith_le_cost_add_supp` / `cost_bind_le_supp` restrict the worst-case cost of the
continuation the same way.

`x.CallsIn S` says that every call of `x` is at a position in `S`. Under it, charges and handlers
matter only on `S`:

* `IsChargeBound.congr_charge` and `costWith_congr_charge`: charges agreeing on `S` give the same
  bound and cost;
* `liftM_congr_of_callsIn`: handlers agreeing on `S` give the same run;
* `IsChargeBound.liftM_of_callsIn`: free-handler transfer with step certificates only on `S`.

`callsIn_iff_isChargeBound` reads `CallsIn` as the zero budget for the indicator of the excluded
positions.
-/

@[expose] public section

universe uA uB uA₂ uB₂ v v' w

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v} {ω : Type w}

/-! ## Restricted sequencing -/

section Bound

variable [AddCommMonoid ω] [PartialOrder ω] {c : P.A → ω} {B L s : ω}

/-- **Sequencing on reachable results.** If `x` stays within `L ≤ B` and the continuation at
every result `x` can return stays within `B` from any amount at most `L`, then `x >>= f` stays
within `B`. -/
theorem IsChargeBound.bind_of_le_supp {β : Type v'} {x : FreeM P α} {f : α → FreeM P β}
    (hx : IsChargeBound x c L s) (hL : L ≤ B)
    (hf : ∀ a ∈ x.supp, ∀ s', s' ≤ L → IsChargeBound (f a) c B s') :
    IsChargeBound (FreeM.bind x f) c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact hf a rfl s hx
  | liftBind a r ih =>
    exact ⟨hx.1.trans hL, fun b =>
      ih b (hx.2 b) fun a' ha' => hf a' (mem_supp_liftBind_of_mem ha')⟩

/-- **Sequencing at an invariant.** If `x` stays within `L ≤ B`, every result of `x` satisfies
`I`, and the continuation at every result satisfying `I` stays within `B` from any amount at most
`L`, then `x >>= f` stays within `B`. Reachable results are the case `I := (· ∈ x.supp)`
(`IsChargeBound.bind_of_le_supp`). -/
theorem IsChargeBound.bind_of_le_of_wpFold {β : Type v'} {x : FreeM P α} {f : α → FreeM P β}
    {I : α → Prop} (hx : IsChargeBound x c L s) (hI : wpFold (OpSpec.demonic P) x I) (hL : L ≤ B)
    (hf : ∀ a, I a → ∀ s', s' ≤ L → IsChargeBound (f a) c B s') :
    IsChargeBound (FreeM.bind x f) c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact hf a hI s hx
  | liftBind a r ih => exact ⟨hx.1.trans hL, fun b => ih b (hx.2 b) (hI b)⟩

/-- **Budgets add under sequencing at an invariant.** -/
theorem IsChargeBound.bind_of_wpFold [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω]
    {β : Type v'} {x : FreeM P α} {f : α → FreeM P β} {I : α → Prop} {B₁ B₂ : ω}
    (hx : IsChargeBound x c B₁ s) (hI : wpFold (OpSpec.demonic P) x I)
    (hf : ∀ a, I a → IsChargeBound (f a) c B₂) :
    IsChargeBound (FreeM.bind x f) c (B₁ + B₂) s := by
  refine hx.bind_of_le_of_wpFold hI le_self_add fun a ha s' hs' => ?_
  have := (hf a ha).add_left s'
  rw [add_zero] at this
  exact this.mono (add_le_add hs' le_rfl)

/-- **Budgets add under sequencing on reachable results.** -/
theorem IsChargeBound.bind_supp [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω] {β : Type v'}
    {x : FreeM P α} {f : α → FreeM P β} {B₁ B₂ : ω} (hx : IsChargeBound x c B₁ s)
    (hf : ∀ a ∈ x.supp, IsChargeBound (f a) c B₂) :
    IsChargeBound (FreeM.bind x f) c (B₁ + B₂) s := by
  refine hx.bind_of_le_supp le_self_add fun a ha s' hs' => ?_
  have := (hf a ha).add_left s'
  rw [add_zero] at this
  exact this.mono (add_le_add hs' le_rfl)

end Bound

section Cost

variable [AddCommMonoid ω] [CompleteLattice ω] [IsOrderedAddMonoid ω] {c : P.A → ω}

/-- The leaf costs split off over reachable results only. -/
theorem costWith_le_cost_add_supp (x : FreeM P α) (k : α → ω) :
    costWith c x k ≤ cost c x + ⨆ a ∈ x.supp, k a := by
  induction x using FreeM.rec with
  | pure a =>
    exact (le_iSup₂ (f := fun a' (_ : a' ∈ supp (FreeM.pure a : FreeM P α)) => k a') a rfl).trans
      (le_of_eq (zero_add _).symm)
  | liftBind a r ih =>
    rw [costWith_liftBind, cost_liftBind, add_assoc]
    refine add_le_add le_rfl (iSup_le fun b => (ih b).trans (add_le_add
      (le_iSup (fun b => cost c (r b)) b) (iSup₂_le fun a' ha' => ?_)))
    exact le_iSup₂ (f := fun a' (_ : a' ∈ supp (FreeM.liftBind a r)) => k a') a'
      (mem_supp_liftBind_of_mem ha')

/-- The cost of a sequence is at most the cost of the first part plus the worst continuation at a
reachable result. -/
theorem cost_bind_le_supp {β : Type v'} (x : FreeM P α) (f : α → FreeM P β) :
    cost c (FreeM.bind x f) ≤ cost c x + ⨆ a ∈ x.supp, cost c (f a) := by
  rw [cost_bind]
  exact costWith_le_cost_add_supp x _

end Cost

/-! ## Provenance -/

/-- Every call of `x` is at a position in `S`. -/
def CallsIn (x : FreeM P α) (S : Set P.A) : Prop :=
  IsRollBound x () (fun a _ => a ∈ S) (fun _ _ => ())

variable {S : Set P.A}

@[simp]
theorem callsIn_pure (a : α) : CallsIn (pure a : FreeM P α) S :=
  trivial

theorem callsIn_liftBind_iff (a : P.A) (r : P.B a → FreeM P α) :
    CallsIn (FreeM.liftBind a r) S ↔ a ∈ S ∧ ∀ b, CallsIn (r b) S :=
  Iff.rfl

/-- `CallsIn` is the zero budget for the indicator of the positions outside `S`. -/
theorem callsIn_iff_isChargeBound [DecidablePred (· ∈ S)] (x : FreeM P α) :
    CallsIn x S ↔ x.IsChargeBound (fun a => if a ∈ S then 0 else 1) (0 : ℕ) := by
  induction x using FreeM.rec with
  | pure a => exact iff_of_true trivial le_rfl
  | liftBind a r ih =>
    rw [callsIn_liftBind_iff, isChargeBound_liftBind_iff]
    by_cases ha : a ∈ S <;> simp [ha, ih]

/-- `x.MayCall a`: a call at `a` occurs in the tree of `x`, on any branch. -/
def MayCall : FreeM P α → P.A → Prop
  | .pure _, _ => False
  | .liftBind a' r, a => a = a' ∨ ∃ b, MayCall (r b) a

@[simp]
theorem mayCall_pure (x : α) (a : P.A) : MayCall (pure x : FreeM P α) a ↔ False :=
  Iff.rfl

theorem mayCall_liftBind_iff (a' : P.A) (r : P.B a' → FreeM P α) (a : P.A) :
    MayCall (FreeM.liftBind a' r) a ↔ a = a' ∨ ∃ b, MayCall (r b) a :=
  Iff.rfl

/-- A program calls only in `S` exactly when every call occurring in its tree lies in `S`. -/
theorem callsIn_iff_forall_mayCall (x : FreeM P α) :
    CallsIn x S ↔ ∀ a, x.MayCall a → a ∈ S := by
  induction x using FreeM.rec with
  | pure v => exact iff_of_true trivial fun _ h => h.elim
  | liftBind a' r ih =>
    rw [callsIn_liftBind_iff]
    simp only [mayCall_liftBind_iff, ih]
    constructor
    · rintro ⟨ha, hr⟩ a (rfl | ⟨b, hb⟩)
      exacts [ha, hr b a hb]
    · intro h
      exact ⟨h a' (Or.inl rfl), fun b a hb => h a (Or.inr ⟨b, hb⟩)⟩

/-- A program calls only in the set of calls occurring in it; it is the least such set
(`callsIn_iff_forall_mayCall`). -/
theorem callsIn_setOf_mayCall (x : FreeM P α) : CallsIn x {a | x.MayCall a} :=
  (callsIn_iff_forall_mayCall x).2 fun _ h => h

/-- Charges agreeing on the positions a program calls give the same bound. -/
theorem IsChargeBound.congr_charge [Add ω] [LE ω] [Zero ω] {c c' : P.A → ω} {B s : ω}
    {x : FreeM P α} (hS : x.CallsIn S) (hc : ∀ a ∈ S, c a = c' a) :
    x.IsChargeBound c B s ↔ x.IsChargeBound c' B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact Iff.rfl
  | liftBind a r ih =>
    rw [isChargeBound_liftBind_iff, isChargeBound_liftBind_iff, hc a hS.1]
    exact and_congr_right fun _ => forall_congr' fun b => ih b (hS.2 b)

/-- Charges agreeing on the positions a program calls give the same cost. -/
theorem costWith_congr_charge [AddCommMonoid ω] [CompleteLattice ω] {c c' : P.A → ω}
    {x : FreeM P α} (hS : x.CallsIn S) (hc : ∀ a ∈ S, c a = c' a) (k : α → ω) :
    costWith c x k = costWith c' x k := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rw [costWith_liftBind, costWith_liftBind, hc a hS.1]
    exact congrArg (c' a + ·) (iSup_congr fun b => ih b (hS.2 b))

/-- Handlers agreeing on the positions a program calls run it the same way. -/
theorem liftM_congr_of_callsIn {m : Type uB → Type v'} [Monad m] {α : Type uB}
    {h h' : (a : P.A) → m (P.B a)} {x : FreeM P α} (hS : x.CallsIn S) (hh : ∀ a ∈ S, h a = h' a) :
    x.liftM h = x.liftM h' := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    change (h a >>= fun b => (r b).liftM h) = h' a >>= fun b => (r b).liftM h'
    rw [hh a hS.1]
    exact bind_congr fun b => ih b (hS.2 b)

/-- **Free-handler transfer on the positions called.** Step certificates are needed only on
`S`. -/
theorem IsChargeBound.liftM_of_callsIn [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]
    {Q : PFunctor.{uA₂, uB₂}} {α : Type uB} (h : (a : P.A) → FreeM Q (P.B a)) {c : P.A → ω}
    {d : Q.A → ω} {B s : ω} (hstep : ∀ a ∈ S, IsChargeBound (h a) d (c a)) {x : FreeM P α}
    (hS : x.CallsIn S) (hx : x.IsChargeBound c B s) : (x.liftM h).IsChargeBound d B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact hx
  | liftBind a r ih =>
    change IsChargeBound (FreeM.bind (h a) fun b => (r b).liftM h) d B s
    have hh := (hstep a hS.1).add_left s
    rw [add_zero] at hh
    exact hh.bind_of_le hx.1 fun b s' hs' => (ih b (hS.2 b) (hx.2 b)).mono_spent hs'

end PFunctor.FreeM
