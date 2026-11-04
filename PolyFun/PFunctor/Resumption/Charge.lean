/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Value
public import PolyFun.PFunctor.Resumption.Truncate

/-!
# Charges on resumptions

A resumption may never return, so its charge bound is a safety property: every finite truncation
stays within budget (`IsChargeBound`). A run that never returns is within budget when all of its
finite prefixes are, and a run whose calls are free is within every nonnegative budget. The
worst-case cost is the supremum of the costs of the truncations (`cost`).

Both readings reduce to `FreeM` by truncation, so the `FreeM` laws apply to them. On the
embedding of a free program they agree with the `FreeM` bound (`isChargeBound_toResumption_iff`),
and they unfold one call at a time (`isChargeBound_query_iff`).
-/

@[expose] public section

universe uA uB uβ w

namespace PFunctor.Resumption

variable {p : PFunctor.{uA, uB}} {β : Type uβ} {ω : Type w}

/-- Every finite truncation of `r` stays within budget `B`, with `spent` already spent. -/
def IsChargeBound [Add ω] [LE ω] [Zero ω] (r : Resumption p β) (c : p.A → ω) (B : ω)
    (spent : ω := 0) : Prop :=
  ∀ k, (truncate k r).IsChargeBound c B spent

/-- The worst-case cost of `r`: the supremum of the costs of its finite truncations. -/
noncomputable def cost [AddCommMonoid ω] [CompleteLattice ω] (c : p.A → ω) (r : Resumption p β) :
    ω :=
  ⨆ k, FreeM.cost c (truncate k r)

section Bound

variable [AddCommMonoid ω] [PartialOrder ω] {c : p.A → ω} {B s : ω}

@[simp]
theorem isChargeBound_pure_iff (result : β) :
    (Resumption.pure (p := p) result).IsChargeBound c B s ↔ s ≤ B := by
  simp [IsChargeBound]

theorem isChargeBound_query_iff [CanonicallyOrderedAdd ω] (a : p.A)
    (next : p.B a → Resumption p β) :
    (query a next).IsChargeBound c B s ↔
      s + c a ≤ B ∧ ∀ b, (next b).IsChargeBound c B (s + c a) := by
  constructor
  · intro h
    have h₁ := h 1
    rw [truncate_query_succ] at h₁
    exact ⟨h₁.1, fun b k => by
      have := h (k + 1)
      rw [truncate_query_succ] at this
      exact this.2 b⟩
  · rintro ⟨ha, hn⟩ (_ | k)
    · rw [truncate_query_zero]
      exact le_self_add.trans ha
    · rw [truncate_query_succ]
      exact ⟨ha, fun b => hn b k⟩

/-- On the embedding of a free program, the safety reading is the `FreeM` charge bound. -/
theorem isChargeBound_toResumption_iff [CanonicallyOrderedAdd ω] (x : FreeM p β) :
    (FreeM.toResumption x).IsChargeBound c B s ↔ x.IsChargeBound c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact isChargeBound_pure_iff a
  | liftBind a r ih =>
    rw [FreeM.toResumption_liftBind, isChargeBound_query_iff, FreeM.isChargeBound_liftBind_iff]
    exact and_congr_right fun _ => forall_congr' fun b => ih b

/-- A resumption within budget has not overspent before its first call. -/
theorem IsChargeBound.spent_le {r : Resumption p β} (h : r.IsChargeBound c B s) : s ≤ B := by
  have h₀ := h 0
  rw [truncate_zero] at h₀
  split at h₀ <;> exact h₀

/-- A larger budget keeps a resumption within budget. -/
theorem IsChargeBound.mono {r : Resumption p β} {B' : ω} (h : r.IsChargeBound c B s)
    (hB : B ≤ B') : r.IsChargeBound c B' s :=
  fun k => (h k).mono hB

end Bound

/-- The safety reading is the value bound, where addition distributes over nonempty suprema. -/
theorem isChargeBound_iff_cost_le [AddCommMonoid ω] [CompleteLattice ω] [IsOrderedAddMonoid ω]
    [CanonicallyOrderedAdd ω] [AddSupDistrib ω] {c : p.A → ω} {B : ω} {r : Resumption p β} :
    r.IsChargeBound c B ↔ cost c r ≤ B := by
  simp only [IsChargeBound, cost, iSup_le_iff, FreeM.isChargeBound_iff_cost_le]

end PFunctor.Resumption
