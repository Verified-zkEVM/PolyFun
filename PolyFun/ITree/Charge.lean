/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.Machine
public import PolyFun.PFunctor.Dynamical.DynComputation.Charge

/-!
# Charges on interaction trees

An interaction tree makes visible calls of an interface `F` and silent steps. Its charge bound
charges each visible call at `a` by `c a` and each silent step by `tau`, which defaults to `0`.
It is the safety reading of the resumption-with-tau encoding, in which a silent step is a call
of `y`.

With `tau = 0`, silent steps are free and a bound does not see them (`isChargeBound_step_iff`), so
weakly bisimilar trees have the same bounds. With `tau = 1` and unit charges, the bound counts every
step, which is the fuel of `ITree.toDynComputation` (`isChargeBound_iff_toDynComputation`).
-/

@[expose] public section

universe uA uB uα w

namespace ITree

variable {F : PFunctor.{uA, uB}} {α : Type uα} {ω : Type w}

/-- Every finite prefix of `t` stays within budget `B`, with `spent` already spent, where a visible
call at `a` costs `c a` and a silent step costs `tau`. -/
def IsChargeBound [Add ω] [LE ω] [Zero ω] (t : ITree F α) (c : F.A → ω) (B : ω) (spent : ω := 0)
    (tau : ω := 0) : Prop :=
  PFunctor.Resumption.IsChargeBound (toResumptionWithTau t) (Sum.elim c fun _ => tau) B spent

variable [AddCommMonoid ω] [PartialOrder ω] {c : F.A → ω} {B s tau : ω}

@[simp]
theorem isChargeBound_pure_iff (a : α) :
    (ITree.pure (F := F) a).IsChargeBound c B s tau ↔ s ≤ B := by
  simp [IsChargeBound]

theorem isChargeBound_query_iff [CanonicallyOrderedAdd ω] (a : F.A) (next : F.B a → ITree F α) :
    (ITree.query a next).IsChargeBound c B s tau ↔
      s + c a ≤ B ∧ ∀ b, (next b).IsChargeBound c B (s + c a) tau := by
  rw [IsChargeBound, toResumptionWithTau_query, PFunctor.Resumption.isChargeBound_query_iff]
  rfl

theorem isChargeBound_step_iff' [CanonicallyOrderedAdd ω] (t : ITree F α) :
    (ITree.step t).IsChargeBound c B s tau ↔ s + tau ≤ B ∧ t.IsChargeBound c B (s + tau) tau := by
  rw [IsChargeBound, toResumptionWithTau_step, PFunctor.Resumption.isChargeBound_query_iff]
  exact and_congr_right fun _ => ⟨fun h => h PUnit.unit, fun h _ => h⟩

/-- Free silent steps are invisible to a charge bound. -/
@[simp]
theorem isChargeBound_step_iff [CanonicallyOrderedAdd ω] (t : ITree F α) :
    (ITree.step t).IsChargeBound c B s ↔ t.IsChargeBound c B s := by
  rw [isChargeBound_step_iff', add_zero]
  exact ⟨fun h => h.2, fun h => ⟨PFunctor.Resumption.IsChargeBound.spent_le h, h⟩⟩

/-- The bound of a tree is the bound of its machine over `F + y`, whose silent steps are calls
of `y` charged `tau`. -/
theorem isChargeBound_iff_toDynComputation (t : ITree F α) :
    t.IsChargeBound c B s tau ↔
      (toDynComputation (F := F) (α := α)).IsChargeBound (Sum.elim c fun _ => tau) B
        ((toDynComputation (F := F) (α := α)).init t) s := by
  rw [PFunctor.DynSystem.DynComputation.isChargeBound_init_iff_denote, denote_toDynComputation]
  rfl

end ITree
