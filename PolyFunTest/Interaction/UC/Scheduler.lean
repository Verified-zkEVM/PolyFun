/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.UC.ScheduledOpenProcessModel

/-!
# Tests for mass-aware UC scheduling

These canaries pin the distinction between merely inspecting subtree masses
and satisfying the flat-scheduler coherence contract.
-/

public section

namespace Interaction
namespace UC

def largerSide : BinaryScheduler Id :=
  fun left right => ULift.up (decide (right ≤ left))

theorem sourceDraw_largerSide_unit :
    BinaryScheduler.sourceDraw largerSide 1 1 1 =
      ULift.up .first := by
  rfl

theorem leftDraw_largerSide_unit :
    BinaryScheduler.leftDraw largerSide 1 1 1 =
      ULift.up .context := by
  rfl

/-- A mass-sensitive deterministic policy need not be reassociation-stable.
The `IsFlat` premise is therefore a genuine scheduler law, not a consequence
of carrying masses. -/
theorem largerSide_not_reassociation_stable :
    BinaryScheduler.sourceDraw largerSide 1 1 1 ≠
    BinaryScheduler.leftDraw largerSide 1 1 1 := by
  rw [sourceDraw_largerSide_unit, leftDraw_largerSide_unit]
  nofun

/-- No deterministic identity-monad scheduler is exactly coherent: at equal
masses, swap coherence would require its Boolean choice to equal its negation. -/
theorem not_isCoherent_eq_id (scheduler : BinaryScheduler Id) :
    ¬ scheduler.IsCoherent (MonadRelFamily.eq Id) := by
  intro h
  have hs := (MonadRelFamily.eq_rel _ _).mp (h.swap 1 1)
  change scheduler 1 1 = BinaryScheduler.flip (scheduler 1 1) at hs
  generalize scheduler 1 1 = x at hs
  rcases x with ⟨x⟩
  cases x <;> cases hs

end UC
end Interaction
