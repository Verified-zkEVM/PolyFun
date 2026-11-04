/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Event

/-!
# Answer-dependent charges and watermarks

Checks for `PolyFun.PFunctor.Free.Cost.Event`:

* a fetch priced by the size of the data it returns is bounded by its event budget, and by any
  call price that dominates every answer;
* allocation at `+1` and release at `-1` keep the amount live within a budget exactly when the
  watermark of every completed path peaks within it.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargeEvents

/-! ## Prices that depend on answers -/

/-- A fetch returns up to three units of data. -/
abbrev Fetch : PFunctor.{0, 0} := ⟨Unit, fun _ => Fin 4⟩

/-- A fetch costs the size of the data it returns. -/
def returned (i : Fetch.Idx) : ℕ := i.2.val

def twoFetches : FreeM Fetch ℕ := do
  let a ← FreeM.lift (P := Fetch) ()
  let b ← FreeM.lift (P := Fetch) ()
  pure (a.val + b.val)

/-- After every answer, at most six units have been returned. -/
example : twoFetches.IsEventChargeBound returned 6 := by
  simp only [twoFetches, isEventChargeBound_lift_bind_iff', isEventChargeBound_pure_iff,
    returned]
  decide

/-- A price of three per call, paid when asking, dominates every answer. -/
example : twoFetches.IsEventChargeBound returned 6 :=
  IsEventChargeBound.of_isChargeBound (c := fun _ => 3)
    (fun ⟨_, b⟩ => Nat.le_of_lt_succ (show b.val < 4 from b.isLt)) (by simp [twoFetches])

/-! ## Peaks of signed prices -/

/-- Allocate (`true`) or release (`false`) one unit. -/
abbrev Mem : PFunctor.{0, 0} := ⟨Bool, fun _ => PUnit⟩

def live (b : Mem.A) : ℤ := if b then 1 else -1

/-- Two allocations, a release, an allocation, and two releases: at most two units are live. -/
def alloc : FreeM Mem Bool := do
  let _ ← FreeM.lift (P := Mem) true
  let _ ← FreeM.lift (P := Mem) true
  let _ ← FreeM.lift (P := Mem) false
  let _ ← FreeM.lift (P := Mem) true
  let _ ← FreeM.lift (P := Mem) false
  let _ ← FreeM.lift (P := Mem) false
  pure true

theorem alloc_progress : alloc.ProgramProgress :=
  programProgress_of_nonempty alloc

/-- The budget `2` holds, so every completed path peaks at two live units or fewer. -/
example (p : Path alloc) : 0 + (Path.charge (Watermark.of ∘ live) alloc p).peak ≤ 2 :=
  (isChargeBound_iff_forall_peak_le alloc_progress).1
    ⟨by omega, by simp [alloc, live]⟩ p

/-- The budget `1` fails: two units are live after the second allocation. -/
example : ¬ alloc.IsChargeBound live 1 := by
  simp [alloc, live]

end PolyFunTest.ChargeEvents
