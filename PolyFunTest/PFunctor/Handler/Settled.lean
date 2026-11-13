/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Settled

/-!
# Settled runs of partial handlers

Checks for `PolyFun.PFunctor.Handler.Settled`, with a cache read as a partial handler:

* a program whose calls the cache answers is settled, and stays settled when the cache grows;
* a stateful handler that answers cached keys without changing its state, and changes it on a
  miss, runs a settled program at the same state, while an unsettled program moves the state;
* charging the cache in a writer logs the charge of the path the program follows, which counts a
  repeated warm read each time;
* positions without decidable equality, such as functions, need nothing extra.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.SettledRuns

/-- Look up a number by a number. -/
abbrev Key : PFunctor := ⟨ℕ, fun _ => ℕ⟩

/-- A cache holding keys `0` and `7`. -/
def cache : Handler Option Key := fun k =>
  if k = 0 then some 10 else if k = 7 then some 70 else none

/-- Read `0`, `7` and `0` again. -/
def warmReads : FreeM Key ℕ := do
  let a ← FreeM.lift (P := Key) 0
  let b ← FreeM.lift (P := Key) 7
  let c ← FreeM.lift (P := Key) 0
  pure (a + b + c)

/-- Read the uncached key `3`. -/
def coldRead : FreeM Key ℕ := FreeM.lift (P := Key) 3

example : warmReads.liftM cache = some 90 := rfl

example : coldRead.liftM cache = none := rfl

/-! ## Extension -/

/-- The cache after key `3` is added. -/
def grown : Handler Option Key := fun k => if k = 3 then some 30 else cache k

example : warmReads.liftM grown = some 90 :=
  FreeM.liftM_eq_some_of_le cache grown
    (fun k b h => by
      by_cases hk : k = 3
      · subst hk; simp [cache] at h
      · simpa [grown, hk] using h)
    rfl

/-! ## Framing a stateful run -/

/-- Answer cached keys from the cache at the same state; on a miss, answer with the state and
count the miss. -/
def counting : Handler (StateT ℕ Id) Key := fun k =>
  StateT.mk fun s => match cache k with
    | some v => (v, s)
    | none => (s, s + 1)

/-- The settled program runs at the starting state. -/
example : (warmReads.liftM counting).run 5 = pure (90, 5) :=
  FreeM.run_liftM_eq_pure_of_liftM_eq_some cache counting 5
    (fun k b h => by simp only [counting, StateT.run_mk, h]; rfl) rfl

/-- The unsettled program counts a miss, so its run does not end at the starting state: the frame
law needs its program to be settled. -/
example : (coldRead.liftM counting).run 5 = (5, 6) := rfl

example : ∀ v, (coldRead.liftM counting).run 5 ≠ pure (v, 5) := by
  intro v h
  have moved : (6 : ℕ) = 5 := congrArg Prod.snd h
  omega

/-! ## The charge of a settled run -/

/-- Charge a read of key `k` by `k + 1`. -/
def readCharge : Key.A → ℕ := fun k => k + 1

/-- A total choice of answers that agrees with the cache. -/
def fallback : (k : Key.A) → Key.B k := fun k => (cache k).getD 0

/-- The repeated warm read of `0` pays again: the charge is `1 + 8 + 1`. -/
example : (warmReads.liftM (cache.withChargeW readCharge)).run =
    some (90, Multiplicative.ofAdd 10) := rfl

example : (warmReads.liftM (cache.withChargeW readCharge)).run =
    some (90, Multiplicative.ofAdd
      (FreeM.Path.charge readCharge warmReads (FreeM.Path.ofHandler fallback warmReads))) :=
  FreeM.run_liftM_withChargeW_eq_of_liftM_eq_some cache readCharge fallback
    (fun k b h => by simp [fallback, h]) rfl

example : FreeM.output warmReads (FreeM.Path.ofHandler fallback warmReads) = 90 :=
  FreeM.output_ofHandler_eq_of_liftM_eq_some cache fallback (fun k b h => by simp [fallback, h]) rfl

/-! ## Function positions -/

/-- Ask for a function's value at `0`. -/
abbrev AtZero : PFunctor := ⟨ℕ → ℕ, fun _ => ℕ⟩

/-- A stateful handler that evaluates at `0` and keeps its state. -/
def evalAtZero : Handler (StateT Bool Id) AtZero := fun f => StateT.mk fun s => (f 0, s)

example : ((FreeM.lift (P := AtZero) (· + 1)).liftM evalAtZero).run true = pure (1, true) :=
  FreeM.run_liftM_eq_pure_of_liftM_eq_some (fun f => some (f 0) : Handler Option AtZero) evalAtZero
    true
    (fun f b h => by cases h; rfl) rfl

end PolyFunTest.SettledRuns
