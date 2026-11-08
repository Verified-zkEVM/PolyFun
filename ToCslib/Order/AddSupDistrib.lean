/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.ENat.Lattice

/-!
# Addition distributing over suprema

`AddSupDistrib ω` says that, in a complete lattice with an addition, adding on the left distributes
over suprema of nonempty sets: `a + sSup s ≤ ⨆ b ∈ s, a + b`. The reverse inequality holds whenever
addition is monotone. It holds in `ℕ∞` (from `ENat.add_sSup`) and pointwise in families. Mathlib
proves the equation separately for `ℕ∞` and `ℝ≥0∞` (`ENat.add_sSup`, `ENNReal.add_sSup`); the
class names the common hypothesis. Mathlib's `IsAddQuantale` asks for the equation on every set,
the empty one included, where it reads `a + ⊥ = ⊥`. That fails in `ℕ∞`, whose bottom is `0`, so
this class asks only for nonempty sets.

`iSup_zero_eq_zero` is the constant supremum of `0` over a possibly empty index in a canonically
ordered monoid, whose bottom is `0`. Mathlib has it for `ℕ∞` and `ℝ≥0∞` (`ENat.iSup_zero`,
`ENNReal.iSup_zero`).
-/

public section

universe w

/-- Addition on the left distributes over suprema of nonempty sets. -/
class AddSupDistrib (ω : Type w) [Add ω] [CompleteLattice ω] : Prop where
  add_sSup_le (a : ω) {s : Set ω} (hs : s.Nonempty) : a + sSup s ≤ ⨆ b ∈ s, a + b

theorem add_iSup_le_iSup_add {ω : Type w} [Add ω] [CompleteLattice ω] [AddSupDistrib ω]
    {ι : Sort*} [Nonempty ι] (a : ω) (f : ι → ω) : a + ⨆ i, f i ≤ ⨆ i, a + f i := by
  rw [← sSup_range]
  refine (AddSupDistrib.add_sSup_le a (Set.range_nonempty f)).trans ?_
  exact iSup₂_le fun _ ⟨i, hi⟩ => hi ▸ le_iSup (fun i => a + f i) i

instance : AddSupDistrib ℕ∞ where
  add_sSup_le _ _ hs := (ENat.add_sSup hs).le

instance Pi.addSupDistrib {ι : Type*} {ω : ι → Type w} [∀ i, Add (ω i)]
    [∀ i, CompleteLattice (ω i)] [∀ i, AddSupDistrib (ω i)] : AddSupDistrib (∀ i, ω i) where
  add_sSup_le a s hs i := by
    have : Nonempty s := hs.to_subtype
    rw [Pi.add_apply, sSup_apply, iSup_apply]
    refine (add_iSup_le_iSup_add (a i) fun f : s => (f : ∀ i, ω i) i).trans ?_
    refine iSup_le fun f => ?_
    refine le_trans ?_ (le_iSup _ (f : ∀ i, ω i))
    rw [iSup_apply]
    exact le_iSup (fun _ : (f : ∀ i, ω i) ∈ s => (a + f) i) f.2

@[simp]
theorem iSup_zero_eq_zero {ω : Type w} [AddZeroClass ω] [CompleteLattice ω]
    [CanonicallyOrderedAdd ω] {ι : Sort*} : (⨆ _ : ι, (0 : ω)) = 0 := by
  rw [← bot_eq_zero, iSup_bot]
