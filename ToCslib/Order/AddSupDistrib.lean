/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.ENat.Lattice

/-!
# Bounding a sum by a supremum

Suppose a call incurs a charge `a` and its possible continuations have costs in a nonempty set
`s`. If every `a + b` for `b ∈ s` is within budget, `AddSupDistrib` puts `a + sSup s` within
the same budget. It supplies the inequality `a + sSup s ≤ ⨆ b ∈ s, a + b`. When
`b ↦ a + b` is monotone, `b ≤ sSup s` for each `b ∈ s` gives the reverse inequality.

Mathlib's `IsAddQuantale` requires equality even for the empty set, where it gives
`a + ⊥ = ⊥`. In `ℕ∞` the bottom is `0`, so this would erase the charge of a call with no
answers. For nonempty sets, `ENat.add_sSup` and `ENNReal.add_sSup` give equality in `ℕ∞`
and `ℝ≥0∞`. The `AddSupDistrib` inequality also holds pointwise in families.

`iSup_zero_eq_zero` uses the fact that `0` is the bottom element. The supremum of a family of
zeros is therefore zero even when the index type is empty. See also `ENat.iSup_zero` and
`ENNReal.iSup_zero`.
-/

public section

universe w

/-- For every `a` and nonempty set `s`, `a + sSup s` is at most the supremum of `a + b`
over `b ∈ s`. -/
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
