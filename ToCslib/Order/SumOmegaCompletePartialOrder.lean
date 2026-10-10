/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Data.Sum.Order

/-!
# Disjoint sums of omega-CPOs

The default sum order keeps the two tags incomparable. Every increasing
sequence stays in its initial summand, so its supremum can be computed there.
-/

public section

-- upstream candidate: disjoint sums for Mathlib's omega-CPO API.

open OmegaCompletePartialOrder

namespace Sum

variable {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

/-- A chain initially in the left summand stays there. -/
theorem chain_eq_inl (c : Chain (α ⊕ β)) {a : α} (h : c 0 = inl a) (n : ℕ) :
    ∃ x, c n = inl x := by
  have hn := c.monotone (Nat.zero_le n)
  change c 0 ≤ c n at hn
  rw [h] at hn
  cases heq : c n with
  | inl x => exact ⟨x, rfl⟩
  | inr x => rw [heq] at hn; exact (not_inl_le_inr hn).elim

/-- The left components of a chain in the left summand. -/
noncomputable def inlChain (c : Chain (α ⊕ β)) {a : α} (h : c 0 = inl a) : Chain α where
  toFun n := (chain_eq_inl c h n).choose
  monotone' i j hij := by
    have hc := c.monotone hij
    change c i ≤ c j at hc
    rw [(chain_eq_inl c h i).choose_spec, (chain_eq_inl c h j).choose_spec] at hc
    exact inl_le_inl_iff.mp hc

@[simp] theorem inl_inlChain (c : Chain (α ⊕ β)) {a : α} (h : c 0 = inl a) (n : ℕ) :
    inl (inlChain c h n) = c n := (chain_eq_inl c h n).choose_spec.symm

/-- A chain in the left summand has its least upper bound there. -/
theorem isLUB_inlChain (c : Chain (α ⊕ β)) {a : α} (h : c 0 = inl a) :
    IsLUB (Set.range c) (inl (ωSup (inlChain c h))) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    rw [(chain_eq_inl c h n).choose_spec, inl_le_inl_iff]
    exact le_ωSup (inlChain c h) n
  · intro bound hb
    cases bound with
    | inl b =>
        apply inl_le_inl_iff.mpr
        apply ωSup_le
        intro n
        have hn := hb (Set.mem_range_self n)
        rw [(chain_eq_inl c h n).choose_spec, inl_le_inl_iff] at hn
        exact hn
    | inr b =>
        have hn := hb (Set.mem_range_self 0)
        rw [h] at hn
        exact (not_inl_le_inr hn).elim

/-- An increasing sequence in a disjoint sum has a least upper bound. -/
theorem exists_isLUB_chain (c : Chain (α ⊕ β)) : ∃ x, IsLUB (Set.range c) x := by
  cases h : c 0 with
  | inl a => exact ⟨_, isLUB_inlChain c h⟩
  | inr b =>
      let swapOrder := OrderIso.sumComm α β
      let swapped := c.map (swapOrder : (α ⊕ β) →o (β ⊕ α))
      have hs : swapped 0 = inl b := by simp [swapped, h, swapOrder]
      have hsup := isLUB_inlChain swapped hs
      refine ⟨swapOrder.symm (inl (ωSup (inlChain swapped hs))), ?_, ?_⟩
      · rintro _ ⟨n, rfl⟩
        exact swapOrder.le_symm_apply.mpr (hsup.1 (Set.mem_range_self n))
      · intro bound hb
        apply swapOrder.symm_apply_le.mpr
        apply hsup.2
        rintro _ ⟨n, rfl⟩
        exact swapOrder.monotone (hb (Set.mem_range_self n))

noncomputable instance omegaCompletePartialOrder : OmegaCompletePartialOrder (α ⊕ β) where
  ωSup c := (exists_isLUB_chain c).choose
  le_ωSup c n := (exists_isLUB_chain c).choose_spec.1 (Set.mem_range_self n)
  ωSup_le c _ hx := (exists_isLUB_chain c).choose_spec.2
    (by rintro _ ⟨n, rfl⟩; exact hx n)

/-- A chain in the left summand has its supremum in the left summand. -/
theorem ωSup_eq_inl (c : Chain (α ⊕ β)) {a : α} (h : c 0 = inl a) :
    ωSup c = inl (ωSup (inlChain c h)) :=
  (ωSup_eq_of_isLUB (isLUB_inlChain c h)).symm

/-- The left inclusion is continuous for the disjoint sum order. -/
@[fun_prop] theorem ωScottContinuous_inl : ωScottContinuous (inl : α → α ⊕ β) := by
  apply ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h => inl_le_inl_iff.mpr h, fun c => ?_⟩
  rw [ωSup_eq_inl _ (a := c 0) rfl]
  congr 2
  ext n
  exact (Sum.inl.inj (inl_inlChain _ rfl n)).symm

/-- Swapping the two summands is continuous. -/
@[fun_prop] theorem ωScottContinuous_swap : ωScottContinuous (swap : α ⊕ β → β ⊕ α) := by
  apply ωScottContinuous.of_monotone_map_ωSup ⟨swap_monotone, fun c => ?_⟩
  apply ωSup_eq_of_isLUB
  constructor
  · rintro _ ⟨n, rfl⟩
    exact swap_monotone (le_ωSup c n)
  · intro bound hb
    rw [← swap_le_swap_iff, swap_swap]
    apply ωSup_le
    intro n
    rw [← swap_le_swap_iff, swap_swap]
    exact hb (Set.mem_range_self n)

/-- The right inclusion is continuous for the disjoint sum order. -/
@[fun_prop] theorem ωScottContinuous_inr : ωScottContinuous (inr : β → α ⊕ β) :=
  ωScottContinuous_swap.comp ωScottContinuous_inl

variable {γ : Type*} [OmegaCompletePartialOrder γ]

/-- Case analysis on a disjoint sum is continuous when each branch is. -/
@[fun_prop] theorem ωScottContinuous_elim (f : α →𝒄 γ) (g : β →𝒄 γ) :
    ωScottContinuous (Sum.elim f g) := by
  have mono : Monotone (Sum.elim f g) := by
    intro x y h
    cases h with
    | inl h => exact f.monotone h
    | inr h => exact g.monotone h
  apply ωScottContinuous.of_monotone_map_ωSup ⟨mono, fun c => ?_⟩
  have left (c : Chain (α ⊕ β)) {a : α} (h : c 0 = inl a) :
      Sum.elim f g (ωSup c) = ωSup (c.map ⟨Sum.elim f g, mono⟩) := by
    rw [ωSup_eq_inl c h, Sum.elim_inl, f.continuous]
    congr 1
    ext n
    change f (inlChain c h n) = Sum.elim f g (c n)
    rw [(chain_eq_inl c h n).choose_spec]
    rfl
  cases h : c 0 with
  | inl a => exact left c h
  | inr b =>
      let swapped := c.map ⟨Sum.swap, swap_monotone⟩
      have hs : swapped 0 = inl b := by simp [swapped, h]
      have supSwap : ωSup swapped = (ωSup c).swap :=
        (ωScottContinuous_swap.map_ωSup c).symm
      have supc : ωSup c = inr (ωSup (inlChain swapped hs)) := by
        have hh := ωSup_eq_inl swapped hs
        rw [supSwap] at hh
        simpa only [swap_swap, swap_inl] using congrArg Sum.swap hh
      rw [supc, Sum.elim_inr, g.continuous]
      congr 1
      ext n
      have hn := inl_inlChain swapped hs n
      have hc : c n = inr (inlChain swapped hs n) := by
        have hh := congrArg Sum.swap hn
        simpa only [swap_inl, swapped, Chain.coe_map, Function.comp_apply,
          OrderHom.coe_mk, swap_swap] using hh.symm
      change g (inlChain swapped hs n) = Sum.elim f g (c n)
      rw [hc]
      rfl

/-- Continuous case analysis on a disjoint sum. -/
@[expose] noncomputable def elimContinuous (f : α →𝒄 γ) (g : β →𝒄 γ) : (α ⊕ β) →𝒄 γ :=
  .ofFun (Sum.elim f g) (ωScottContinuous_elim f g)

end Sum
