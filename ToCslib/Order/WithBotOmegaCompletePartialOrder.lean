/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Order.WithBot

/-!
# Lifting an omega-CPO

Adjoining a fresh bottom preserves omega-completeness and the order within
defined values. This is the lift used for lazy values: a defined pair whose
fields are partial can acquire more information without changing its tag.
-/

public section

-- upstream candidate: bottom lifting for Mathlib's omega-CPO API.

open OmegaCompletePartialOrder

namespace WithBot

variable {α : Type*} [OmegaCompletePartialOrder α]

/-- A lifted chain stays defined after its first defined element. -/
theorem tail_ne_bot (c : Chain (WithBot α)) (k : ℕ) (hk : c k ≠ ⊥) (n : ℕ) :
    c (k + n) ≠ ⊥ :=
  ne_bot_of_le_ne_bot hk (c.monotone (Nat.le_add_right k n))

/-- Once a lifted chain becomes defined, its remaining values form a chain in
the original domain. -/
@[expose] def unbotChain (c : Chain (WithBot α)) (k : ℕ) (hk : c k ≠ ⊥) : Chain α where
  toFun n := (c (k + n)).unbot (tail_ne_bot c k hk n)
  monotone' _ _ h := unbot_mono _ _ (c.monotone (Nat.add_le_add_left h k))

private theorem isLUB_unbotChain (c : Chain (WithBot α)) (k : ℕ) (hk : c k ≠ ⊥) :
    IsLUB (Set.range c) (↑(ωSup (unbotChain c k hk)) : WithBot α) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    apply le_trans (c.monotone (Nat.le_add_left n k))
    change c (k + n) ≤ _
    rw [← coe_unbot (c (k + n)) (tail_ne_bot c k hk n), coe_le_coe]
    exact le_ωSup (unbotChain c k hk) n
  · intro bound hbound
    have hb : bound ≠ ⊥ := ne_bot_of_le_ne_bot hk (hbound (Set.mem_range_self k))
    lift bound to α using hb
    rw [coe_le_coe]
    apply ωSup_le
    intro n
    change (c (k + n)).unbot _ ≤ bound
    rw [unbot_le_iff]
    exact hbound (Set.mem_range_self (k + n))

/-- Every increasing sequence in the lifted order has a least upper bound. -/
theorem exists_isLUB_chain (c : Chain (WithBot α)) :
    ∃ x, IsLUB (Set.range c) x := by
  classical
  by_cases h : ∃ k, c k ≠ ⊥
  · obtain ⟨k, hk⟩ := h
    exact ⟨_, isLUB_unbotChain c k hk⟩
  · refine ⟨⊥, ?_, fun _ _ => bot_le⟩
    rintro _ ⟨n, rfl⟩
    have : c n = ⊥ := by simpa using not_exists.mp h n
    simp [this]

/-- The supremum of a lifted chain is bottom precisely when every term is
bottom, and otherwise is the lifted supremum of its defined tail. -/
noncomputable instance omegaCompletePartialOrder : OmegaCompletePartialOrder (WithBot α) where
  ωSup c := (exists_isLUB_chain c).choose
  le_ωSup c n := (exists_isLUB_chain c).choose_spec.1 (Set.mem_range_self n)
  ωSup_le c x hx := (exists_isLUB_chain c).choose_spec.2
    (by rintro _ ⟨n, rfl⟩; exact hx n)

/-- A nonbottom tail computes the supremum of the whole lifted chain. -/
theorem ωSup_eq_coe_unbotChain (c : Chain (WithBot α)) (k : ℕ) (hk : c k ≠ ⊥) :
    ωSup c = ↑(ωSup (unbotChain c k hk)) :=
  (ωSup_eq_of_isLUB (isLUB_unbotChain c k hk)).symm

/-- A lifted chain has no information exactly when every term is bottom. -/
theorem ωSup_eq_bot_iff (c : Chain (WithBot α)) : ωSup c = ⊥ ↔ ∀ n, c n = ⊥ := by
  constructor
  · intro h n
    exact le_bot_iff.mp (h ▸ le_ωSup c n)
  · intro h
    exact le_bot_iff.mp (ωSup_le c ⊥ (fun n => (h n).le))

/-- Including defined values preserves suprema of increasing sequences. -/
@[fun_prop] theorem ωScottContinuous_coe :
    ωScottContinuous (fun x : α => (x : WithBot α)) := by
  apply ωScottContinuous.of_monotone_map_ωSup ⟨coe_mono, fun c => ?_⟩
  apply ωSup_eq_of_isLUB
  constructor
  · rintro _ ⟨n, rfl⟩
    exact coe_le_coe.mpr (le_ωSup c n)
  · intro bound hb
    have h : (c 0 : WithBot α) ≤ bound := hb (Set.mem_range_self 0)
    obtain ⟨b, rfl, _⟩ := coe_le_iff.mp h
    apply coe_le_coe.mpr
    exact ωSup_le c b (fun n => coe_le_coe.mp (hb (Set.mem_range_self n)))

/-- The inclusion of a value into its lifted domain. -/
@[expose] noncomputable def coeContinuous : α →𝒄 WithBot α :=
  .ofFun (fun x => (x : WithBot α)) ωScottContinuous_coe

variable {β : Type*} [OmegaCompletePartialOrder β] [OrderBot β]

/-- Strict extension of a continuous map to a lifted argument. -/
@[expose] def extendFun (f : α →𝒄 β) : WithBot α → β := recBotCoe ⊥ f

@[simp] theorem extendFun_bot (f : α →𝒄 β) : extendFun f ⊥ = ⊥ := rfl

@[simp] theorem extendFun_coe (f : α →𝒄 β) (x : α) : extendFun f x = f x := rfl

theorem monotone_extendFun (f : α →𝒄 β) : Monotone (extendFun f) := by
  intro x y h
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe x =>
      obtain ⟨y, rfl, hxy⟩ := coe_le_iff.mp h
      exact f.monotone hxy

/-- Strict extension preserves increasing suprema, including chains that
become defined only after a finite delay. -/
@[fun_prop] theorem ωScottContinuous_extendFun (f : α →𝒄 β) :
    ωScottContinuous (extendFun f) := by
  apply ωScottContinuous.of_monotone_map_ωSup ⟨monotone_extendFun f, fun c => ?_⟩
  classical
  by_cases h : ∃ k, c k ≠ ⊥
  · obtain ⟨k, hk⟩ := h
    rw [ωSup_eq_coe_unbotChain c k hk, extendFun_coe, f.continuous]
    apply le_antisymm
    · apply ωSup_le
      intro n
      have heq : f (unbotChain c k hk n) = extendFun f (c (k + n)) := by
        rw [← coe_unbot (c (k + n)) (tail_ne_bot c k hk n)]
        rfl
      change f (unbotChain c k hk n) ≤ _
      rw [heq]
      exact le_ωSup (c.map ⟨extendFun f, monotone_extendFun f⟩) (k + n)
    · apply ωSup_le
      intro n
      apply le_trans (monotone_extendFun f (c.monotone (Nat.le_add_left n k)))
      change extendFun f (c (k + n)) ≤ _
      rw [← coe_unbot (c (k + n)) (tail_ne_bot c k hk n)]
      exact le_ωSup ((unbotChain c k hk).map f.toOrderHom) n
  · have hc : ∀ n, c n = ⊥ := by simpa using h
    rw [(ωSup_eq_bot_iff c).mpr hc, extendFun_bot]
    apply le_antisymm bot_le
    apply ωSup_le
    intro n
    change extendFun f (c n) ≤ ⊥
    simp [hc n]

/-- A continuous map extended strictly to a lifted domain. -/
@[expose] noncomputable def extend (f : α →𝒄 β) : WithBot α →𝒄 β :=
  .ofFun (extendFun f) (ωScottContinuous_extendFun f)

end WithBot
