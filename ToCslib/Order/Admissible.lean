/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Order.DiscreteOmegaCompletePartialOrder
public import ToCslib.Order.SumOmegaCompletePartialOrder
public import ToCslib.Order.WithBotOmegaCompletePartialOrder

/-!
# Predicates closed under increasing suprema

Admissible predicates support fixed-point induction and logical relations for
lazy values. Closure is preserved by continuous inverse images, universal
quantification, disjoint sums, and adjoining bottom. `Admissible.fix_induction`
states fixed-point induction with this hypothesis.
-/

public section

-- upstream candidate: admissibility and its closure laws over Mathlib's omega-CPO API.

namespace OmegaCompletePartialOrder

variable {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

/-- A predicate closed under suprema of increasing sequences. -/
@[expose] def Admissible (p : α → Prop) : Prop :=
  ∀ c : Chain α, (∀ n, p (c n)) → p (ωSup c)

/-- Fixed-point induction for an admissible predicate: it holds at the least
fixed point when it holds at bottom and is preserved by the recursive body. -/
theorem Admissible.fix_induction [OrderBot α] {p : α → Prop} (hp : Admissible p)
    (f : α →𝒄 α) (hbot : p ⊥) (hstep : ∀ x, p x → p (f x)) : p f.fix :=
  ContinuousHom.fix_induction f p hbot hstep hp

/-- Continuous inverse images of admissible predicates are admissible. -/
theorem Admissible.comp {p : β → Prop} (hp : Admissible p) (f : α →𝒄 β) :
    Admissible (fun a => p (f a)) := by
  intro c hc
  rw [f.continuous]
  exact hp (c.map f.toOrderHom) hc

/-- Admissibility is preserved by universal quantification. -/
theorem Admissible.forall {ι : Sort*} {p : ι → α → Prop}
    (h : ∀ i, Admissible (p i)) : Admissible (fun a => ∀ i, p i a) :=
  fun c hc i => h i c (fun n => hc n i)

/-- Every predicate on an equality-ordered type is admissible. -/
theorem admissible_discrete {ι : Type*} (p : DiscreteOrder ι → Prop) : Admissible p :=
  fun _ hc => hc 0

/-- Disjoint case analysis preserves admissibility. -/
theorem Admissible.sum {p : α → Prop} {q : β → Prop} (hp : Admissible p) (hq : Admissible q) :
    Admissible (Sum.elim p q) := by
  intro c hc
  cases h : c 0 with
  | inl a =>
      rw [Sum.ωSup_eq_inl c h]
      apply hp
      intro n
      have hn := hc n
      rw [← Sum.inl_inlChain c h n] at hn
      exact hn
  | inr b =>
      let swapped := c.map ⟨Sum.swap, Sum.swap_monotone⟩
      have hs : swapped 0 = Sum.inl b := by simp [swapped, h]
      have supc : ωSup c = (ωSup swapped).swap := by
        have hh := Sum.ωScottContinuous_swap.map_ωSup c
        simpa only [Sum.swap_swap] using congrArg Sum.swap hh
      rw [supc, Sum.ωSup_eq_inl swapped hs]
      apply hq
      intro n
      have heq := congrArg Sum.swap (Sum.inl_inlChain swapped hs n)
      have hn := hc n
      have heq' : Sum.inr (Sum.inlChain swapped hs n) = c n := by
        simpa only [Sum.swap_inl, swapped, Chain.coe_map, Function.comp_apply,
          OrderHom.coe_mk, Sum.swap_swap] using heq
      rw [← heq'] at hn
      exact hn

/-- An admissible predicate on values remains admissible when bottom is
accepted in the lifted domain. -/
theorem Admissible.withBot {p : α → Prop} (hp : Admissible p) :
    Admissible (WithBot.recBotCoe True p) := by
  intro c hc
  classical
  by_cases h : ∃ k, c k ≠ ⊥
  · obtain ⟨k, hk⟩ := h
    rw [WithBot.ωSup_eq_coe_unbotChain c k hk]
    apply hp
    intro n
    have hn := hc (k + n)
    rw [← WithBot.coe_unbot (c (k + n)) (WithBot.tail_ne_bot c k hk n)] at hn
    exact hn
  · rw [(WithBot.ωSup_eq_bot_iff c).mpr (by simpa using h)]
    trivial

end OmegaCompletePartialOrder
