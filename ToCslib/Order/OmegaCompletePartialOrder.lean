/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Order.FixedPoints
public import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Least fixed points of continuous maps

Kleene iteration in a pointed omega-complete partial order. The carrier need
not be a complete lattice. In particular, distinct errors and returned values
need not have a common upper bound.

The approximants are Mathlib's `fixedPoints.iterateChain` started at bottom, so
`ContinuousHom.fix` is the supremum of that Kleene chain, and its unfolding and
leastness are Mathlib's `fixedPoints.ωSup_iterate_mem_fixedPoint` and
`fixedPoints.ωSup_iterate_le_prefixedPoint`. This file adds the pointed packaging,
fixed-point induction, fusion, and continuity in the recursive body. As the least
prefixed point (`ContinuousHom.isLeast_fix`), the result agrees with `OrderHom.lfp`
on a complete lattice (`ContinuousHom.fix_eq_lfp`).
-/

public section

-- upstream candidate: continuous-map constructions over Mathlib's omega-CPO API.

open OmegaCompletePartialOrder

namespace OmegaCompletePartialOrder.ωScottContinuous

/-- A fixed choice between continuous functions is continuous. -/
@[fun_prop] theorem ite {α β : Type*} [OmegaCompletePartialOrder α]
    [OmegaCompletePartialOrder β] (p : Prop) [Decidable p] {f g : α → β}
    (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
    ωScottContinuous (fun x => if p then f x else g x) := by
  by_cases h : p <;> simp only [h, ↓reduceIte] <;> assumption

end OmegaCompletePartialOrder.ωScottContinuous

namespace OmegaCompletePartialOrder.ContinuousHom

variable {α β γ : Type*} [OmegaCompletePartialOrder α]
  [OmegaCompletePartialOrder β] [OmegaCompletePartialOrder γ]

/-- Continuity into a space of continuous maps is pointwise continuity. -/
@[fun_prop] theorem ωScottContinuous_of_apply {f : α → (β →𝒄 γ)}
    (h : ∀ b, ωScottContinuous (fun a => f a b)) : ωScottContinuous f := by
  refine ωScottContinuous.of_monotone_map_ωSup (f := f) ⟨?_, ?_⟩
  · intro a a' haa
    exact fun b => (h b).monotone haa
  · intro c
    ext b
    exact (h b).map_ωSup c

/-- Packaging pointwise continuous functions preserves continuity in their parameter. -/
@[fun_prop] theorem ωScottContinuous_ofFun {f : α → β → γ}
    (h : ∀ a, ωScottContinuous (f a)) (hf : ωScottContinuous f) :
    ωScottContinuous (fun a => ContinuousHom.ofFun (f a) (h a)) := by
  apply ωScottContinuous_of_apply
  intro b
  exact (ωScottContinuous.apply b).comp hf

/-- Curry a continuous map on a product. -/
@[expose] def curry (f : (α × β) →𝒄 γ) : α →𝒄 (β →𝒄 γ) :=
  .ofFun (fun a => .ofFun (fun b => f (a, b))) (by
    apply ωScottContinuous_of_apply
    intro b
    exact f.ωScottContinuous.comp
      (Prod.ωScottContinuous.prodMk ωScottContinuous.id ωScottContinuous.const))

/-- Uncurry a continuous map into a space of continuous maps. -/
@[expose] def uncurry (f : α →𝒄 (β →𝒄 γ)) : (α × β) →𝒄 γ :=
  .ofFun (fun ab => f ab.1 ab.2)

/-- Exchange two continuous arguments. -/
@[expose] def swapArgs (f : α →𝒄 (β →𝒄 γ)) : β →𝒄 (α →𝒄 γ) :=
  curry (.ofFun (fun ba : β × α => f ba.2 ba.1))

instance orderBot [OrderBot β] : OrderBot (α →𝒄 β) where
  bot := .const ⊥
  bot_le _ _ := bot_le

variable [OrderBot α] [OrderBot β]

/-- The finite Kleene approximations, starting at bottom. -/
@[expose] def approximants (f : α →𝒄 α) : Chain α :=
  fixedPoints.iterateChain f ⊥ bot_le

@[simp] theorem approximants_zero (f : α →𝒄 α) : f.approximants 0 = ⊥ := rfl

@[simp] theorem approximants_succ (f : α →𝒄 α) (n : ℕ) :
    f.approximants (n + 1) = f (f.approximants n) :=
  Function.iterate_succ_apply' ..

/-- The least fixed point of a continuous map on a pointed omega-CPO. -/
@[expose] def fix (f : α →𝒄 α) : α := ωSup f.approximants

/-- Unfold one recursive call. -/
theorem map_fix (f : α →𝒄 α) : f f.fix = f.fix :=
  fixedPoints.ωSup_iterate_mem_fixedPoint f ⊥ bot_le

/-- Every finite approximation is below the least fixed point. -/
theorem approximants_le_fix (f : α →𝒄 α) (n : ℕ) : f.approximants n ≤ f.fix :=
  le_ωSup _ n

/-- The least fixed point is below every prefixed point. -/
theorem fix_le (f : α →𝒄 α) {x : α} (h : f x ≤ x) : f.fix ≤ x :=
  fixedPoints.ωSup_iterate_le_prefixedPoint f ⊥ bot_le h bot_le

/-- The least fixed point is the supremum of Mathlib's Kleene chain from bottom. -/
theorem fix_eq_ωSup_iterateChain (f : α →𝒄 α) :
    f.fix = ωSup (fixedPoints.iterateChain f ⊥ bot_le) := rfl

/-- The least fixed point is the least prefixed point. Together with
`OrderHom.isLeast_lfp_le`, this identifies it with `OrderHom.lfp` whenever the
carrier is also a complete lattice with the same order. -/
theorem isLeast_fix (f : α →𝒄 α) : IsLeast {x | f x ≤ x} f.fix :=
  ⟨(map_fix f).le, fun _ h => fix_le f h⟩

/-- For the omega-CPO structure of a complete lattice, the least fixed point of a
continuous map is its order-theoretic least fixed point. Carriers with a separate
omega-CPO instance, such as function types, use `isLeast_fix` instead. -/
theorem fix_eq_lfp {L : Type*} [CompleteLattice L] (f : L →𝒄 L) :
    f.fix = OrderHom.lfp f.toOrderHom :=
  (isLeast_fix f).unique (OrderHom.isLeast_lfp_le _)

/-- Induction over finite approximations followed by an admissibility step. -/
theorem fix_induction (f : α →𝒄 α) (p : α → Prop)
    (hbot : p ⊥) (hstep : ∀ x, p x → p (f x))
    (hclosed : ∀ c : Chain α, (∀ n, p (c n)) → p (ωSup c)) : p f.fix := by
  apply hclosed
  intro n
  induction n with
  | zero => exact hbot
  | succ n ih => simpa using hstep _ ih

/-- Continuous strict maps commuting with recursive bodies commute with their
least fixed points. Strictness rules out inserting a result at divergence. -/
theorem fix_fusion (f : α →𝒄 α) (g : β →𝒄 β) (h : α →𝒄 β)
    (hbot : h ⊥ = ⊥) (hcomm : ∀ x, h (f x) = g (h x)) :
    h f.fix = g.fix := by
  rw [fix, h.continuous, fix]
  congr 1
  ext n
  change h (f.approximants n) = g.approximants n
  induction n with
  | zero => exact hbot
  | succ n ih => simp only [approximants_succ, hcomm, ih]

/-- Each finite approximation depends continuously on the recursive body. -/
@[fun_prop] theorem ωScottContinuous_approximants (n : ℕ) :
    ωScottContinuous (fun f : α →𝒄 α => f.approximants n) := by
  induction n with
  | zero => exact ωScottContinuous.const
  | succ n ih =>
      simp only [approximants_succ]
      exact ωScottContinuous_apply (f := fun x : α →𝒄 α => x) ωScottContinuous.id ih

/-- Taking the least fixed point depends continuously on the recursive body. -/
@[fun_prop] theorem ωScottContinuous_fix : ωScottContinuous (fix : (α →𝒄 α) → α) := by
  let c : Chain ((α →𝒄 α) →𝒄 α) :=
    ⟨fun n => .ofFun (fun f => f.approximants n) (ωScottContinuous_approximants n),
      fun _ _ h f => f.approximants.monotone h⟩
  exact (ωSup c).ωScottContinuous

/-- Least fixed point as a continuous map, for recursive definitions with
parameters that can themselves contain partial information. -/
@[expose] def fixContinuous : (α →𝒄 α) →𝒄 α := .ofFun fix ωScottContinuous_fix

end OmegaCompletePartialOrder.ContinuousHom
