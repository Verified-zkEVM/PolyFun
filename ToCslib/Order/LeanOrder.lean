/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Init.Internal.Order
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Core's order hierarchy from Mathlib's

Core's weakest-precondition stack states assertions over `Lean.Order.CompleteLattice`, a
lattice class whose order is a bare relation `⊑` and whose suprema are indexed by predicates,
while Mathlib's program-logic carriers (`Prop`, `ℝ≥0∞`, function lattices) come with Mathlib's
`CompleteLattice`. The pinned Mathlib has no bridge between the two hierarchies; this file
supplies it. The instances are low priority so that core's own instances on `Prop` and on
function types win where both apply; they agree with these definitionally on the order relation,
and `Lean.Order.CompleteLattice` carries no further data, so the two routes to a lattice
structure on the same type are propositionally interchangeable.

The file also reverses core's order on Mathlib's `OrderDual`: `⊑` on `αᵒᵈ` is `⊑` on `α` read
backwards, and the supremum of a predicate is its infimum in `α`. On a Mathlib lattice this agrees,
at instance transparency, with the bridge of Mathlib's own dual order.
-/

public section

namespace Lean.Order

universe u

variable {α : Type u}

/-- Mathlib's `≤` as core's `⊑`. -/
instance (priority := low) instPartialOrderOfMathlib [_root_.PartialOrder α] :
    Lean.Order.PartialOrder α where
  rel := (· ≤ ·)
  rel_refl := le_refl _
  rel_trans := le_trans
  rel_antisymm := le_antisymm

/-- The relation underlying the bridged order is Mathlib's `≤`. -/
@[simp]
theorem rel_eq_le [_root_.PartialOrder α] (x y : α) :
    (@Lean.Order.PartialOrder.rel α instPartialOrderOfMathlib x y) = (x ≤ y) :=
  rfl

/-- Mathlib's complete lattice as core's, with `sSup` of the set a predicate carves out
supplying every predicate-indexed supremum. -/
instance (priority := low) instCompleteLatticeOfMathlib [_root_.CompleteLattice α] :
    Lean.Order.CompleteLattice α where
  toPartialOrder := instPartialOrderOfMathlib
  has_sup c := ⟨sSup {x | c x}, fun _ =>
    ⟨fun h y hy => le_trans (le_sSup (show y ∈ {x | c x} from hy)) h,
      fun h => sSup_le fun y hy => h y hy⟩⟩

/-- Core's predicate-indexed supremum is Mathlib's `sSup` of the carved-out set. -/
theorem sup_eq_sSup [_root_.CompleteLattice α] (c : α → Prop) :
    Lean.Order.CompleteLattice.sup c = sSup {x | c x} :=
  is_sup_unique (CompleteLattice.sup_spec c) fun _ =>
    ⟨fun h y hy => le_trans (le_sSup (show y ∈ {x | c x} from hy)) h,
      fun h => sSup_le fun y hy => h y hy⟩

/-- Core's order read backwards on the order dual. -/
instance instPartialOrderOrderDual [PartialOrder α] : PartialOrder αᵒᵈ where
  rel x y := PartialOrder.rel (α := α) y x
  rel_refl := PartialOrder.rel_refl (α := α)
  rel_trans h₁ h₂ := PartialOrder.rel_trans (α := α) h₂ h₁
  rel_antisymm h₁ h₂ := PartialOrder.rel_antisymm (α := α) h₂ h₁

/-- The order dual of a complete lattice: the supremum of a predicate is its infimum below. -/
instance instCompleteLatticeOrderDual [CompleteLattice α] : CompleteLattice αᵒᵈ :=
  { instPartialOrderOrderDual (α := α) with
    has_sup := fun c => ⟨inf (α := α) c, fun _ => inf_spec (α := α)⟩ }

/-- The dual order is the original order with its arguments swapped. -/
theorem rel_orderDual [PartialOrder α] (x y : αᵒᵈ) :
    PartialOrder.rel x y = PartialOrder.rel (α := α) (OrderDual.ofDual y) (OrderDual.ofDual x) :=
  rfl

end Lean.Order
