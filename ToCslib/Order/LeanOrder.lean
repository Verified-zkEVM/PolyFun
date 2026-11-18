/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Init.Internal.Order
public import Std.Internal.Order.Heyting
public import Mathlib.Order.CompleteBooleanAlgebra

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

On a bridged carrier, core's lattice operations are Mathlib's. The transfer lemmas of the namespace
`LeanOrder` (`LeanOrder.top_eq_top`, `LeanOrder.meet_eq_inf`, …) rewrite each into Mathlib's
spelling, and `simp` uses them.
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

/-! ## Lattice operations across the bridge

`Std.Internal.Order` defines core's `top`, `meet`, `join`, `iInf`, `iSup`, `himp`, and `⌜·⌝` from
predicate-indexed suprema, and `bot` as the supremum of the empty chain. On a carrier whose
`Lean.Order.CompleteLattice` is the bridge above, they are Mathlib's `⊤`, `⊓`, `⊔`, `⨅`, `⨆`, `⇨`,
`if p then ⊤ else ⊥`, and `⊥`.

The transfer lemmas live in the namespace `LeanOrder`, outside `Lean.Order`. A declaration in
`Lean.Order`, or in a namespace below it, is elaborated with `Lean.Order` open. That activates
core's scoped `⊤`, `⊓`, `⊔`, `⨅`, `⨆`, and `⇨` notation beside Mathlib's, and it resolves `le_top`
and `le_inf` to core's lemmas. Outside `Lean.Order`, the statements use Mathlib's notation and name
core's operations in full. -/

namespace LeanOrder

universe u v

section CompleteLattice

variable {α : Type u} [CompleteLattice α]

/-- On a Mathlib complete lattice, core's top element is Mathlib's `⊤`. -/
@[simp]
theorem top_eq_top : (Lean.Order.top : α) = ⊤ :=
  le_antisymm le_top (Lean.Order.le_top (⊤ : α))

/-- On a Mathlib complete lattice, core's bottom element, the supremum of the empty chain under
the chain-complete order of the lattice, is Mathlib's `⊥`. -/
@[simp]
theorem bot_eq_bot : @Lean.Order.bot α Lean.Order.instCCPOOfCompleteLattice = ⊥ :=
  le_antisymm (@Lean.Order.bot_le α Lean.Order.instCCPOOfCompleteLattice ⊥) bot_le

/-- On a Mathlib complete lattice, core's binary meet is Mathlib's `⊓`. -/
@[simp]
theorem meet_eq_inf (x y : α) : Lean.Order.meet x y = x ⊓ y :=
  le_antisymm (le_inf (Lean.Order.meet_le_left x y) (Lean.Order.meet_le_right x y))
    (Lean.Order.le_meet _ x y inf_le_left inf_le_right)

/-- On a Mathlib complete lattice, core's binary join is Mathlib's `⊔`. -/
@[simp]
theorem join_eq_sup (x y : α) : Lean.Order.join x y = x ⊔ y :=
  le_antisymm (Lean.Order.join_le x y _ le_sup_left le_sup_right)
    (sup_le (Lean.Order.left_le_join x y) (Lean.Order.right_le_join x y))

/-- On a Mathlib complete lattice, core's infimum of an indexed family is Mathlib's `⨅`. -/
@[simp]
theorem iInf_eq_iInf {ι : Sort v} (f : ι → α) : Lean.Order.iInf f = ⨅ i, f i :=
  le_antisymm (le_iInf fun i => Lean.Order.iInf_le f i)
    (Lean.Order.le_iInf f _ fun i => iInf_le f i)

/-- On a Mathlib complete lattice, core's supremum of an indexed family is Mathlib's `⨆`. -/
@[simp]
theorem iSup_eq_iSup {ι : Sort v} (f : ι → α) : Lean.Order.iSup f = ⨆ i, f i :=
  le_antisymm (Lean.Order.iSup_le f _ fun i => le_iSup f i)
    (iSup_le fun i => Lean.Order.le_iSup f i)

/-- On a Mathlib complete lattice, core's embedding `⌜p⌝` of a proposition is `⊤` when `p` holds
and `⊥` otherwise. It is not a `simp` lemma, since its right-hand side needs `p` decidable. -/
theorem ofProp_eq_ite (p : Prop) [Decidable p] :
    (Lean.Order.CompleteLattice.ofProp p : α) = if p then ⊤ else ⊥ := by
  by_cases hp : p
  · rw [Lean.Order.CompleteLattice.ofProp_eq_top hp, top_eq_top]
    simp only [hp, ↓reduceIte]
  · rw [Lean.Order.CompleteLattice.ofProp_congr (iff_false_intro hp),
      Lean.Order.CompleteLattice.ofProp_false, bot_eq_bot]
    simp only [hp, ↓reduceIte]

end CompleteLattice

/-- On a Mathlib frame, a complete lattice whose meets distribute over suprema, core's Heyting
implication is Mathlib's `⇨`. -/
@[simp]
theorem himp_eq_himp {α : Type u} [Order.Frame α] (x y : α) : Lean.Order.himp x y = x ⇨ y := by
  refine le_antisymm ?_ ?_
  · change Lean.Order.CompleteLattice.sup _ ≤ _
    rw [Lean.Order.sup_eq_sSup]
    exact sSup_le fun z hz => le_himp_iff.2 (by rw [inf_comm, ← meet_eq_inf]; exact hz)
  · exact Lean.Order.le_himp_of_meet_le_left (a := x) (b := y) (x := x ⇨ y)
      (show Lean.Order.meet x (x ⇨ y) ≤ y by rw [meet_eq_inf]; exact inf_himp_le)

end LeanOrder
