/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Order.LeanOrder
public import Std.Internal.Order.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.SetNotation

/-!
# Canaries for the order bridge

Mathlib complete lattices instantiate core's `Lean.Order.CompleteLattice`, the bridged relation
is Mathlib's `≤` definitionally, and predicate-indexed suprema are `sSup` of the carved-out set.

Core ships its own `Lean.Order` instances on `Prop` (`Std.Internal.Order.Basic`, scoped
there and re-scoped under `Std.WP`) and on function types (`Init.Internal.Order.Basic`); the
bridged Mathlib instances must compute the same order relation and the same suprema
definitionally, so that lemmas stated over either route apply to goals stated over the other.
When the core instances are in scope they win instance search over the low-priority bridge, and
a WP-facing module that does not `open Std.WP` reasons through the bridge instead; the diamond
canaries pin that both routes agree.
-/

open Lean.Order

/-! ## Mathlib lattices through the bridge -/

example : Lean.Order.CompleteLattice (Set Nat) := inferInstance
noncomputable example : Lean.Order.CompleteLattice ℕ∞ := inferInstance
noncomputable example : Lean.Order.CompleteLattice (Nat → ℕ∞) := inferInstance

example (a b : Set Nat) : (a ⊑ b) = (a ≤ b) := rfl
example (a b : ℕ∞) : (a ⊑ b) = (a ≤ b) := rfl

example (c : Set Nat → Prop) : Lean.Order.CompleteLattice.sup c = sSup {x | c x} :=
  Lean.Order.sup_eq_sSup c

/-! ## Diamonds with core's instances -/

section Diamonds

open scoped Std.Internal.Order

/-- Core's `Prop` instance is implication. -/
example (p q : Prop) : (p ⊑ q) = (p → q) := rfl

/-- With the core instances open, `⊑` on `Prop` is core's instance. -/
example : (inferInstance : Lean.Order.PartialOrder Prop) =
    Std.Internal.Order.instPartialOrderProp := rfl

/-- The bridged Mathlib instance on `Prop` is implication too. -/
example (p q : Prop) : (@PartialOrder.rel Prop instPartialOrderOfMathlib p q) = (p → q) := rfl

/-- Both `Prop` orders are the same relation. -/
example : @PartialOrder.rel Prop Std.Internal.Order.instPartialOrderProp =
    @PartialOrder.rel Prop instPartialOrderOfMathlib := rfl

/-- Both `Prop` suprema are the same predicate: "some element of the set is true". -/
example (c : Prop → Prop) :
    @Lean.Order.CompleteLattice.sup Prop Std.Internal.Order.instCompleteLatticeProp c =
      @Lean.Order.CompleteLattice.sup Prop instCompleteLatticeOfMathlib c := rfl

/-- Core's function-space instance is the pointwise order. -/
example (f g : Nat → Prop) : (f ⊑ g) = ∀ n, f n → g n := rfl

/-- The bridged Mathlib instance on functions is the pointwise order too. -/
example (f g : Nat → Prop) :
    (@PartialOrder.rel (Nat → Prop) instPartialOrderOfMathlib f g) = ∀ n, f n → g n := rfl

/-- Core's order reversed on the order dual is the bridge of Mathlib's dual order, at instance
transparency. -/
example : (instPartialOrderOrderDual : Lean.Order.PartialOrder (Nat → Prop)ᵒᵈ) =
    (instPartialOrderOfMathlib : Lean.Order.PartialOrder (Nat → Prop)ᵒᵈ) := by
  with_reducible_and_instances rfl

/-- The two complete lattices on the order dual agree at instance transparency. -/
example : (instCompleteLatticeOrderDual : Lean.Order.CompleteLattice (Nat → Prop)ᵒᵈ) =
    (instCompleteLatticeOfMathlib : Lean.Order.CompleteLattice (Nat → Prop)ᵒᵈ) := by
  with_reducible_and_instances rfl

end Diamonds
