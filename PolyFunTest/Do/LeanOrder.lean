/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Order.LeanOrder
public import Std.Internal.Order.PropLattice

/-!
# Diamond canaries for the order bridge

Core ships its own `Lean.Order` instances on `Prop` (`Std.Internal.Order.PropLattice`, scoped
there and re-scoped under `Std.WP`) and on function types (`Init.Internal.Order.Basic`); the
bridged Mathlib instances of `ToCslib.Order.LeanOrder` must compute the same order relation and
the same suprema definitionally, so that lemmas stated over either route apply to goals stated
over the other. When the core instances are in scope they win instance search over the
low-priority bridge, and a WP-facing module that does not `open Std.WP` reasons through the
bridge instead; these canaries pin that both routes agree.
-/

open Lean.Order
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
