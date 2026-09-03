/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Order.LeanOrder
public import Std.Internal.Do.Order.Basic

/-!
# Diamond canaries for the order bridge

Core ships its own `Lean.Order.CompleteLattice` instances on `Prop` and on function types in
`Std.Internal.Do.Order.Basic`; the bridged Mathlib instances of `ToCslib.Order.LeanOrder` must
compute the same order relation definitionally, so that lemmas stated over either route apply
to goals stated over the other.
-/

open Lean.Order

/-- Core's `Prop` instance is implication. -/
example (p q : Prop) : (p ⊑ q) = (p → q) := rfl

/-- The bridged Mathlib instance on `Prop` is implication too. -/
example (p q : Prop) : (@PartialOrder.rel Prop instPartialOrderOfMathlib p q) = (p → q) := rfl

/-- Core's function-space instance is the pointwise order. -/
example (f g : Nat → Prop) : (f ⊑ g) = ∀ n, f n → g n := rfl

/-- The bridged Mathlib instance on functions is the pointwise order too. -/
example (f g : Nat → Prop) :
    (@PartialOrder.rel (Nat → Prop) instPartialOrderOfMathlib f g) = ∀ n, f n → g n := rfl
