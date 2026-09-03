/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Order.LeanOrder
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Lattice

/-!
# Canaries for the order bridge

Mathlib complete lattices instantiate core's `Lean.Order.CompleteLattice`, the bridged relation
is Mathlib's `≤` definitionally, and predicate-indexed suprema are `sSup` of the carved-out set.
-/

open Lean.Order

example : Lean.Order.CompleteLattice (Set Nat) := inferInstance
noncomputable example : Lean.Order.CompleteLattice ℕ∞ := inferInstance
noncomputable example : Lean.Order.CompleteLattice (Nat → ℕ∞) := inferInstance

example (a b : Set Nat) : (a ⊑ b) = (a ≤ b) := rfl
example (a b : ℕ∞) : (a ⊑ b) = (a ≤ b) := rfl

example (c : Set Nat → Prop) : Lean.Order.CompleteLattice.sup c = sSup {x | c x} :=
  Lean.Order.sup_eq_sSup c
