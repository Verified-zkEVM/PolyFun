/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Do.Algebra
public import PolyFun.Control.Monad.ExactWP

/-!
# Upper bounds on core's `vcgen` through the order dual

An exact interpretation is sound on the order duals as well (`ExactWPMonad.dual`). The identity
algebra of `PolyFunTest.Do.Algebra`, read in `ℕ∞ᵒᵈ`, is a core interpretation whose triples are
upper bounds: `vcgen` decomposes a `do` block exactly as for lower bounds, and the remaining
condition compares the program's value with the bound in the reversed order. The dual reading is
exact again, and exactness is recovered from it (`ExactWPMonad.of_dual`). The module acknowledges
the tactic's experimental status with `set_option experimental.vcgen true`;
`PolyFunTest.Do.Algebra` pins the diagnostic itself.
-/

public section

open Std.WP MAlgOrdered OrderDual

set_option experimental.vcgen true

attribute [local instance] instMAlgOrderedDetENat

/-- The upper-bound reading of the identity algebra, installed locally. -/
noncomputable local instance instWPMonadDetDual : WPMonad Det ℕ∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  letI := toWPMonad (m := Det) (l := ℕ∞)
  ExactWPMonad.dual

/- `vcgen` walks a `do` block under the dual reading; the leaf compares values in reverse. -/
example :
    ⦃ toDual (3 : ℕ∞) ⦄ (do let x ← pure 1; pure (x + 1) : Det Nat)
      ⦃ fun (n : ℕ) => toDual (n : ℕ∞) ⦄ := by
  vcgen
  simp only [Lean.Order.rel_eq_le]
  decide

/-- The dual reading is itself exact. -/
example : ExactWPMonad Det ℕ∞ᵒᵈ EStack⟨⟩ᵒᵈ := inferInstance

/-- Exactness is recovered from soundness on the dual. -/
example :
    @ExactWPMonad Det ℕ∞ EStack⟨⟩ _ _ _ (toWPMonad (m := Det) (l := ℕ∞)) :=
  ExactWPMonad.of_dual _ (letI := toWPMonad (m := Det) (l := ℕ∞); ExactWPMonad.dual)
    fun _ _ _ => rfl
