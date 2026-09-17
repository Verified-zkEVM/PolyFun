/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Do.Algebra
public import PolyFun.Control.Monad.Algebra.Restrict
public import PolyFun.Control.Monad.Support.Instances

/-!
# A restricted carrier on core's `vcgen`

The identity algebra of `PolyFunTest.Do.Algebra` restricted to `[0, 1] ⊆ ℕ∞` drives `vcgen`
like any other ordered algebra: the carrier's own bound is available as `le_top`, and the
restricted `wp` is the original one on underlying values. Each `vcgen` call asserts the
experimental-tactic diagnostic with `#guard_msgs`, keeping `mvcgen.warning` enabled.
-/

public section

open Std.Internal.Do MAlgOrdered

/- The identity ordered algebra on `Det` at the extended naturals, installed locally. -/
attribute [local instance] instMAlgOrderedDetENat

/-- The identity algebra respects every bound. -/
theorem wp_const_le (c : ℕ∞) {α : Type} (x : Det α) : MAlgOrdered.wp x (fun _ => c) ≤ c :=
  le_refl _

/-- The restriction to `[0, 1]`, installed locally as a core interpretation. -/
noncomputable local instance instWPMonadDetUnit : WPMonad Det (Set.Iic (1 : ℕ∞)) EPost.Nil :=
  letI := restrictIic 1 (wp_const_le 1)
  MAlgOrdered.toWPMonad

/-- Agreement with the original `wp` on underlying values. -/
example (x : Det Nat) (post : Nat → Set.Iic (1 : ℕ∞)) (epost : EPost.Nil) :
    (wp x post epost).val = MAlgOrdered.wp x fun a => (post a).val :=
  wp_restrictIic_val 1 (wp_const_le 1) x post

/- `vcgen` decomposes a `do` block through the restricted algebra; the leaf is closed by the
carrier's bound. -/
/--
warning: The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it. Avoid using it in production projects.
-/
#guard_msgs in
example (c : Set.Iic (1 : ℕ∞)) :
    ⦃ c ⦄ (do let x ← pure 1; pure (x + 1) : Det Nat) ⦃ fun _ => ⟨1, Set.self_mem_Iic⟩ ⦄ := by
  vcgen
  exact le_top

/- A bound is not automatic: demonic correctness of an empty choice is vacuous. -/
example :
    (letI := MonadAttach.mAlgOrderedPropDemonic (m := SetM)
     ¬ ∀ x : SetM Unit, MAlgOrdered.wp x (fun _ => False) ≤ False) := by
  intro h
  have hempty := h (∅ : Set Unit)
  apply hempty
  apply (MonadAttach.wp_iff_allOutputs _ _).mpr
  intro a ha
  exact MonadAttach.SetM.canReturn_iff.mp ha
