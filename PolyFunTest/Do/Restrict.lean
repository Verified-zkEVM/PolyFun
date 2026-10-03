/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Do.Algebra
public import PolyFun.Control.Monad.Algebra.Restrict
public import PolyFun.Control.Monad.Support.Instances
public import PolyFun.Control.Monad.Support.WP

/-!
# A restricted carrier on core's `vcgen`

The identity algebra of `PolyFunTest.Do.Algebra` restricted to `[0, 1] ⊆ ℕ∞` drives `vcgen`
like any other ordered algebra: the carrier's own bound is available as `le_top`, and the
restricted `wp` and triple are the original ones on underlying values. The module acknowledges the
tactic's experimental status with `set_option experimental.vcgen true`; `PolyFunTest.Do.Algebra`
pins the diagnostic itself.
-/

public section

open Std.WP MAlgOrdered

set_option experimental.vcgen true

/- The identity ordered algebra on `Det` at the extended naturals, installed locally. -/
attribute [local instance] instMAlgOrderedDetENat

/-- The identity algebra respects every bound. -/
theorem μ_const_le (c : ℕ∞) {α : Type} (x : Det α) :
    MAlgOrdered.μ (x >>= fun _ => pure c) ≤ c :=
  le_refl _

/-- The restriction to `[0, 1]`, installed locally as a core interpretation. -/
noncomputable local instance instWPMonadDetUnit : WPMonad Det (Set.Iic (1 : ℕ∞)) EStack⟨⟩ :=
  letI := restrictIic 1 (μ_const_le 1)
  MAlgOrdered.toWPMonad

/-- Agreement with the original `wp` on underlying values. -/
example (x : Det Nat) (post : Nat → Set.Iic (1 : ℕ∞)) (epost : EStack⟨⟩) :
    (wp x post epost).val =
      (letI := toWPMonad (m := Det) (l := ℕ∞); wp x (fun a => (post a).val) epost) :=
  wp_restrictIic_val 1 (μ_const_le 1) x post epost

/-- The restricted triple is the original one on underlying values. -/
example (x : Det Nat) (pre : Set.Iic (1 : ℕ∞)) (post : Nat → Set.Iic (1 : ℕ∞))
    (epost : EStack⟨⟩) :
    (letI := restrictIic 1 (μ_const_le 1);
      @Triple (Set.Iic (1 : ℕ∞)) EStack⟨⟩ (Det Nat) Nat _ _ x (toWP Nat) pre post epost) ↔
      @Triple ℕ∞ EStack⟨⟩ (Det Nat) Nat _ _ x (toWP Nat) pre.val (fun a => (post a).val) epost :=
  restrictIic_triple_iff 1 (μ_const_le 1) pre x post epost

/- `vcgen` decomposes a `do` block through the restricted algebra; the leaf is closed by the
carrier's bound. -/
example (c : Set.Iic (1 : ℕ∞)) :
    ⦃ c ⦄ (do let x ← pure 1; pure (x + 1) : Det Nat) ⦃ fun _ => ⟨1, Set.self_mem_Iic⟩ ⦄ := by
  vcgen
  exact le_top

/- A bound is not automatic: demonic correctness of an empty choice is vacuous. -/
example :
    (letI := MonadAttach.toWPMonadDemonic (m := SetM.{0});
     ¬ ∀ x : SetM Unit, wp x (fun _ => False) estack⟨⟩ → False) := by
  intro h
  apply h (∅ : Set Unit)
  intro a ha
  exact MonadAttach.SetM.canReturn_iff.mp ha
