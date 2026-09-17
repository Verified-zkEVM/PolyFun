/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Algebra.Restrict
public import Mathlib.Data.ENat.Lattice

/-!
# Restricting an ordered monad algebra to a lower set

The identity algebra on a deterministic monad at the extended naturals respects every bound, so
it restricts to `Set.Iic c` for any `c`; the restricted `wp` and triple are the originals on
underlying values. This is the shape a probabilistic carrier `[0, 1] ⊆ ℝ≥0∞` takes downstream.
-/

@[expose] public section

namespace PolyFunTest.MonadAlgebraRestrict

open MAlgOrdered

/-- A deterministic monad with no global algebra. -/
def Det (α : Type) : Type := α

instance : Monad Det where
  pure a := a
  bind x f := f x

instance : LawfulMonad Det :=
  LawfulMonad.mk' Det (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

/-- The identity ordered algebra on `Det` at the extended naturals. -/
noncomputable local instance instMAlgOrderedDetENat : MAlgOrdered Det ℕ∞ where
  μ x := x
  μ_pure _ := rfl
  μ_bind_mono _ _ h x := h x

/-- The identity algebra respects every bound. -/
theorem wp_const_le (c : ℕ∞) {α : Type} (x : Det α) : MAlgOrdered.wp x (fun _ => c) ≤ c :=
  le_refl _

/-- The restriction to `[0, 1]`. -/
@[instance_reducible]
noncomputable def instUnit : MAlgOrdered Det (Set.Iic (1 : ℕ∞)) :=
  restrictIic 1 (wp_const_le 1)

/-- The restricted `wp` is the original one on values. -/
example (x : Det Nat) (post : Nat → Set.Iic (1 : ℕ∞)) :
    (letI := instUnit; (MAlgOrdered.wp x post).val) = MAlgOrdered.wp x fun a => (post a).val :=
  wp_restrictIic_val 1 (wp_const_le 1) x post

/-- The restricted triple is the original one on values; here a bound that the carrier makes
automatic: every `wp` into `[0, 1]` is at most `1`. -/
example (x : Det Nat) (post : Nat → Set.Iic (1 : ℕ∞)) :
    (letI := instUnit; MAlgOrdered.wp x post) ≤ ⟨1, Set.self_mem_Iic⟩ :=
  le_top

example (x : Det Nat) (pre : Set.Iic (1 : ℕ∞)) (post : Nat → Set.Iic (1 : ℕ∞)) :
    (letI := instUnit; MAlgOrdered.Triple pre x post) ↔
      MAlgOrdered.Triple pre.val x fun a => (post a).val :=
  restrictIic_triple_iff 1 (wp_const_le 1) pre x post

end PolyFunTest.MonadAlgebraRestrict
