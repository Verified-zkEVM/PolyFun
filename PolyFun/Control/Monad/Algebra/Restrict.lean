/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Algebra.WP
public import Mathlib.Order.CompleteLatticeIntervals

/-!
# Restricting an ordered monad algebra to a lower set

A quantitative carrier is often too large for the judgments one states over it: a probabilistic
program logic is stated over `[0, 1]`, not over `ℝ≥0∞`, and the invariants it wants — a
probability is at most `1` — are exactly what the smaller carrier makes automatic. When the
algebra respects the bound, that is, when no program's image of the constant `c` exceeds `c`,
the algebra restricts to the lower set `Set.Iic c`, which Mathlib equips with the complete
lattice inherited from the carrier. `restrictIic` is that restriction: its structure map is the
original map on the underlying values, and core's `wp` through it is the original `wp` of the
postcondition's values (`wp_restrictIic_val`).

The construction is not an instance, matching the rest of the ordered-algebra layer: the base
algebra and the bound are choices installed locally.
-/

@[expose] public section

universe u v

open Std.WP

namespace MAlgOrdered

variable {m : Type u → Type v} {l : Type u} [Monad m] [LawfulMonad m] [CompleteLattice l]
  [MAlgOrdered m l]

/-- The elements of the lower set `Set.Iic c` that an algebra respecting the bound `c` produces:
the structure map, applied to the underlying values, stays below `c`. -/
theorem μ_map_val_le {c : l}
    (hc : ∀ {α : Type u} (x : m α), MAlgOrdered.μ (x >>= fun _ => pure c) ≤ c)
    (x : m (Set.Iic c)) : MAlgOrdered.μ (Subtype.val <$> x) ≤ c := by
  refine le_trans ?_ (hc x)
  rw [map_eq_pure_bind]
  exact MAlgOrdered.μ_bind_mono _ _ (fun a => by simp only [μ_pure]; exact a.2) x

/-- Restrict an ordered monad algebra to the lower set of a bound `c` that every program
respects. -/
@[instance_reducible]
def restrictIic (c : l)
    (hc : ∀ {α : Type u} (x : m α), MAlgOrdered.μ (x >>= fun _ => pure c) ≤ c) :
    MAlgOrdered m (Set.Iic c) where
  μ x := ⟨MAlgOrdered.μ (Subtype.val <$> x), μ_map_val_le hc x⟩
  μ_pure x := by
    apply Subtype.ext
    simp only [map_pure, μ_pure]
  μ_bind_mono f g h x := by
    change MAlgOrdered.μ (Subtype.val <$> (x >>= f)) ≤ MAlgOrdered.μ (Subtype.val <$> (x >>= g))
    simp only [map_bind]
    exact MAlgOrdered.μ_bind_mono _ _ (fun a => h a) x

/-- Core's `wp` through the restricted algebra is the original `wp` of the postcondition's
underlying values. -/
@[simp]
theorem wp_restrictIic_val (c : l)
    (hc : ∀ {α : Type u} (x : m α), MAlgOrdered.μ (x >>= fun _ => pure c) ≤ c)
    {α : Type u} (x : m α) (post : α → Set.Iic c) (epost : EStack⟨⟩) :
    (letI := restrictIic c hc; letI := toWPMonad (m := m) (l := Set.Iic c);
      (wp x post epost).val) =
      (letI := toWPMonad (m := m) (l := l); wp x (fun a => (post a).val) epost) := by
  change MAlgOrdered.μ (Subtype.val <$> (x >>= fun a => pure (post a))) =
    MAlgOrdered.μ (x >>= fun a => pure (post a).val)
  simp only [map_bind, map_pure]

/-- Core's triple through the restricted algebra is the original triple on underlying values. -/
theorem restrictIic_triple_iff (c : l)
    (hc : ∀ {α : Type u} (x : m α), MAlgOrdered.μ (x >>= fun _ => pure c) ≤ c)
    {α : Type u} (pre : Set.Iic c) (x : m α) (post : α → Set.Iic c) (epost : EStack⟨⟩) :
    (letI := restrictIic c hc;
      @Std.WP.Triple (Set.Iic c) EStack⟨⟩ (m α) α _ _ x (toWP α) pre post epost) ↔
      @Std.WP.Triple l EStack⟨⟩ (m α) α _ _ x (toWP α) pre.val
        (fun a => (post a).val) epost := by
  let _ := restrictIic c hc
  rw [toWP_triple_iff, toWP_triple_iff]
  change pre.val ≤ MAlgOrdered.μ (Subtype.val <$> (x >>= fun a => pure (post a))) ↔ _
  simp only [map_bind, map_pure]

end MAlgOrdered
