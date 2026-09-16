/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Algebra
public import Mathlib.Order.CompleteLatticeIntervals

/-!
# Restricting an ordered monad algebra to a lower set

A quantitative carrier is often too large for the judgments one states over it: a probabilistic
program logic is stated over `[0, 1]`, not over `ℝ≥0∞`, and the invariants it wants — a
probability is at most `1` — are exactly what the smaller carrier makes automatic. When the
algebra respects the bound, that is, when no program's weakest precondition of the constant
postcondition `c` exceeds `c`, the algebra restricts to the lower set `Set.Iic c`, which Mathlib
equips with the complete lattice inherited from the carrier. `restrictIic` is that restriction:
its structure map is the original map on the underlying values, and its `wp` is the original
`wp` of the postcondition's values (`wp_restrictIic_val`).

The construction is not an instance, matching the rest of the ordered-algebra layer: the base
algebra and the bound are choices installed locally.
-/

@[expose] public section

universe u v

namespace MAlgOrdered

variable {m : Type u → Type v} {l : Type u} [Monad m] [LawfulMonad m] [CompleteLattice l]
  [MAlgOrdered m l]

/-- The elements of the lower set `Set.Iic c` that an algebra respecting the bound `c` produces:
the structure map, applied to the underlying values, stays below `c`. -/
theorem μ_map_val_le {c : l} (hc : ∀ {α : Type u} (x : m α), wp x (fun _ => c) ≤ c)
    (x : m (Set.Iic c)) : MAlgOrdered.μ (Subtype.val <$> x) ≤ c := by
  refine le_trans ?_ (hc x)
  rw [map_eq_pure_bind]
  exact MAlgOrdered.μ_bind_mono _ _ (fun a => by simp only [μ_pure]; exact a.2) x

/-- Restrict an ordered monad algebra to the lower set of a bound `c` that every program
respects. -/
@[instance_reducible]
def restrictIic (c : l) (hc : ∀ {α : Type u} (x : m α), wp x (fun _ => c) ≤ c) :
    MAlgOrdered m (Set.Iic c) where
  μ x := ⟨MAlgOrdered.μ (Subtype.val <$> x), μ_map_val_le hc x⟩
  μ_pure x := by
    apply Subtype.ext
    simp only [map_pure, μ_pure]
  μ_bind_mono f g h x := by
    change MAlgOrdered.μ (Subtype.val <$> (x >>= f)) ≤ MAlgOrdered.μ (Subtype.val <$> (x >>= g))
    simp only [map_bind]
    exact MAlgOrdered.μ_bind_mono _ _ (fun a => h a) x

/-- The restricted `wp` is the original `wp` of the postcondition's underlying values. -/
@[simp]
theorem wp_restrictIic_val (c : l) (hc : ∀ {α : Type u} (x : m α), wp x (fun _ => c) ≤ c)
    {α : Type u} (x : m α) (post : α → Set.Iic c) :
    (letI := restrictIic c hc; (MAlgOrdered.wp x post).val) =
      MAlgOrdered.wp x fun a => (post a).val := by
  change MAlgOrdered.μ (Subtype.val <$> (x >>= fun a => pure (post a))) =
    MAlgOrdered.μ (x >>= fun a => pure (post a).val)
  simp only [map_bind, map_pure]

/-- The restricted triple is the original triple on underlying values. -/
theorem restrictIic_triple_iff (c : l) (hc : ∀ {α : Type u} (x : m α), wp x (fun _ => c) ≤ c)
    {α : Type u} (pre : Set.Iic c) (x : m α) (post : α → Set.Iic c) :
    (letI := restrictIic c hc; MAlgOrdered.Triple pre x post) ↔
      MAlgOrdered.Triple pre.val x fun a => (post a).val := by
  change pre.val ≤ (letI := restrictIic c hc; (MAlgOrdered.wp x post).val) ↔
    pre.val ≤ MAlgOrdered.wp x fun a => (post a).val
  rw [wp_restrictIic_val]

end MAlgOrdered
