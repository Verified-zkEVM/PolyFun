/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.IPFunctor.Free.Substitution
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Command substitution and combined charge bounds

A substitution preserves a path-wise budget when each replacement tree costs at
most the charge of its source shape. Uniformly scaling those local charges scales
the whole-tree budget by the same factor. Simultaneous bounds for a finite family
of charges add to a bound for their sum.
-/

public section

universe uI uA uB uC uD uX

namespace IPFunctor.IFreeM

variable {I : Type uI} {P : Endo.{uI, uA, uB} I} {Q : Endo.{uI, uC, uD} I}
  {X : I → Type uX} {c : (s : I) → P.A s → ℕ} {c' : (s : I) → Q.A s → ℕ}

/-- Replacement trees bounded by each source charge preserve the whole-tree budget. -/
theorem IsChargeBound.substitute (h : CommandSubstitution P Q)
    (hh : ∀ s a, (h s a).IsChargeBound c' (c s a))
    {s : I} {x : IFreeM P X s} {n : ℕ} (hx : x.IsChargeBound c n) :
    (x.substitute h).IsChargeBound c' n := by
  induction x using IFreeM.inductionOn generalizing n with
  | pure _ _ => simp only [substitute_pure, isChargeBound_pure]
  | liftBind s a next ih =>
      rw [substitute_liftBind]
      have hn := hx.1
      rw [← Nat.add_sub_of_le hn]
      apply isChargeBound_bind (hh s a)
      intro t ⟨b, e⟩
      cases e
      exact ih b (hx.2 b)

/-- A local factor `k` in replacement costs gives the same factor in the total budget. -/
theorem IsChargeBound.substitute_mul (h : CommandSubstitution P Q) (k : ℕ)
    (hh : ∀ s a, (h s a).IsChargeBound c' (k * c s a))
    {s : I} {x : IFreeM P X s} {n : ℕ} (hx : x.IsChargeBound c n) :
    (x.substitute h).IsChargeBound c' (k * n) :=
  (hx.mul k).substitute h hh

variable {s : I}

/-- Simultaneous path-wise bounds add over a finite family of charges. -/
lemma isChargeBound_sum {ι : Type*} [Fintype ι]
    (c : ι → (s : I) → P.A s → ℕ) (b : ι → ℕ) {x : IFreeM P X s}
    (h : ∀ i, x.IsChargeBound (c i) (b i)) :
    x.IsChargeBound (fun s a => ∑ i, c i s a) (∑ i, b i) := by
  induction x using IFreeM.inductionOn generalizing b with
  | pure _ _ => exact isChargeBound_pure _ _
  | liftBind s a next ih =>
      rw [isChargeBound_liftBind_iff]
      refine ⟨Finset.sum_le_sum (fun i _ => (h i).1), fun answer => ?_⟩
      have hb := ih answer (fun i => b i - c i s a) (fun i => (h i).2 answer)
      rwa [Finset.sum_tsub_distrib _ (fun i _ => (h i).1)] at hb

end IPFunctor.IFreeM
