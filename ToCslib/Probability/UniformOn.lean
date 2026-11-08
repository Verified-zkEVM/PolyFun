/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Uniform measures on finite sets

Mathlib's `ProbabilityTheory.uniformOn s` is the counting measure conditioned on `s`. It is a
probability measure when `s` is finite and nonempty, and zero when `s` is infinite and singletons
are measurable. This file adds the facts that finite uniform sampling uses. It computes the mass of
a point and of a decidable event under the uniform measure on a finite type or a finite set, and
integrals against it. The coordinates of a uniform pair are independent and uniform, and
bijections preserve uniform measures.

## Main statements

* `MeasurableEquiv.map_uniformOn`: a measurable equivalence carries the uniform measure on `s` to
  the uniform measure on the image of `s`. It needs no finiteness and no measurable singletons.
* `ProbabilityTheory.map_uniformOn_of_injOn`: a measurable map injective on `s` carries the uniform
  measure on `s` to the uniform measure on the image, when singletons are measurable.
* `ProbabilityTheory.map_uniformOn_univ_of_bijective` and
  `ProbabilityTheory.uniformOn_univ_map_equiv`: a bijection preserves the uniform measure on the
  whole space.
* `ProbabilityTheory.uniformOn_univ_prod`: the uniform measure on a product of finite types is the
  product of the uniform measures.

The measurable-space assumptions stay explicit. The results ask for measurable singletons where
they need them and install no discrete measurable-space instance.
-/

@[expose] public section

-- upstream candidate

noncomputable section

open MeasureTheory Set
open scoped ENNReal

/-! ## Invariance under measurable equivalences -/

namespace MeasurableEquiv

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A measurable equivalence carries the uniform measure on `s` to the uniform measure on the image
of `s`. The statement holds for every set: the counting measure, and so its conditioning on a set,
is invariant under measurable equivalences. -/
theorem map_uniformOn (e : α ≃ᵐ β) (s : Set α) :
    (ProbabilityTheory.uniformOn s).map e = ProbabilityTheory.uniformOn (e '' s) := by
  have hcount : (Measure.count : Measure α).map e = Measure.count := by
    ext t ht
    rw [e.map_apply, Measure.count_apply ht, Measure.count_apply (e.measurable ht),
      ← e.image_symm, e.symm.injective.encard_image]
  have himage (u : Set α) : Measure.count (e '' u) = Measure.count u := by
    rw [← hcount, e.map_apply, e.preimage_image]
  ext t ht
  rw [e.map_apply, ProbabilityTheory.uniformOn, ProbabilityTheory.uniformOn,
    ProbabilityTheory.cond_apply' (e.measurable ht), ProbabilityTheory.cond_apply' ht, himage,
    ← image_inter_preimage, himage]

/-- A measurable equivalence preserves the uniform measure on the whole space. -/
theorem map_uniformOn_univ (e : α ≃ᵐ β) :
    (ProbabilityTheory.uniformOn univ : Measure α).map e = ProbabilityTheory.uniformOn univ := by
  rw [map_uniformOn, image_univ_of_surjective e.surjective]

end MeasurableEquiv

namespace ProbabilityTheory

/-! ## Finite types -/

/-- A measurable space on a finite type with measurable singletons is discrete. -/
theorem MeasurableSpace.eq_top_of_finite {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (inferInstance : MeasurableSpace α) = ⊤ := by
  apply le_antisymm le_top
  rw [MeasurableSpace.le_def]
  intro s _
  exact MeasurableSet.of_discrete

/-- Every point in a finite space has mass `1 / |α|` under its uniform measure. -/
@[simp] theorem uniformOn_univ_apply_singleton
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] (a : α) :
    uniformOn (Set.univ : Set α) {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton]
  simp [div_eq_mul_inv]

/-- The uniform measure of a predicate on a finite type is its normalized cardinality. -/
theorem uniformOn_univ_apply_setOf {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α] (p : α → Prop) [DecidablePred p] :
    (uniformOn Set.univ : Measure α) {x | p x} =
      ((Finset.univ.filter p).card : ℝ≥0∞) / Fintype.card α := by
  rw [uniformOn_univ]
  have hset : {x | p x} = (↑(Finset.univ.filter p) : Set α) := by ext; simp
  rw [hset, Measure.count_apply_finset]

/-- Integrating over a finite uniform space averages the values of the integrand.
The formula also holds for the empty space. -/
theorem lintegral_uniformOn_univ {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α] (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂uniformOn Set.univ = (∑ a, f a) / Fintype.card α := by
  rw [lintegral_fintype]
  simp_rw [uniformOn_univ, Measure.count_singleton, one_div]
  rw [div_eq_mul_inv, Finset.sum_mul]

/-- The uniform measure on a product of finite spaces is the product of their uniform measures.
Thus the two coordinates are independent uniform draws. -/
theorem uniformOn_univ_prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Finite α] [Finite β] :
    uniformOn (Set.univ : Set (α × β)) =
      (uniformOn (Set.univ : Set α)).prod (uniformOn (Set.univ : Set β)) := by
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  calc
    uniformOn (Set.univ : Set (α × β)) {(a, b)} =
        (Fintype.card (α × β) : ℝ≥0∞)⁻¹ := uniformOn_univ_apply_singleton (a, b)
    _ = (Fintype.card α : ℝ≥0∞)⁻¹ * (Fintype.card β : ℝ≥0∞)⁻¹ := by
      simp only [Fintype.card_prod, Nat.cast_mul]
      exact ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inl (ENNReal.natCast_ne_top _))
    _ = ((uniformOn (Set.univ : Set α)).prod
        (uniformOn (Set.univ : Set β))) {(a, b)} := by
      rw [show ({(a, b)} : Set (α × β)) = {a} ×ˢ {b} by
        ext point
        simp]
      simp only [Measure.prod_prod, uniformOn_univ_apply_singleton]

/-! ## Finite sets -/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- Under the uniform measure on a finite set, a point of the set has mass `1 / #s` and a point
outside it has mass zero. -/
theorem uniformOn_finset_apply_singleton [DecidableEq α] (s : Finset α) (a : α) :
    uniformOn (s : Set α) {a} = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  rw [← Finset.coe_singleton, uniformOn_apply_finset]
  split_ifs with ha
  · simp [Finset.inter_singleton_of_mem ha]
  · simp [Finset.inter_singleton_of_notMem ha]

/-- The uniform measure on a finite set gives a predicate the fraction of the set that satisfies
it. -/
theorem uniformOn_finset_apply_setOf (s : Finset α) (p : α → Prop) [DecidablePred p] :
    uniformOn (s : Set α) {x | p x} = ((s.filter p).card : ℝ≥0∞) / s.card := by
  classical
  rw [← uniformOn_inter_self s.finite_toSet,
    show (s : Set α) ∩ {x | p x} = ↑(s.filter p) by ext; simp, uniformOn_apply_finset,
    Finset.inter_filter, Finset.inter_self]

/-! ## Invariance under injective maps and bijections -/

/-- A measurable map injective on `s` carries the uniform measure on `s` to the uniform measure on
the image of `s`. When `s` is infinite, both measures are zero. -/
theorem map_uniformOn_of_injOn {f : α → β} (hf : Measurable f) {s : Set α} (hinj : InjOn f s) :
    (uniformOn s).map f = uniformOn (f '' s) := by
  rcases s.finite_or_infinite with hs | hs
  · ext t ht
    have hst : (s ∩ f ⁻¹' t).Finite := hs.subset inter_subset_left
    rw [Measure.map_apply hf ht, uniformOn, uniformOn, cond_apply hs.measurableSet,
      cond_apply (hs.image f).measurableSet, ← image_inter_preimage,
      Measure.count_apply hs.measurableSet, Measure.count_apply (hs.image f).measurableSet,
      Measure.count_apply hst.measurableSet, Measure.count_apply (hst.image f).measurableSet,
      hinj.encard_image, (hinj.mono inter_subset_left).encard_image]
  · rw [(uniformOn_eq_zero).mpr (Or.inl hs), Measure.map_zero,
      (uniformOn_eq_zero).mpr (Or.inl (hs.image hinj))]

/-- Pushing the uniform measure on the whole space through a measurable bijection gives the
uniform measure on its codomain. Only forward measurability is needed. -/
theorem map_uniformOn_univ_of_bijective {f : α → β} (hf : Measurable f)
    (hbij : Function.Bijective f) :
    Measure.map f (uniformOn (Set.univ : Set α)) = uniformOn (Set.univ : Set β) := by
  rw [map_uniformOn_of_injOn hf hbij.injective.injOn, image_univ_of_surjective hbij.surjective]

/-- An equivalence of countable types carries the uniform measure on its domain to the uniform
measure on its codomain. Countability with measurable singletons makes the equivalence
measurable. -/
theorem uniformOn_univ_map_equiv [Countable α] (e : α ≃ β) :
    (uniformOn Set.univ : Measure α).map e = (uniformOn Set.univ : Measure β) :=
  map_uniformOn_univ_of_bijective Measurable.of_discrete e.bijective

end ProbabilityTheory
