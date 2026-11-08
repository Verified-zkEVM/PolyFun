/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.EvalDistEq
public import ToCslib.Probability.UniformOn

/-!
# Uniform output measures

`EvalDist.IsUniformOn mx s` states that the computation `mx` is a uniform draw from the set `s`:
in every measurable structure on its outputs with measurable singletons, its output measure is
Mathlib's `ProbabilityTheory.uniformOn s`. `EvalDist.IsUniform mx` is the case `s = Set.univ`.
The predicate names no sampler, so it applies to a computation in any monad with a measure
semantics. On a finite type the measurable structure is irrelevant, and one output measure
suffices to establish the predicate (`EvalDist.IsUniformOn.of_evalDist_eq`).

## Main statements

Under lawful semantics:

* `EvalDist.IsUniformOn.map_of_injOn`: a map injective on `s` turns a uniform draw from `s` into a
  uniform draw from the image of `s`. In particular a bijection keeps a uniform draw uniform
  (`EvalDist.IsUniform.map_of_bijective`), and an injection makes it uniform on its range
  (`EvalDist.IsUniform.map_of_injective`).
* `EvalDist.IsUniformOn.prFail_eq_zero`: a uniform draw from a finite nonempty set never fails.
* `EvalDist.IsUniform.pair`: two independent uniform draws are a uniform draw from the product.
* `EvalDist.IsUniformOn.evalDistEq`: two uniform draws from the same set, possibly in different
  monads, are equal in distribution, and equality in distribution preserves uniformity
  (`EvalDistEq.isUniformOn_iff`).
* `EvalDist.IsUniformOn.prEvent_eq` and `EvalDist.IsUniform.prEvent_eq`: an event of a uniform draw
  has the probability of the fraction of outputs that satisfy it.
* `EvalDist.IsUniform.evalDistEq_bind_comp`: reindexing a uniform draw by a bijection does not
  change the distribution of any continuation.

Event probabilities and equality in distribution are stated for outputs in `Type`.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

universe u v v'

namespace EvalDist

section defs

variable {m : Type u → Type v} [EvalDistSemantics m] {α : Type u}

/-- The computation `mx` is a uniform draw from `s`: in every measurable structure on its outputs
with measurable singletons, its output measure is the uniform measure on `s`. The uniform measure
on an infinite set is zero, so a uniform draw from an infinite set always fails. -/
structure IsUniformOn (mx : m α) (s : Set α) : Prop where
  /-- The output measure is the uniform measure on `s` in every structure with measurable
  singletons. -/
  evalDist_eq : ∀ [MeasurableSpace α] [MeasurableSingletonClass α], evalDist mx = uniformOn s

/-- The computation `mx` is a uniform draw from all of its output type. -/
abbrev IsUniform (mx : m α) : Prop :=
  IsUniformOn mx Set.univ

end defs

namespace IsUniformOn

variable {m : Type u → Type v} [EvalDistSemantics m] {α β : Type u} {mx : m α} {s : Set α}

/-- On a finite type, the output measure in one structure with measurable singletons determines
uniformity, because every such structure is discrete. -/
theorem of_evalDist_eq [Finite α] [hα : MeasurableSpace α] [hs : MeasurableSingletonClass α]
    (h : evalDist mx = uniformOn s) : IsUniformOn mx s := by
  constructor
  intro hα' hs'
  obtain rfl := @MeasurableSpace.eq_top_of_finite α _ hα hs
  obtain rfl := @MeasurableSpace.eq_top_of_finite α _ hα' hs'
  exact h

/-- On a finite type, uniformity is the uniform output measure in any one structure with
measurable singletons. -/
theorem _root_.EvalDist.isUniformOn_iff_evalDist_eq [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] : IsUniformOn mx s ↔ evalDist mx = uniformOn s :=
  ⟨fun h ↦ h.evalDist_eq, of_evalDist_eq⟩

section lawful

variable [Monad m] [LawfulMonad m] [LawfulEvalDistSemantics m]

/-- A map injective on `s` turns a uniform draw from `s` into a uniform draw from the image of
`s`. -/
theorem map_of_injOn (h : IsUniformOn mx s) {f : α → β} (hf : InjOn f s) :
    IsUniformOn (f <$> mx) (f '' s) := by
  constructor
  intro _ _
  let : MeasurableSpace α := ⊤
  rw [evalDist_map_of_discrete, h.evalDist_eq, map_uniformOn_of_injOn Measurable.of_discrete hf]

/-- A uniform draw from a finite nonempty set never fails. -/
theorem prFail_eq_zero (h : IsUniformOn mx s) (hs : s.Finite) (hne : s.Nonempty) :
    prFail mx = 0 := by
  let : MeasurableSpace α := ⊤
  have := isProbabilityMeasure_uniformOn hs hne
  rw [prFail_eq_defect, h.evalDist_eq, Measure.defect, measure_univ, tsub_self]

/-- A uniform draw from an infinite or empty set always fails. -/
theorem prFail_eq_one (h : IsUniformOn mx s) (hs : s.Infinite ∨ s = ∅) : prFail mx = 1 := by
  let : MeasurableSpace α := ⊤
  rw [prFail_eq_defect, h.evalDist_eq, uniformOn_eq_zero.mpr hs, Measure.defect]
  simp

end lawful

end IsUniformOn

namespace IsUniform

variable {m : Type u → Type v} [EvalDistSemantics m] [Monad m] [LawfulMonad m]
  [LawfulEvalDistSemantics m] {α β : Type u} {mx : m α}

/-- A bijection keeps a uniform draw uniform. -/
theorem map_of_bijective (h : IsUniform mx) {f : α → β} (hf : f.Bijective) :
    IsUniform (f <$> mx) := by
  simpa only [image_univ_of_surjective hf.surjective] using h.map_of_injOn hf.injective.injOn

/-- An injection turns a uniform draw into a uniform draw from its range. -/
theorem map_of_injective (h : IsUniform mx) {f : α → β} (hf : f.Injective) :
    IsUniformOn (f <$> mx) (range f) := by
  simpa only [image_univ] using h.map_of_injOn hf.injOn

/-- An equivalence keeps a uniform draw uniform. -/
theorem map_equiv (h : IsUniform mx) (e : α ≃ β) : IsUniform (e <$> mx) :=
  h.map_of_bijective e.bijective

/-- A uniform draw from a finite nonempty type never fails. -/
theorem prFail_eq_zero [Finite α] [Nonempty α] (h : IsUniform mx) : prFail mx = 0 :=
  IsUniformOn.prFail_eq_zero h finite_univ univ_nonempty

/-- Two independent uniform draws from finite types are a uniform draw from their product. -/
theorem pair [Finite α] [Finite β] {my : m β} (hx : IsUniform mx)
    (hy : IsUniform my) : IsUniform (do let x ← mx; let y ← my; return (x, y)) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  refine IsUniformOn.of_evalDist_eq (α := α × β) ?_
  rw [evalDist_pair, hx.evalDist_eq, hy.evalDist_eq, uniformOn_univ_prod]

end IsUniform

/-! ## Events and equality in distribution -/

section events

variable {m : Type → Type v} {m' : Type → Type v'} [EvalDistSemantics m] [EvalDistSemantics m']
  [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m'] [LawfulEvalDistSemantics m]
  [LawfulEvalDistSemantics m'] {α β γ : Type} {mx : m α} {s : Set α}

namespace IsUniformOn

/-- Two uniform draws from the same set are equal in distribution. -/
theorem evalDistEq {my : m' α} (hx : IsUniformOn mx s) (hy : IsUniformOn my s) :
    EvalDistEq mx my := by
  let : MeasurableSpace α := ⊤
  exact EvalDistEq.of_evalDist_eq (hx.evalDist_eq.trans hy.evalDist_eq.symm)

/-- An event of a uniform draw from a finite set has the probability of the fraction of the set
that satisfies it. -/
theorem prEvent_eq {s : Finset α} (h : IsUniformOn mx s) (p : α → Prop) [DecidablePred p] :
    prEvent (p <$> mx) = ((s.filter p).card : ℝ≥0∞) / s.card := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, h.evalDist_eq, uniformOn_finset_apply_setOf]

/-- A uniform draw from a finite set returns a given element of the set with probability
`1 / #s`, and an element outside the set with probability zero. -/
theorem prEvent_eq_singleton [DecidableEq α] {s : Finset α} (h : IsUniformOn mx s) (a : α) :
    prEvent ((fun x ↦ x = a) <$> mx) = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_singleton, h.evalDist_eq, uniformOn_finset_apply_singleton]

/-- An event of a uniform draw from a finite set has probability zero exactly when no element of
the set satisfies it. -/
theorem prEvent_eq_zero_iff (h : IsUniformOn mx s) (hs : s.Finite) (p : α → Prop) :
    prEvent (p <$> mx) = 0 ↔ ∀ x ∈ s, ¬p x := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, h.evalDist_eq, uniformOn_eq_zero_iff hs,
    eq_empty_iff_forall_notMem]
  simp

/-- An event of a uniform draw from a finite set has positive probability exactly when some
element of the set satisfies it. -/
theorem prEvent_pos_iff (h : IsUniformOn mx s) (hs : s.Finite) (p : α → Prop) :
    0 < prEvent (p <$> mx) ↔ ∃ x ∈ s, p x := by
  rw [pos_iff_ne_zero, Ne, h.prEvent_eq_zero_iff hs]
  simp

/-- An event of a uniform draw from a finite nonempty set has probability one exactly when every
element of the set satisfies it. -/
theorem prEvent_eq_one_iff (h : IsUniformOn mx s) (hs : s.Finite) (hne : s.Nonempty)
    (p : α → Prop) : prEvent (p <$> mx) = 1 ↔ ∀ x ∈ s, p x := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, h.evalDist_eq]
  exact ⟨fun h₁ _ hx ↦ pred_true_of_uniformOn_eq_one h₁ hx,
    fun h₁ ↦ uniformOn_eq_one_of hs hne h₁⟩

end IsUniformOn

/-- Equality in distribution preserves uniformity. -/
theorem _root_.EvalDistEq.isUniformOn_iff {my : m' α} (h : EvalDistEq mx my) :
    IsUniformOn mx s ↔ IsUniformOn my s :=
  ⟨fun hx ↦ ⟨h.evalDist_eq.symm.trans hx.evalDist_eq⟩,
    fun hy ↦ ⟨h.evalDist_eq.trans hy.evalDist_eq⟩⟩

namespace IsUniform

/-- An event of a uniform draw from a finite type has the probability of the fraction of outputs
that satisfy it. -/
theorem prEvent_eq [Fintype α] (h : IsUniform mx) (p : α → Prop) [DecidablePred p] :
    prEvent (p <$> mx) = ((Finset.univ.filter p).card : ℝ≥0∞) / Fintype.card α := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, h.evalDist_eq, uniformOn_univ_apply_setOf]

/-- A uniform draw from a finite type returns any given output with probability `1 / |α|`. -/
theorem prEvent_eq_singleton [Fintype α] (h : IsUniform mx) (a : α) :
    prEvent ((fun x ↦ x = a) <$> mx) = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_singleton, h.evalDist_eq, uniformOn_univ_apply_singleton]

/-- An event of a uniform draw from a finite type has probability zero exactly when no output
satisfies it. -/
theorem prEvent_eq_zero_iff [Finite α] (h : IsUniform mx) (p : α → Prop) :
    prEvent (p <$> mx) = 0 ↔ ∀ x, ¬p x := by
  simpa only [mem_univ, true_imp_iff] using IsUniformOn.prEvent_eq_zero_iff h finite_univ p

/-- An event of a uniform draw from a finite type has positive probability exactly when some
output satisfies it. -/
theorem prEvent_pos_iff [Finite α] (h : IsUniform mx) (p : α → Prop) :
    0 < prEvent (p <$> mx) ↔ ∃ x, p x := by
  simpa only [mem_univ, true_and] using IsUniformOn.prEvent_pos_iff h finite_univ p

/-- An event of a uniform draw from a finite nonempty type has probability one exactly when every
output satisfies it. -/
theorem prEvent_eq_one_iff [Finite α] [Nonempty α] (h : IsUniform mx) (p : α → Prop) :
    prEvent (p <$> mx) = 1 ↔ ∀ x, p x := by
  simpa only [mem_univ, true_imp_iff] using
    IsUniformOn.prEvent_eq_one_iff h finite_univ univ_nonempty p

/-- A bijection between the outputs of two uniform draws transports their events. -/
theorem prEvent_comp_of_bijective {my : m' β} (hx : IsUniform mx) (hy : IsUniform my)
    {f : α → β} (hf : f.Bijective) (p : β → Prop) :
    prEvent ((fun x ↦ p (f x)) <$> mx) = prEvent (p <$> my) := by
  rw [← prEvent_map]
  exact ((hx.map_of_bijective hf).evalDistEq hy).prEvent_eq p

/-- Reindexing a uniform draw by a bijection onto the outputs of another uniform draw does not
change the distribution of a continuation. -/
theorem evalDistEq_bind_comp {my : m β} (hx : IsUniform mx) (hy : IsUniform my) {e : α → β}
    (he : e.Bijective) (f : β → m γ) :
    EvalDistEq (mx >>= fun x ↦ f (e x)) (my >>= f) := by
  rw [← bind_map_left]
  exact ((hx.map_of_bijective he).evalDistEq hy).bind_left f

end IsUniform

end events

end EvalDist
