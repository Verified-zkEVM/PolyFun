/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Measure.Measurable
public import ToCslib.MeasureTheory.Measure.Option

/-!
# Values and failure of a measure on partial results

A measure `ν` on `DomainResult ε α` splits into the mass of its values and the mass of bottom and
the errors.

- `DomainResult.success ν` is the measure on `α` that keeps only the values. It is the pullback of
  `ν` along `value`, and it is a subprobability measure when `ν` is one.
- `DomainResult.failureMass ν` is the mass of bottom plus the errors.

The two parts add up to the total mass (`success_apply_univ_add_failureMass`). For a
subprobability measure, the defect of `success ν` is the defect of `ν` plus `failureMass ν`
(`defect_success`). For a probability measure, the defect of `success ν` is therefore exactly
`failureMass ν` (`defect_success_eq_failureMass`). Pushing `ν` forward along `toOption` and
discarding `none` gives `success ν` (`dropNone_map_toOption`), and for a probability measure that
pushforward is the failure completion of `success ν` (`map_toOption_eq_withFailure`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DomainResult

variable {ε α : Type*} [MeasurableSpace α]

/-- The values of a measure on results: the mass at `value x` becomes mass at `x`, and bottom and
the errors are discarded. -/
noncomputable def success (ν : Measure (DomainResult ε α)) : Measure α :=
  ν.comap value

/-- The mass of bottom plus the errors. -/
noncomputable def failureMass (ν : Measure (DomainResult ε α)) : ℝ≥0∞ :=
  ν (Set.range value)ᶜ

variable (ν : Measure (DomainResult ε α))

theorem success_apply (s : Set α) : success ν s = ν (value '' s) :=
  measurableEmbedding_value.comap_apply ν s

theorem success_apply_univ : success ν Set.univ = ν (Set.range value) := by
  rw [success_apply, Set.image_univ]

/-- The failure mass is the mass of bottom plus the mass of the errors. -/
theorem failureMass_eq_measure_bot_add_measure_range_error :
    failureMass ν = ν {⊥} + ν (Set.range error) := by
  have hne : ∀ (e : ε) (x : α), (error e : DomainResult ε α) ≠ value x :=
    fun e x h => value_ne_error x e h.symm
  have hsplit : (Set.range (value : α → DomainResult ε α))ᶜ = {⊥} ∪ Set.range error := by
    ext d
    induction d using inductionOn <;> simp [hne]
  have hdisjoint : Disjoint ({⊥} : Set (DomainResult ε α)) (Set.range error) :=
    Set.disjoint_singleton_left.2 fun ⟨e, he⟩ => error_ne_bot e he
  rw [failureMass, hsplit, measure_union hdisjoint measurableSet_range_error]

/-- The values and the failures together carry the total mass. -/
theorem success_apply_univ_add_failureMass : success ν Set.univ + failureMass ν = ν Set.univ := by
  rw [success_apply_univ, failureMass, measure_add_measure_compl measurableSet_range_value]

theorem success_apply_univ_le : success ν Set.univ ≤ ν Set.univ :=
  (success_apply_univ_add_failureMass ν).le.trans' le_self_add

theorem failureMass_le_measure_univ : failureMass ν ≤ ν Set.univ :=
  (success_apply_univ_add_failureMass ν).le.trans' le_add_self

instance isSubprobabilityMeasure_success [IsSubprobabilityMeasure ν] :
    IsSubprobabilityMeasure (success ν) :=
  ⟨(success_apply_univ_le ν).trans (measure_univ_le ν)⟩

theorem failureMass_le_one [IsSubprobabilityMeasure ν] : failureMass ν ≤ 1 :=
  (failureMass_le_measure_univ ν).trans (measure_univ_le ν)

/-- The mass that `success ν` is missing is the mass `ν` is missing plus the failure mass. -/
theorem defect_success [IsSubprobabilityMeasure ν] :
    (success ν).defect = ν.defect + failureMass ν := by
  have htotal : success ν Set.univ + failureMass ν ≤ 1 :=
    (success_apply_univ_add_failureMass ν).trans_le (measure_univ_le ν)
  have hcancel : AddLECancellable (success ν Set.univ) := ENNReal.cancel_of_ne (measure_ne_top _ _)
  rw [Measure.defect, Measure.defect, ← success_apply_univ_add_failureMass ν, ← tsub_tsub,
    tsub_add_cancel_of_le (hcancel.le_tsub_of_add_le_left htotal)]

/-- For a probability measure, the mass that `success ν` is missing is the failure mass. -/
theorem defect_success_eq_failureMass [IsProbabilityMeasure ν] :
    (success ν).defect = failureMass ν := by
  rw [defect_success, Measure.defect, measure_univ, tsub_self, zero_add]

/-! ## Point masses and linearity -/

@[simp]
theorem success_map_value (μ : Measure α) :
    success (μ.map value : Measure (DomainResult ε α)) = μ :=
  measurableEmbedding_value.comap_map μ

@[simp]
theorem failureMass_map_value (μ : Measure α) :
    failureMass (μ.map value : Measure (DomainResult ε α)) = 0 := by
  rw [failureMass, Measure.map_apply measurable_value measurableSet_range_value.compl]
  simp

@[simp]
theorem success_dirac_value (x : α) :
    success (Measure.dirac (value x : DomainResult ε α)) = Measure.dirac x := by
  rw [← Measure.map_dirac' measurable_value, success_map_value]

@[simp]
theorem failureMass_dirac_value (x : α) :
    failureMass (Measure.dirac (value x : DomainResult ε α)) = 0 := by
  rw [← Measure.map_dirac' measurable_value, failureMass_map_value]

@[simp]
theorem success_dirac_bot : success (Measure.dirac (⊥ : DomainResult ε α)) = 0 := by
  ext s hs
  rw [success_apply, Measure.dirac_apply' _ (measurableSet_value_image.2 hs)]
  simp

@[simp]
theorem failureMass_dirac_bot : failureMass (Measure.dirac (⊥ : DomainResult ε α)) = 1 := by
  rw [failureMass, Measure.dirac_apply' _ measurableSet_range_value.compl]
  simp

@[simp]
theorem success_dirac_error (e : ε) :
    success (Measure.dirac (error e : DomainResult ε α)) = 0 := by
  ext s hs
  rw [success_apply, Measure.dirac_apply' _ (measurableSet_value_image.2 hs)]
  simp

@[simp]
theorem failureMass_dirac_error (e : ε) :
    failureMass (Measure.dirac (error e : DomainResult ε α)) = 1 := by
  rw [failureMass, Measure.dirac_apply' _ measurableSet_range_value.compl]
  simp

@[simp]
theorem success_zero : success (0 : Measure (DomainResult ε α)) = 0 :=
  Measure.comap_zero _

@[simp]
theorem failureMass_zero : failureMass (0 : Measure (DomainResult ε α)) = 0 := rfl

@[simp]
theorem success_add (ν' : Measure (DomainResult ε α)) :
    success (ν + ν') = success ν + success ν' :=
  measurableEmbedding_value.comap_add ν ν'

@[simp]
theorem failureMass_add (ν' : Measure (DomainResult ε α)) :
    failureMass (ν + ν') = failureMass ν + failureMass ν' :=
  rfl

@[simp]
theorem success_smul (c : ℝ≥0∞) : success (c • ν) = c • success ν :=
  Measure.comap_smul c

@[simp]
theorem failureMass_smul (c : ℝ≥0∞) : failureMass (c • ν) = c * failureMass ν := rfl

/-! ## Optional values -/

/-- Pushing a measure on results to optional values and discarding `none` keeps the values. -/
@[simp]
theorem dropNone_map_toOption : (ν.map toOption).dropNone = success ν := by
  ext s hs
  rw [Measure.dropNone_apply _ hs,
    Measure.map_apply measurable_toOption (Option.measurableSet_some_image.2 hs),
    toOption_preimage_some_image, success_apply]

/-- The `none` outcome of the optional pushforward carries the failure mass. -/
theorem map_toOption_apply_none : ν.map toOption {none} = failureMass ν := by
  rw [Measure.map_apply measurable_toOption Option.measurableSet_none, toOption_preimage_none,
    failureMass]

/-- The optional pushforward of a probability measure on results is the failure completion of its
values. -/
theorem map_toOption_eq_withFailure [IsProbabilityMeasure ν] :
    ν.map toOption = (success ν).withFailure := by
  rw [← dropNone_map_toOption, Measure.withFailure_dropNone]

end DomainResult
