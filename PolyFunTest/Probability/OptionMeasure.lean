/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import ToCslib.MeasureTheory.MeasurableSpace.Instances
import ToCslib.MeasureTheory.Measure.Option
import ToCslib.MeasureTheory.MeasurableSpace.Sum

/-!
# Optional outcomes and discrete words

Regression tests for the staged `Option` and sum measurable spaces, the `dropNone` and
`withFailure` measures, and the discrete instances on `BitVec`.
-/

open MeasureTheory

namespace PolyFunTest.Probability.OptionMeasure

/-- Optional values over a discrete space are discrete, with measurable singletons. -/
example : DiscreteMeasurableSpace (Option ℕ) := inferInstance

example : MeasurableSingletonClass (Option Bool) := inferInstance

example : MeasurableSet ({none} : Set (Option ℕ)) := Option.measurableSet_none

/-- Completing a subprobability measure with its missing mass gives a probability measure. -/
example (μ : Measure Bool) [IsSubprobabilityMeasure μ] : IsProbabilityMeasure μ.withFailure :=
  inferInstance

/-- The failure outcome of a completion carries exactly the missing mass. -/
example (μ : Measure Bool) : μ.withFailure {none} = 1 - μ Set.univ :=
  Measure.withFailure_apply_none μ

/-- Discarding failure after a successful point keeps the point. -/
example : (Measure.dirac (some true)).dropNone = Measure.dirac true := by simp

example : (Measure.dirac (none : Option Bool)).dropNone = 0 := by simp

/-- Completion and discarding `none` are inverse to each other. -/
example (μ : Measure Bool) : μ.withFailure.dropNone = μ := by simp

example (μ : Measure (Option Bool)) [IsProbabilityMeasure μ] : μ.dropNone.withFailure = μ :=
  Measure.withFailure_dropNone μ

/-- A measurable equivalence extends to optional values. -/
example (e : Bool ≃ᵐ Bool) (b : Bool) : e.optionCongr (some b) = some (e b) := by simp

/-- Sums of discrete spaces are discrete, and both injections are measurable embeddings. -/
example : DiscreteMeasurableSpace (ℕ ⊕ Bool) := inferInstance

example : MeasurableSingletonClass (Option (ℕ ⊕ Bool)) := inferInstance

example : MeasurableEmbedding (Sum.inr : Bool → ℕ ⊕ Bool) := measurableEmbedding_inr

/-- Bit vectors carry the discrete σ-algebra, and it propagates to products. -/
example : DiscreteMeasurableSpace (BitVec 8) := inferInstance

example : DiscreteMeasurableSpace (BitVec 4 × BitVec 4) := inferInstance

example (s : Set (BitVec 16)) : MeasurableSet s := MeasurableSet.of_discrete

end PolyFunTest.Probability.OptionMeasure
