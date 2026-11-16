/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Measure

/-!
# Measurable partial results

Regression tests for the measurable structure on `DomainResult ε α`. Its instances agree with the
coproduct structure of `Option (DiscreteOrder ε ⊕ α)` by unfolding instances alone, and errors need
no σ-algebra on `ε`. A three-atom measure splits into its values and its failure mass.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace PolyFunTest.Probability.DomainMeasurable

/-! ## Instances -/

/-- `String` has no measurable space, yet results with string errors do. -/
example : MeasurableSpace (DomainResult String ℕ) := inferInstance

example : MeasurableSingletonClass (DomainResult String ℕ) := inferInstance

example : DiscreteMeasurableSpace (DomainResult String ℕ) := inferInstance

example : (inferInstance : MeasurableSpace (DiscreteOrder String)) = ⊤ := rfl

/-- The instance is the coproduct structure of `Option` over the sum, up to instance unfolding. -/
example {ε α : Type} [MeasurableSpace α] :
    (inferInstance : MeasurableSpace (DomainResult ε α)) =
      (inferInstance : MeasurableSpace (Option (DiscreteOrder ε ⊕ α))) := by
  with_reducible_and_instances rfl

/-- The equivalence with optional sums is the identity function. -/
example (x : DomainResult String ℕ) : DomainResult.measurableEquiv x = x := rfl

example (x : Option (DiscreteOrder String ⊕ ℕ)) : DomainResult.measurableEquiv.symm x = x := rfl

/-- The structure induced by either equivalence is the instance. -/
example {ε α : Type} [MeasurableSpace α] :
    MeasurableSpace.comap DomainResult.measurableEquiv
        (inferInstance : MeasurableSpace (Option (DiscreteOrder ε ⊕ α))) =
      (inferInstance : MeasurableSpace (DomainResult ε α)) :=
  DomainResult.measurableEquiv.measurableEmbedding.comap_eq

example {α : Type} [MeasurableSpace α] :
    MeasurableSpace.comap DomainResult.measurableEquivSum
        (inferInstance : MeasurableSpace (Option (ℕ ⊕ α))) =
      (inferInstance : MeasurableSpace (DomainResult ℕ α)) :=
  DomainResult.measurableEquivSum.measurableEmbedding.comap_eq

-- There is no measurable structure on `WithBot` in general.
/--
error: failed to synthesize
  MeasurableSpace (WithBot ℕ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth MeasurableSpace (WithBot ℕ)

/-! ## Measurable sets and functions -/

example : MeasurableSet ({⊥} : Set (DomainResult String ℕ)) := DomainResult.measurableSet_bot

example (e : String) : MeasurableSet ({DomainResult.error e} : Set (DomainResult String ℕ)) :=
  DomainResult.measurableSet_singleton_error e

example : Measurable (DomainResult.toOption : DomainResult String ℕ → Option ℕ) := by fun_prop

example : Measurable (DomainResult.value : ℕ → DomainResult String ℕ) := by fun_prop

/-! ## Values and failure -/

/-- Half the mass returns `3`, a quarter reports an error, and a quarter diverges. -/
noncomputable def threeAtoms : Measure (DomainResult String ℕ) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac (DomainResult.value 3) +
    (4⁻¹ : ℝ≥0∞) • Measure.dirac (DomainResult.error "timeout") +
    (4⁻¹ : ℝ≥0∞) • Measure.dirac ⊥

example : DomainResult.success threeAtoms = (2⁻¹ : ℝ≥0∞) • Measure.dirac 3 := by
  simp [threeAtoms]

example : DomainResult.failureMass threeAtoms = 4⁻¹ + 4⁻¹ := by
  simp [threeAtoms]

/-- Discarding `none` from the optional pushforward keeps the values. -/
example (ν : Measure (DomainResult String ℕ)) :
    (ν.map DomainResult.toOption).dropNone = DomainResult.success ν :=
  DomainResult.dropNone_map_toOption ν

/-- For a probability measure, the values miss exactly the failure mass. -/
example (ν : Measure (DomainResult String ℕ)) [IsProbabilityMeasure ν] :
    (DomainResult.success ν).defect = DomainResult.failureMass ν :=
  DomainResult.defect_success_eq_failureMass ν

end PolyFunTest.Probability.DomainMeasurable
