/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure
public import PolyFun.Control.Monad.Algebra.Restrict
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# The expectation algebra of free programs

A free program whose results are values in `ℝ≥0∞` can be collapsed to the integral of those
values under its measure fold. `PFunctor.FreeM.expectationAlgebra ν` is that collapse, an
ordered monad algebra (`MAlgOrdered`) on `FreeM P`, for answer measures `ν` over discrete answer
types. Through PolyFun's program-logic bridges it is an exact weakest-precondition
interpretation: `wp x post` is the expected value of `post` under the measure fold of `x`
(`expectationAlgebra_μ_bind_pure`), and the order dual reading states upper bounds.

When every answer measure has total mass at most one, the expectation of the constant `1` is at
most `1`, so the algebra restricts to the probability carrier `Set.Iic (1 : ℝ≥0∞)`
(`PFunctor.FreeM.probabilityAlgebra`).

Both algebras are definitions. `open scoped PFunctor.FreeM.Expectation` installs the expectation
algebra of `PFunctor.AnswerMeasure` as an instance.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe uA

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, 0}} [∀ a, MeasurableSpace (P.B a)]
  [∀ a, DiscreteMeasurableSpace (P.B a)] (ν : (a : P.A) → Measure (P.B a))

/-- The ordered expectation algebra of free programs under answer measures `ν`: a program with
values in `ℝ≥0∞` collapses to the integral of its values under the measure fold. -/
@[instance_reducible]
noncomputable def expectationAlgebra : MAlgOrdered (FreeM P) ℝ≥0∞ where
  μ x := ∫⁻ r, r ∂measureFold ν x
  μ_pure x := by
    change ∫⁻ r, r ∂Measure.dirac x = x
    exact lintegral_dirac x id
  μ_bind_mono {α} f g hfg x := by
    let obs : α → Measure ℝ≥0∞ × Measure ℝ≥0∞ := fun a => (measureFold ν (f a), measureFold ν (g a))
    let _ : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
    have hobs : Measurable obs := comap_measurable obs
    have hf : Measurable fun a => measureFold ν (f a) := measurable_fst.comp hobs
    have hg : Measurable fun a => measureFold ν (g a) := measurable_snd.comp hobs
    change ∫⁻ r, r ∂measureFold ν (FreeM.bind x f) ≤ ∫⁻ r, r ∂measureFold ν (FreeM.bind x g)
    rw [measureFold_bind ν x f hf, measureFold_bind ν x g hg,
      Measure.lintegral_bind (f := fun r => r) hf.aemeasurable aemeasurable_id',
      Measure.lintegral_bind (f := fun r => r) hg.aemeasurable aemeasurable_id']
    exact lintegral_mono hfg

theorem expectationAlgebra_μ (x : FreeM P ℝ≥0∞) :
    (expectationAlgebra ν).μ x = ∫⁻ r, r ∂measureFold ν x :=
  rfl

/-- The expectation of a measurable postcondition is its integral under the measure fold. This
is the value of `wp x post` in the weakest-precondition interpretation of the algebra. -/
theorem expectationAlgebra_μ_bind_pure {α : Type} [MeasurableSpace α] (x : FreeM P α)
    {post : α → ℝ≥0∞} (hpost : Measurable post) :
    (expectationAlgebra ν).μ (x >>= fun a => pure (post a)) = ∫⁻ a, post a ∂measureFold ν x := by
  change ∫⁻ r, r ∂measureFold ν (FreeM.bind x fun a => pure (post a)) = _
  have hk : Measurable fun a => measureFold ν (pure (post a) : FreeM P ℝ≥0∞) :=
    Measure.measurable_dirac.comp hpost
  rw [measureFold_bind ν x _ hk,
    Measure.lintegral_bind (f := fun r => r) hk.aemeasurable aemeasurable_id']
  simp only [measureFold_pure, lintegral_dirac]

/-- Under subprobability answer measures, the expectation of the constant `1` is at most `1`. -/
theorem expectationAlgebra_μ_bind_const_le_one [∀ a, IsSubprobabilityMeasure (ν a)] {α : Type}
    (x : FreeM P α) : (expectationAlgebra ν).μ (x >>= fun _ => pure 1) ≤ 1 := by
  let _ : MeasurableSpace α := ⊤
  rw [expectationAlgebra_μ_bind_pure ν x measurable_const, lintegral_const, one_mul]
  exact measure_univ_le (measureFold ν x)

/-- The probability algebra of free programs: the expectation algebra under subprobability answer
measures, restricted to the carrier `Set.Iic (1 : ℝ≥0∞)`. -/
@[instance_reducible]
noncomputable def probabilityAlgebra [∀ a, IsSubprobabilityMeasure (ν a)] :
    MAlgOrdered (FreeM P) (Set.Iic (1 : ℝ≥0∞)) :=
  letI := expectationAlgebra ν
  MAlgOrdered.restrictIic 1 fun x => expectationAlgebra_μ_bind_const_le_one ν x

namespace Expectation

/-- The expectation algebra of the answer measures in `PFunctor.AnswerMeasure`. -/
noncomputable scoped instance instMAlgOrdered [P.AnswerMeasure] : MAlgOrdered (FreeM P) ℝ≥0∞ :=
  expectationAlgebra AnswerMeasure.toMeasure

end Expectation

end PFunctor.FreeM
