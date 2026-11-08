/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Expectation
public import PolyFun.PFunctor.Free.Measure.EvalDist
public import PolyFun.PFunctor.Free.Measure.Lintegral
public import PolyFun.Control.Monad.Algebra.Restrict

/-!
# The expectation algebra of free programs

`PFunctor.FreeM.expectationAlgebra ν` is the ordered monad algebra (`MAlgOrdered`) that the
integration spec `OpSpec.lintegral ν` induces on `FreeM P`: a program with values in `ℝ≥0∞`
collapses to the fold of the integration spec at the identity. Through PolyFun's program-logic
bridges it is an exact weakest-precondition interpretation, in which `wp x post` is the fold
`wpFold (OpSpec.lintegral ν) x post`. Over discrete answers that fold is the integral of `post`
under the measure fold of `x` (`expectationAlgebra_μ_bind_pure`), and the order dual reading
states upper bounds.

The algebra is defined for all answer measures and answer universes. When every answer measure
has total mass at most one, the expectation of the constant `1` is at most `1`, so the algebra
restricts to the probability carrier `Set.Iic (1 : ℝ≥0∞)` (`PFunctor.FreeM.probabilityAlgebra`).

The carrier of an ordered monad algebra lies in the universe of the program's values, so these
algebras apply to programs with values in `Type`. `PFunctor.FreeM.expectationAlgebraULift ν` is the
algebra of the lifted spec `(OpSpec.lintegral ν).ulift` over `ULift ℝ≥0∞`, for programs with values
in any universe.

Under the answer measures of `PFunctor.AnswerMeasure`, over discrete answers, both algebras are the
expectation algebras of the measure semantics of free programs (`ExpectationWP.algebra_freeM`,
`ExpectationWP.algebraULift_freeM`).

All of these algebras are definitions. `open scoped PFunctor.FreeM.Expectation` installs the
expectation algebra of `PFunctor.AnswerMeasure` as an instance.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe uA uB v

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)] (ν : (a : P.A) → Measure (P.B a))

/-! ## Values in `Type` -/

/-- The ordered expectation algebra of free programs under answer measures `ν`: the algebra that
the integration spec induces, which collapses a program with values in `ℝ≥0∞` to the fold of the
integration spec at the identity. -/
@[instance_reducible]
noncomputable def expectationAlgebra : MAlgOrdered (FreeM P) ℝ≥0∞ :=
  (OpSpec.lintegral ν).toMAlgOrdered (OpSpec.lintegral_mono ν)

theorem expectationAlgebra_μ (x : FreeM P ℝ≥0∞) :
    (expectationAlgebra ν).μ x = wpFold (OpSpec.lintegral ν) x id :=
  rfl

/-- Over discrete answers, the expectation algebra collapses a program with values in `ℝ≥0∞` to the
integral of its values under the measure fold. -/
theorem expectationAlgebra_μ_eq_lintegral [∀ a, DiscreteMeasurableSpace (P.B a)]
    (x : FreeM P ℝ≥0∞) : (expectationAlgebra ν).μ x = ∫⁻ r, r ∂measureFold ν x :=
  (lintegral_measureFold_eq_wpFold ν x measurable_id).symm

/-- Over discrete answers, the expectation of a measurable postcondition is its integral under the
measure fold. This is the value of `wp x post` in the weakest-precondition interpretation of the
algebra. -/
theorem expectationAlgebra_μ_bind_pure [∀ a, DiscreteMeasurableSpace (P.B a)] {α : Type}
    [MeasurableSpace α] (x : FreeM P α) {post : α → ℝ≥0∞} (hpost : Measurable post) :
    (expectationAlgebra ν).μ (x >>= fun a => pure (post a)) = ∫⁻ a, post a ∂measureFold ν x := by
  rw [expectationAlgebra, toMAlgOrdered_μ_bind_pure]
  exact (lintegral_measureFold_eq_wpFold ν x hpost).symm

/-- Under subprobability answers, the expectation of the constant `1` is at most `1`. -/
theorem expectationAlgebra_μ_bind_const_le_one [∀ a, IsSubprobabilityMeasure (ν a)] {α : Type}
    (x : FreeM P α) : (expectationAlgebra ν).μ (x >>= fun _ => pure 1) ≤ 1 := by
  rw [expectationAlgebra, toMAlgOrdered_μ_bind_pure]
  exact wpFold_lintegral_const_le ν x 1

/-- The probability algebra of free programs: the expectation algebra under subprobability answer
measures, restricted to the carrier `Set.Iic (1 : ℝ≥0∞)`. -/
@[instance_reducible]
noncomputable def probabilityAlgebra [∀ a, IsSubprobabilityMeasure (ν a)] :
    MAlgOrdered (FreeM P) (Set.Iic (1 : ℝ≥0∞)) :=
  letI := expectationAlgebra ν
  MAlgOrdered.restrictIic 1 fun x => expectationAlgebra_μ_bind_const_le_one ν x

/-! ## Values in every universe -/

/-- The ordered expectation algebra of free programs with values in any universe: the algebra
that the integration spec induces over `ULift ℝ≥0∞`. -/
@[instance_reducible]
noncomputable def expectationAlgebraULift : MAlgOrdered (FreeM.{v} P) (ULift.{v} ℝ≥0∞) :=
  (OpSpec.lintegral ν).ulift.toMAlgOrdered (OpSpec.lintegral_mono ν).ulift

theorem expectationAlgebraULift_μ (x : FreeM.{v} P (ULift.{v} ℝ≥0∞)) :
    (expectationAlgebraULift ν).μ x = ⟨wpFold (OpSpec.lintegral ν) x ULift.down⟩ :=
  wpFold_ulift _ x id

/-- The lifted expectation algebra sends a program with a mapped output to the lifted fold of the
integration spec. -/
theorem expectationAlgebraULift_μ_bind_pure {α : Type v} (x : FreeM P α) (post : α → ℝ≥0∞) :
    (expectationAlgebraULift ν).μ (x >>= fun a => pure ⟨post a⟩) =
      ⟨wpFold (OpSpec.lintegral ν) x post⟩ := by
  rw [expectationAlgebraULift, toMAlgOrdered_μ_bind_pure, wpFold_ulift]

/-- Over discrete answers, the lifted expectation of a measurable postcondition is its integral
under the measure fold. -/
theorem expectationAlgebraULift_μ_bind_pure_eq_lintegral [∀ a, DiscreteMeasurableSpace (P.B a)]
    {α : Type v} [MeasurableSpace α] (x : FreeM P α) {post : α → ℝ≥0∞} (hpost : Measurable post) :
    (expectationAlgebraULift ν).μ (x >>= fun a => pure ⟨post a⟩) =
      ⟨∫⁻ a, post a ∂measureFold ν x⟩ := by
  rw [expectationAlgebraULift_μ_bind_pure, lintegral_measureFold_eq_wpFold ν x hpost]

/-! ## Agreement with the measure semantics -/

section AnswerMeasure

variable [P.AnswerMeasure] [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- Over discrete answers, the expectation algebra of the measure semantics of free programs is the
algebra of the integration spec of their answer measures. -/
theorem _root_.ExpectationWP.algebra_freeM :
    ExpectationWP.algebra (FreeM P) = expectationAlgebra AnswerMeasure.toMeasure := by
  have h : ∀ x : FreeM P ℝ≥0∞,
      (ExpectationWP.algebra (FreeM P)).μ x = (expectationAlgebra AnswerMeasure.toMeasure).μ x :=
    fun x => (expectationAlgebra_μ_eq_lintegral _ x).symm
  unfold ExpectationWP.algebra expectationAlgebra OpSpec.toMAlgOrdered at *
  congr 1
  exact funext h

/-- Over discrete answers, the lifted expectation algebra of the measure semantics of free programs
is the algebra of the lifted integration spec of their answer measures. -/
theorem _root_.ExpectationWP.algebraULift_freeM :
    ExpectationWP.algebraULift (FreeM.{v} P) = expectationAlgebraULift AnswerMeasure.toMeasure := by
  have h : ∀ x : FreeM.{v} P (ULift.{v} ℝ≥0∞),
      (ExpectationWP.algebraULift (FreeM.{v} P)).μ x =
        (expectationAlgebraULift AnswerMeasure.toMeasure).μ x := fun x => by
    rw [expectationAlgebraULift_μ, ExpectationWP.algebraULift_μ]
    exact congrArg ULift.up (lintegral_measureFold_eq_wpFold _ x measurable_down)
  unfold ExpectationWP.algebraULift expectationAlgebraULift OpSpec.toMAlgOrdered at *
  congr 1
  exact funext h

end AnswerMeasure

namespace Expectation

/-- The expectation algebra of the answer measures in `PFunctor.AnswerMeasure`. -/
noncomputable scoped instance instMAlgOrdered [P.AnswerMeasure] : MAlgOrdered (FreeM P) ℝ≥0∞ :=
  expectationAlgebra AnswerMeasure.toMeasure

end Expectation

end PFunctor.FreeM
