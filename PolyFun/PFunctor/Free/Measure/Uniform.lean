/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Uniform
public import PolyFun.PFunctor.Free.Measure.EvalDist

/-!
# Uniform answers to free programs

A call to an operation whose answer measure is uniform is a uniform draw from the answer type
(`PFunctor.FreeM.isUniform_lift`). The uniform answer measures of
`PFunctor.AnswerMeasure.uniformOfFiniteNonempty` satisfy the hypothesis by `rfl`. Over discrete
answers the measure semantics of free programs is lawful, so the laws of `EvalDist.IsUniformOn`
apply to programs built from such calls. A call post-processed by a bijection is a uniform draw
that never fails, independent calls combine into a uniform draw from the product, and their events
have counting probabilities.

A uniform answer measure is a probability measure only on a finite answer type, so the
hypothesis also gives finiteness (`PFunctor.AnswerMeasure.finite_of_toMeasure_eq_uniformOn`).
Every answer type of an answer measure is nonempty (`PFunctor.AnswerMeasure.nonempty`).
-/

public section

open MeasureTheory ProbabilityTheory Set

universe uA u

namespace PFunctor

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]

namespace AnswerMeasure

/-- Every answer type carries a probability measure, so it is nonempty. Not an instance: its
conclusion would be a candidate for every `Nonempty` goal. -/
theorem nonempty (a : P.A) : Nonempty (P.B a) :=
  (toMeasure a).nonempty_of_neZero

/-- An answer type whose answer measure is uniform is finite, because the uniform measure on an
infinite type is zero. Not an instance, for the reason given at `nonempty`. -/
theorem finite_of_toMeasure_eq_uniformOn {a : P.A}
    (h : toMeasure a = uniformOn Set.univ) : Finite (P.B a) := by
  have hne : uniformOn (Set.univ : Set (P.B a)) Set.univ ≠ 0 := by
    rw [← h, measure_univ]
    exact one_ne_zero
  exact Set.finite_univ_iff.mp (finite_of_uniformOn_ne_zero hne)

end AnswerMeasure

namespace FreeM

/-- A call whose answer measure is uniform is a uniform draw from its answer type. The answer type
needs measurable singletons. -/
theorem isUniform_lift (a : P.A) [MeasurableSingletonClass (P.B a)]
    (h : AnswerMeasure.toMeasure a = uniformOn Set.univ) :
    EvalDist.IsUniform (FreeM.lift a : FreeM P (P.B a)) :=
  have := AnswerMeasure.finite_of_toMeasure_eq_uniformOn h
  EvalDist.IsUniformOn.of_evalDist_eq (by rw [evalDist_lift, h])

end FreeM

end PFunctor
