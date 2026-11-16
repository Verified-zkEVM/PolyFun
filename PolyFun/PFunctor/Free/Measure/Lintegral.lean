/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.WP
public import PolyFun.PFunctor.Free.Measure

/-!
# Expectations of free programs through the fold

`PFunctor.OpSpec.lintegral ν` specifies a call at `a` by the integral of its continuation under
the answer measure `ν a`. Its fold, `wpFold (OpSpec.lintegral ν) x post`, is the expectation of
`post` over the results of `x`, taken one call at a time. The fold places no measurable space on
the results and no measurability condition on `post`, and the results may lie in any universe.

The fold agrees with integration against the measure fold `measureFold ν x`:

* `PFunctor.FreeM.lintegral_measureFold_le_wpFold`: the integral of any postcondition is at most
  its fold, for all answer measures.
* `PFunctor.FreeM.lintegral_measureFold_eq_wpFold`: over discrete answers, the integral of a
  measurable postcondition equals its fold.

The gap in general has two sources. `measureFold` sends a call whose continuation family is not
almost everywhere measurable to the zero measure, and the integral of a postcondition that is not
measurable is the supremum over its measurable minorants. The fold integrates each continuation
directly, so neither loses mass there. Discrete answers make every continuation family
measurable, and a measurable postcondition satisfies the tower law of `Measure.bind`.

Event probabilities are folds of indicators (`measureFold_apply_eq_wpFold`). Substitution is
pullback for the integration spec as for any spec: over discrete answers, pulling the
integration spec back along a free handler integrates against the measure folds of the
implementations (`OpSpec.lintegral_pullback`).

Under subprobability answers a constant postcondition folds to at most itself
(`wpFold_lintegral_const_le`); under probability answers it folds to itself, and a constant added
to a postcondition passes through the fold (`wpFold_lintegral_const_add`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe uA uB uA₂ uB₂ v

namespace PFunctor

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)]

/-! ## The integration spec -/

/-- The integration spec of answer measures `ν`: a call at `a` is specified by the integral of its
continuation under `ν a`. -/
noncomputable def OpSpec.lintegral (ν : (a : P.A) → Measure (P.B a)) : OpSpec P ℝ≥0∞ :=
  fun a k => ∫⁻ b, k b ∂ν a

@[simp]
theorem OpSpec.lintegral_apply (ν : (a : P.A) → Measure (P.B a)) (a : P.A) (k : P.B a → ℝ≥0∞) :
    OpSpec.lintegral ν a k = ∫⁻ b, k b ∂ν a :=
  rfl

/-- The integration spec is monotone in the continuation. -/
theorem OpSpec.lintegral_mono (ν : (a : P.A) → Measure (P.B a)) : (OpSpec.lintegral ν).Monotone :=
  fun _ _ _ hk => MeasureTheory.lintegral_mono hk

namespace FreeM

variable (ν : (a : P.A) → Measure (P.B a)) {α : Type v}

/-! ## Integration against the measure fold -/

/-- The integral of a measurable postcondition is at most its fold. This is the inductive core of
`lintegral_measureFold_le_wpFold`. -/
private theorem lintegral_measureFold_le_wpFold_of_measurable [MeasurableSpace α]
    (x : FreeM P α) {post : α → ℝ≥0∞} (hpost : Measurable post) :
    ∫⁻ r, post r ∂measureFold ν x ≤ wpFold (OpSpec.lintegral ν) x post := by
  induction x with
  | pure x => exact (lintegral_dirac' x hpost).le
  | lift_bind a cont ih =>
      change ∫⁻ r, post r ∂measureFold ν (FreeM.liftBind a cont) ≤
        ∫⁻ b, wpFold (OpSpec.lintegral ν) (cont b) post ∂ν a
      by_cases h : AEMeasurable (fun b => measureFold ν (cont b)) (ν a)
      · rw [measureFold_liftBind ν a cont h, Measure.lintegral_bind h hpost.aemeasurable]
        exact lintegral_mono ih
      · rw [measureFold_liftBind_of_not_aemeasurable ν a cont h, lintegral_zero_measure]
        exact zero_le

/-- **The fold bounds the integral.** For all answer measures `ν`, the integral of a
postcondition against the measure fold is at most the fold of the integration spec.

No hypothesis is needed. The measure fold sends a call to zero when its continuation family is
not almost everywhere measurable. The integral of a postcondition that is not measurable is the
supremum of the integrals of its measurable minorants. Both only lower the left side.
`lintegral_measureFold_eq_wpFold` gives equality over discrete answers. -/
theorem lintegral_measureFold_le_wpFold [MeasurableSpace α] (x : FreeM P α) (post : α → ℝ≥0∞) :
    ∫⁻ r, post r ∂measureFold ν x ≤ wpFold (OpSpec.lintegral ν) x post := by
  obtain ⟨g, hg, hgpost, heq⟩ := exists_measurable_le_lintegral_eq (measureFold ν x) post
  rw [heq]
  exact (lintegral_measureFold_le_wpFold_of_measurable ν x hg).trans
    (wpFold_mono (OpSpec.lintegral_mono ν) x hgpost)

/-- **The fold is the integral.** Over discrete answers, the integral of a measurable
postcondition against the measure fold is the fold of the integration spec.

Discrete answers make the continuation family of every call measurable, so the measure fold
composes by `Measure.bind` at every call. Countable answer types with measurable singletons are
discrete (`MeasurableSingletonClass.toDiscreteMeasurableSpace`). Measurability of `post` gives the
Dirac evaluation at a leaf and the tower law of `Measure.bind` at a call. -/
theorem lintegral_measureFold_eq_wpFold [∀ a, DiscreteMeasurableSpace (P.B a)] [MeasurableSpace α]
    (x : FreeM P α) {post : α → ℝ≥0∞} (hpost : Measurable post) :
    ∫⁻ r, post r ∂measureFold ν x = wpFold (OpSpec.lintegral ν) x post := by
  induction x with
  | pure x => exact lintegral_dirac' x hpost
  | lift_bind a cont ih =>
      change ∫⁻ r, post r ∂measureFold ν (FreeM.liftBind a cont) =
        ∫⁻ b, wpFold (OpSpec.lintegral ν) (cont b) post ∂ν a
      rw [measureFold_liftBind ν a cont Measurable.of_discrete.aemeasurable,
        Measure.lintegral_bind Measurable.of_discrete.aemeasurable hpost.aemeasurable]
      exact lintegral_congr ih

/-- Over discrete answers, the measure-fold mass of a measurable event is the fold of its
indicator. -/
theorem measureFold_apply_eq_wpFold [∀ a, DiscreteMeasurableSpace (P.B a)] [MeasurableSpace α]
    (x : FreeM P α) {s : Set α} (hs : MeasurableSet s) :
    measureFold ν x s = wpFold (OpSpec.lintegral ν) x (s.indicator 1) := by
  rw [← lintegral_indicator_one hs]
  exact lintegral_measureFold_eq_wpFold ν x (measurable_one.indicator hs)

/-! ## Total mass -/

/-- Under subprobability answers, a constant postcondition folds to at most itself. -/
theorem wpFold_lintegral_const_le [∀ a, IsSubprobabilityMeasure (ν a)] (x : FreeM P α)
    (t : ℝ≥0∞) : wpFold (OpSpec.lintegral ν) x (fun _ => t) ≤ t := by
  induction x with
  | pure _ => exact le_rfl
  | lift_bind a cont ih =>
      change ∫⁻ b, wpFold (OpSpec.lintegral ν) (cont b) (fun _ => t) ∂ν a ≤ t
      calc ∫⁻ b, wpFold (OpSpec.lintegral ν) (cont b) (fun _ => t) ∂ν a ≤ ∫⁻ _, t ∂ν a :=
            lintegral_mono ih
        _ = t * ν a Set.univ := lintegral_const t
        _ ≤ t := mul_le_of_le_one_right' (measure_univ_le (ν a))

/-- Under probability answers, a constant added to a postcondition passes through the fold. -/
theorem wpFold_lintegral_const_add [∀ a, IsProbabilityMeasure (ν a)] (x : FreeM P α) (t : ℝ≥0∞)
    (post : α → ℝ≥0∞) :
    wpFold (OpSpec.lintegral ν) x (fun r => t + post r) =
      t + wpFold (OpSpec.lintegral ν) x post := by
  induction x with
  | pure _ => rfl
  | lift_bind a cont ih =>
      change ∫⁻ b, wpFold (OpSpec.lintegral ν) (cont b) (fun r => t + post r) ∂ν a =
        t + ∫⁻ b, wpFold (OpSpec.lintegral ν) (cont b) post ∂ν a
      simp only [ih]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- Under probability answers, a constant postcondition folds to itself. -/
theorem wpFold_lintegral_const [∀ a, IsProbabilityMeasure (ν a)] (x : FreeM P α) (t : ℝ≥0∞) :
    wpFold (OpSpec.lintegral ν) x (fun _ => t) = t := by
  induction x with
  | pure _ => rfl
  | lift_bind a cont ih =>
      change ∫⁻ b, wpFold (OpSpec.lintegral ν) (cont b) (fun _ => t) ∂ν a = t
      simp only [ih, lintegral_const, measure_univ, mul_one]

end FreeM

/-! ## Substitution -/

/-- **Substitution is pullback.** Over discrete answers, the integration spec pulled back along a
free handler is the integration spec of the measures its implementations fold to. Folding the
integration spec over a simulated program therefore integrates against those measures
(`FreeM.wpFold_liftM`). -/
theorem OpSpec.lintegral_pullback [∀ a, DiscreteMeasurableSpace (P.B a)]
    {Q : PFunctor.{uA₂, uB₂}} [∀ b, MeasurableSpace (Q.B b)] [∀ b, DiscreteMeasurableSpace (Q.B b)]
    (ν : (b : Q.A) → Measure (Q.B b)) (handler : (a : P.A) → FreeM Q (P.B a)) :
    (OpSpec.lintegral ν).pullback handler =
      OpSpec.lintegral fun a => FreeM.measureFold ν (handler a) := by
  funext a k
  exact (FreeM.lintegral_measureFold_eq_wpFold ν (handler a) Measurable.of_discrete).symm

end PFunctor
