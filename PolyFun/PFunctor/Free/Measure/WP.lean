/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.Expectation
public import PolyFun.PFunctor.Free.Do

/-!
# The expectation readings of free programs

The *expectation reading* interprets a free program over postconditions valued in `ℝ≥0∞`. The
weakest precondition of a postcondition is the fold of the integration spec,
`wp x post = wpFold (OpSpec.lintegral ν) x post`: the expectation of `post`, taken one call at a
time. A triple `⦃ pre ⦄ x ⦃ post ⦄` states the lower bound `pre ≤ wp x post`. The reading is exact,
so its dual reading (`ExactWPMonad.dual`) interprets the same programs over the order duals, and a
triple of the dual reading states an upper bound.

* `PFunctor.FreeM.expectationWPMonad ν` is the expectation reading under answer measures `ν`, the
  interpretation of the expectation algebra `expectationAlgebra ν`, and
  `PFunctor.FreeM.upperExpectationWPMonad ν` is its dual reading. Both are constructions, and both
  are exact.
* `open scoped PFunctor.FreeM.Expectation` installs the expectation reading under the answer
  measures of `PFunctor.AnswerMeasure`, beside the expectation algebra that the scope already
  installs. `open scoped PFunctor.FreeM.UpperExpectation` installs the dual reading. Open one of
  the two at a time: core's assertion types are output parameters, so instance search finds one
  reading of `FreeM P` and never tries the other.

In each scope, `wp_lift` and `wp_liftBind` integrate the postcondition of a call against its answer
measure, and `wp_eq_wpFold` and `triple_iff` state the reading through the fold.

Under `PFunctor.AnswerMeasure`, the expectation reading bounds the integral against the output
measure `evalDist`. The integral of a postcondition is at most its weakest precondition
(`Expectation.lintegral_evalDist_le_wp`), so an upper-bound triple bounds the integral
(`UpperExpectation.lintegral_evalDist_le_of_triple`). Over discrete answers the two are equal for
a measurable postcondition (`Expectation.wp_eq_lintegral_evalDist`), so a lower-bound triple
bounds the integral from below (`Expectation.le_lintegral_evalDist_of_triple`). The expectation
reading is then the interpretation of the expectation algebra of the measure semantics
(`ExpectationWP.toWPMonad_algebra_freeM`).

The carrier `ℝ≥0∞` lies in `Type`, so the readings interpret programs with values in `Type`. The
answers may lie in any universe, but a call `FreeM.lift a` is a program of the readings only when
its answers lie in `Type`. A call over answers in another universe is written
`FreeM.liftBind a fun b => pure (f b)`.

## Rules for `vcgen`

The readings are defined from the integration spec written out as the integral
`fun a k => ∫⁻ b, k b ∂ν a`. `PolyFun.PFunctor.Free.Do`, imported here, registers rules for the
reading of any spec (`Spec.lift_lower`, `Spec.liftBind_lower`) and for its upper-bound reading
(`Spec.lift_upper`, `Spec.liftBind_upper`). Under these readings, the rules therefore state the
precondition of a call as that integral: `∫⁻ b, Q b ∂ν a ⊑ wp (FreeM.lift a) Q`, read in the dual
order for the upper reading. These rules are exact. `vcgen` does not descend under the integral
they produce, so a call followed by more program leaves the condition
`pre ⊑ ∫⁻ b, wp (rest b) post ⊥ ∂ν a`, which the exact `wp` equations finish.

Under probability answer measures, a lower bound at every answer holds in expectation. The
pointwise rules `Spec.lift_expectation_iInf` and `Spec.liftBind_expectation_iInf` state that bound
with core's indexed infimum `Lean.Order.iInf`, which `vcgen` splits into one condition per answer,
so it descends through every call. They lose the averaging over answers, and suit bounds that hold
on every path. `open scoped PFunctor.FreeM.Expectation.Pointwise` registers them.
-/

@[expose] public section

open MeasureTheory Std.WP OrderDual
open scoped ENNReal

universe uA uB

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)]

/-! ## The readings under answer measures -/

section Readings

variable (ν : (a : P.A) → Measure (P.B a))

/-- The expectation reading of free programs under answer measures `ν`: the weakest precondition
of a postcondition is the fold of the integration spec, its expectation taken one call at a time.
Its triples state lower bounds on that expectation. The spec is written out as the integral, so
that `Spec.lift_lower` states the precondition of a call as an integral. -/
@[instance_reducible]
noncomputable def expectationWPMonad : WPMonad (FreeM P) ℝ≥0∞ EStack⟨⟩ :=
  OpSpec.toWPMonad (fun a k => ∫⁻ b, k b ∂ν a) (OpSpec.lintegral_mono ν)

/-- The expectation reading is the interpretation of the expectation algebra, by definition. -/
theorem expectationWPMonad_eq_toWPMonad :
    expectationWPMonad ν = @MAlgOrdered.toWPMonad (FreeM P) ℝ≥0∞ _ _ (expectationAlgebra ν) _ :=
  rfl

/-- The weakest precondition of the expectation reading is the fold of the integration spec. -/
theorem expectationWPMonad_wp {α : Type} (x : FreeM P α) (post : α → ℝ≥0∞) (epost : EStack⟨⟩) :
    ((expectationWPMonad ν).toWP α).wp x post epost = wpFold (OpSpec.lintegral ν) x post :=
  OpSpec.toWPMonad_wp _ _ x post epost

/-- The expectation reading is exact. -/
instance instExactWPMonadExpectationWPMonad :
    @ExactWPMonad (FreeM P) ℝ≥0∞ EStack⟨⟩ _ _ _ (expectationWPMonad ν) :=
  OpSpec.instExactWPMonadToWPMonad _ _

/-- The upper expectation reading of free programs under answer measures `ν`: the dual reading of
the expectation reading (`upperExpectationWPMonad_eq_dual`). Its triple `⦃ toDual t ⦄ x ⦃ post ⦄`
states that the expectation of `ofDual ∘ post` is at most `t`. -/
@[instance_reducible]
noncomputable def upperExpectationWPMonad : WPMonad (FreeM P) ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  OpSpec.toUpperWPMonad (fun a k => ∫⁻ b, k b ∂ν a) (OpSpec.lintegral_mono ν)

/-- The upper expectation reading is the dual reading of the expectation reading, by
definition. -/
theorem upperExpectationWPMonad_eq_dual :
    upperExpectationWPMonad ν =
      @ExactWPMonad.dual (FreeM P) ℝ≥0∞ EStack⟨⟩ _ _ _ (expectationWPMonad ν) _ :=
  rfl

/-- The weakest precondition of the upper expectation reading is the fold of the integration spec,
read in the dual order. -/
theorem upperExpectationWPMonad_wp {α : Type} (x : FreeM P α) (post : α → ℝ≥0∞ᵒᵈ)
    (epost : EStack⟨⟩ᵒᵈ) :
    ((upperExpectationWPMonad ν).toWP α).wp x post epost =
      toDual (wpFold (OpSpec.lintegral ν) x fun a => ofDual (post a)) :=
  OpSpec.toUpperWPMonad_wp _ _ x post epost

/-- The upper expectation reading is exact. -/
instance instExactWPMonadUpperExpectationWPMonad :
    @ExactWPMonad (FreeM P) ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ _ _ _ (upperExpectationWPMonad ν) :=
  OpSpec.instExactWPMonadToUpperWPMonad _ _

/-! ### Pointwise rules -/

/-- Under probability answer measures, a lower bound on the postcondition at every answer of a call
bounds its expectation. Registered in the scope `PFunctor.FreeM.Expectation.Pointwise`. -/
theorem Spec.lift_expectation_iInf {P : PFunctor.{uA, 0}} [∀ a, MeasurableSpace (P.B a)]
    (ν : (a : P.A) → Measure (P.B a)) [∀ a, IsProbabilityMeasure (ν a)] (a : P.A)
    (Q : P.B a → ℝ≥0∞) (E : EStack⟨⟩) :
    @Triple ℝ≥0∞ EStack⟨⟩ (FreeM P (P.B a)) (P.B a) _ _ (FreeM.lift (P := P) a)
      ((expectationWPMonad ν).toWP _) (Lean.Order.iInf Q) Q E := by
  let inst := expectationWPMonad ν
  refine ⟨?_⟩
  rw [expectationWPMonad_wp, wpFold_lift, OpSpec.lintegral_apply, LeanOrder.iInf_eq_iInf]
  calc ⨅ b, Q b = ∫⁻ _, ⨅ b, Q b ∂ν a := by simp
    _ ≤ ∫⁻ b, Q b ∂ν a := lintegral_mono fun b => iInf_le Q b

/-- Under probability answer measures, a lower bound on the weakest preconditions of the
continuations of a node at every answer bounds its expectation. Registered in the scope
`PFunctor.FreeM.Expectation.Pointwise`. -/
theorem Spec.liftBind_expectation_iInf [∀ a, IsProbabilityMeasure (ν a)] {α : Type} (a : P.A)
    (r : P.B a → FreeM P α) (Q : α → ℝ≥0∞) (E : EStack⟨⟩) :
    @Triple ℝ≥0∞ EStack⟨⟩ (FreeM P α) α _ _ (FreeM.liftBind a r) ((expectationWPMonad ν).toWP _)
      (Lean.Order.iInf fun b => ((expectationWPMonad ν).toWP α).wp (r b) Q E) Q E := by
  let inst := expectationWPMonad ν
  refine ⟨?_⟩
  simp only [expectationWPMonad_wp, LeanOrder.iInf_eq_iInf]
  change ⨅ b, wpFold (OpSpec.lintegral ν) (r b) Q ≤
    ∫⁻ b, wpFold (OpSpec.lintegral ν) (r b) Q ∂ν a
  calc ⨅ b, wpFold (OpSpec.lintegral ν) (r b) Q
        = ∫⁻ _, ⨅ b, wpFold (OpSpec.lintegral ν) (r b) Q ∂ν a := by simp
    _ ≤ ∫⁻ b, wpFold (OpSpec.lintegral ν) (r b) Q ∂ν a :=
        lintegral_mono fun b => iInf_le (fun b => wpFold (OpSpec.lintegral ν) (r b) Q) b

end Readings

/-! ## The expectation reading under `PFunctor.AnswerMeasure` -/

namespace Expectation

variable [P.AnswerMeasure]

/-- The expectation reading under the answer measures of `PFunctor.AnswerMeasure`. -/
noncomputable scoped instance instWPMonad : WPMonad (FreeM P) ℝ≥0∞ EStack⟨⟩ :=
  expectationWPMonad AnswerMeasure.toMeasure

/-- The expectation reading under `PFunctor.AnswerMeasure` is exact. -/
scoped instance instExactWPMonad : ExactWPMonad (FreeM P) ℝ≥0∞ EStack⟨⟩ :=
  instExactWPMonadExpectationWPMonad AnswerMeasure.toMeasure

variable {α : Type}

/-- The weakest precondition is the fold of the integration spec of the answer measures. -/
theorem wp_eq_wpFold (x : FreeM P α) (post : α → ℝ≥0∞) (epost : EStack⟨⟩) :
    wp x post epost = wpFold (OpSpec.lintegral AnswerMeasure.toMeasure) x post :=
  expectationWPMonad_wp _ x post epost

/-- A triple is a lower bound on the fold of the integration spec. -/
theorem triple_iff (x : FreeM P α) (pre : ℝ≥0∞) (post : α → ℝ≥0∞) (epost : EStack⟨⟩) :
    Triple x pre post epost ↔ pre ≤ wpFold (OpSpec.lintegral AnswerMeasure.toMeasure) x post := by
  rw [Triple.iff, wp_eq_wpFold]
  rfl

/-- A call integrates the weakest preconditions of its continuations against its answer
measure. -/
theorem wp_liftBind (a : P.A) (r : P.B a → FreeM P α) (post : α → ℝ≥0∞) (epost : EStack⟨⟩) :
    wp (FreeM.liftBind a r) post epost = ∫⁻ b, wp (r b) post epost ∂AnswerMeasure.toMeasure a := by
  simp only [wp_eq_wpFold]
  rfl

/-- A call integrates the postcondition against its answer measure. -/
theorem wp_lift {P : PFunctor.{uA, 0}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
    (a : P.A) (post : P.B a → ℝ≥0∞) (epost : EStack⟨⟩) :
    wp (FreeM.lift a) post epost = ∫⁻ b, post b ∂AnswerMeasure.toMeasure a := by
  rw [wp_eq_wpFold, wpFold_lift, OpSpec.lintegral_apply]

/-- Answer measures are probability measures, so a constant postcondition is its own weakest
precondition. -/
theorem wp_const (x : FreeM P α) (t : ℝ≥0∞) (epost : EStack⟨⟩) : wp x (fun _ => t) epost = t := by
  rw [wp_eq_wpFold]
  exact wpFold_lintegral_const _ x t

/-- A lower bound on the postcondition at every result bounds its weakest precondition. -/
theorem iInf_le_wp (x : FreeM P α) (post : α → ℝ≥0∞) (epost : EStack⟨⟩) :
    ⨅ r, post r ≤ wp x post epost := by
  rw [← wp_const x (⨅ r, post r) epost, wp_eq_wpFold, wp_eq_wpFold]
  exact wpFold_mono (OpSpec.lintegral_mono _) x fun r => iInf_le post r

/-- The integral of a postcondition against the output measure is at most its weakest
precondition, for all answer spaces. -/
theorem lintegral_evalDist_le_wp [MeasurableSpace α] (x : FreeM P α) (post : α → ℝ≥0∞)
    (epost : EStack⟨⟩) : ∫⁻ r, post r ∂evalDist x ≤ wp x post epost := by
  rw [wp_eq_wpFold]
  exact lintegral_measureFold_le_wpFold _ x post

/-- Over discrete answers, the weakest precondition of a measurable postcondition is its integral
against the output measure. -/
theorem wp_eq_lintegral_evalDist [∀ a, DiscreteMeasurableSpace (P.B a)] [MeasurableSpace α]
    (x : FreeM P α) {post : α → ℝ≥0∞} (hpost : Measurable post) (epost : EStack⟨⟩) :
    wp x post epost = ∫⁻ r, post r ∂evalDist x := by
  rw [wp_eq_wpFold]
  exact (lintegral_measureFold_eq_wpFold _ x hpost).symm

/-- Over discrete answers, a triple with a measurable postcondition bounds its integral against
the output measure from below. -/
theorem le_lintegral_evalDist_of_triple [∀ a, DiscreteMeasurableSpace (P.B a)]
    [MeasurableSpace α] {x : FreeM P α} {pre : ℝ≥0∞} {post : α → ℝ≥0∞} {epost : EStack⟨⟩}
    (hpost : Measurable post) (h : Triple x pre post epost) :
    pre ≤ ∫⁻ r, post r ∂evalDist x := by
  rw [← wp_eq_lintegral_evalDist x hpost epost]
  exact h.le_wp

/-! `open scoped PFunctor.FreeM.Expectation.Pointwise` registers the pointwise rules, so `vcgen`
descends through every call, with one condition per answer, at the cost of the averaging over
answers. -/

namespace Pointwise

attribute [scoped spec high] Spec.lift_expectation_iInf Spec.liftBind_expectation_iInf

end Pointwise

end Expectation

/-- Over discrete answers, the interpretation of the expectation algebra of the measure semantics
is the expectation reading under the answer measures of `PFunctor.AnswerMeasure`. -/
theorem _root_.ExpectationWP.toWPMonad_algebra_freeM [P.AnswerMeasure]
    [∀ a, DiscreteMeasurableSpace (P.B a)] :
    @MAlgOrdered.toWPMonad (FreeM P) ℝ≥0∞ _ _ (ExpectationWP.algebra (FreeM P)) _ =
      expectationWPMonad AnswerMeasure.toMeasure := by
  rw [ExpectationWP.algebra_freeM]
  rfl

/-! ## The upper expectation reading under `PFunctor.AnswerMeasure` -/

namespace UpperExpectation

variable [P.AnswerMeasure]

/-- The upper expectation reading under the answer measures of `PFunctor.AnswerMeasure`. -/
noncomputable scoped instance instWPMonad : WPMonad (FreeM P) ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  upperExpectationWPMonad AnswerMeasure.toMeasure

/-- The upper expectation reading under `PFunctor.AnswerMeasure` is exact. -/
scoped instance instExactWPMonad : ExactWPMonad (FreeM P) ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  instExactWPMonadUpperExpectationWPMonad AnswerMeasure.toMeasure

variable {α : Type}

/-- The weakest precondition is the fold of the integration spec of the answer measures, read in
the dual order. -/
theorem wp_eq_wpFold (x : FreeM P α) (post : α → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    wp x post epost =
      toDual (wpFold (OpSpec.lintegral AnswerMeasure.toMeasure) x fun a => ofDual (post a)) :=
  upperExpectationWPMonad_wp _ x post epost

/-- A triple is an upper bound on the fold of the integration spec. -/
theorem triple_iff (x : FreeM P α) (pre : ℝ≥0∞ᵒᵈ) (post : α → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    Triple x pre post epost ↔
      wpFold (OpSpec.lintegral AnswerMeasure.toMeasure) x (fun a => ofDual (post a)) ≤
        ofDual pre := by
  rw [Triple.iff, wp_eq_wpFold]
  rfl

/-- A call integrates the weakest preconditions of its continuations against its answer measure,
in the dual order. -/
theorem wp_liftBind (a : P.A) (r : P.B a → FreeM P α) (post : α → ℝ≥0∞ᵒᵈ)
    (epost : EStack⟨⟩ᵒᵈ) :
    wp (FreeM.liftBind a r) post epost =
      toDual (∫⁻ b, ofDual (wp (r b) post epost) ∂AnswerMeasure.toMeasure a) := by
  simp only [wp_eq_wpFold, ofDual_toDual]
  rfl

/-- A call integrates the postcondition against its answer measure, in the dual order. -/
theorem wp_lift {P : PFunctor.{uA, 0}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
    (a : P.A) (post : P.B a → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    wp (FreeM.lift a) post epost = toDual (∫⁻ b, ofDual (post b) ∂AnswerMeasure.toMeasure a) := by
  rw [wp_eq_wpFold, wpFold_lift, OpSpec.lintegral_apply]

/-- An upper-bound triple bounds the integral of the postcondition against the output measure, for
all answer spaces. -/
theorem lintegral_evalDist_le_of_triple [MeasurableSpace α] {x : FreeM P α} {pre : ℝ≥0∞ᵒᵈ}
    {post : α → ℝ≥0∞ᵒᵈ} {epost : EStack⟨⟩ᵒᵈ} (h : Triple x pre post epost) :
    ∫⁻ r, ofDual (post r) ∂evalDist x ≤ ofDual pre :=
  (lintegral_measureFold_le_wpFold _ x _).trans ((triple_iff x pre post epost).1 h)

end UpperExpectation

end PFunctor.FreeM
