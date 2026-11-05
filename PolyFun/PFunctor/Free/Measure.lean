/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Basic
public import PolyFun.PFunctor.Measure
public import ToCslib.MeasureTheory.Measure.Subprobability

/-!
# Measure semantics for polynomial free programs

This module interprets a polynomial free program directly as a Mathlib `Measure`. Each operation
is assigned a probability measure on its answer type (`PFunctor.AnswerMeasure`), and
`PFunctor.FreeM.denote` composes those measures with `Measure.bind` when the continuation is
almost everywhere measurable. An unmeasurable continuation denotes zero. This convention makes
the fold subprobabilistic without depending on Mathlib's arbitrary default for an unmeasurable
pushforward.

`Measure α` is a type only after `α` receives a `MeasurableSpace`, so this interpretation is an
explicit fold rather than a Lean monad morphism. The measurable-continuation boundary stays
visible in the general laws. Discrete answer types discharge the internal measurability
obligations while leaving the result space arbitrary.

## Main definitions

* `PFunctor.FreeM.measureFold μ` folds a free program under arbitrary per-operation measures
  `μ : (a : P.A) → Measure (P.B a)`: probability measures, subprobability measures for failing
  operations, or any other weighting.
* `PFunctor.FreeM.denote` is the measure fold under the answer measures of `PFunctor.AnswerMeasure`.

## Main statements

* `PFunctor.FreeM.measureFold_liftM`: substitution is pullback. Folding a program simulated by a
  free handler is folding the source program under the measures its implementations denote.
* `PFunctor.FreeM.denote_lift` identifies the denotation of one operation.
* `PFunctor.FreeM.denote_bind_of_discrete` and `PFunctor.FreeM.denote_map_of_discrete` give the
  discrete Giry composition laws.
* `PFunctor.FreeM.denote_bind_bind_prod_mk_eq_prod` identifies two independent executions with
  Mathlib's product measure.
* Every program denotes a subprobability measure (`PFunctor.FreeM.denote_apply_univ_le_one`), and
  over discrete answers a probability measure (`PFunctor.FreeM.isProbabilityMeasure_denote`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe u v w uA uQ

namespace PFunctor

namespace FreeM

/-! ## The measure fold under arbitrary answer measures -/

section MeasureFold

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] (μ : (a : P.A) → Measure (P.B a))
  {α : Type v} {β : Type w}

open scoped Classical in
/-- The measure fold of a free program under per-operation answer measures `μ`. A measurable
continuation uses Giry bind; an unmeasurable continuation folds to zero. -/
noncomputable def measureFold [MeasurableSpace α] : FreeM P α → Measure α
  | .pure x => Measure.dirac x
  | .liftBind a cont =>
      if AEMeasurable (fun b => measureFold (cont b)) (μ a) then
        Measure.bind (μ a) fun b => measureFold (cont b)
      else 0

@[simp]
theorem measureFold_pure [MeasurableSpace α] (x : α) :
    measureFold μ (pure x : FreeM P α) = Measure.dirac x := rfl

theorem measureFold_liftBind [MeasurableSpace α] (a : P.A) (cont : P.B a → FreeM P α)
    (h : AEMeasurable (fun b => measureFold μ (cont b)) (μ a)) :
    measureFold μ (FreeM.liftBind a cont) = Measure.bind (μ a) fun b => measureFold μ (cont b) := by
  simp [measureFold, h]

/-- An unmeasurable operation continuation folds to zero. -/
theorem measureFold_liftBind_of_not_aemeasurable [MeasurableSpace α] (a : P.A)
    (cont : P.B a → FreeM P α) (h : ¬AEMeasurable (fun b => measureFold μ (cont b)) (μ a)) :
    measureFold μ (FreeM.liftBind a cont) = 0 := by
  simp [measureFold, h]

/-- A one-operation program folds to its answer measure. -/
@[simp]
theorem measureFold_lift (a : P.A) :
    measureFold μ (FreeM.lift a : FreeM P (P.B a)) = μ a := by
  rw [FreeM.lift, measureFold_liftBind μ a pure Measure.measurable_dirac.aemeasurable]
  exact Measure.bind_dirac

/-- Subprobability answer measures fold to a subprobability measure. Measurable continuations
keep the mass bound through integration; unmeasurable continuations fold to zero. -/
theorem measureFold_apply_univ_le_one [∀ a, IsSubprobabilityMeasure (μ a)] [MeasurableSpace α]
    (program : FreeM P α) : measureFold μ program Set.univ ≤ 1 := by
  induction program with
  | pure _ => simp
  | lift_bind a cont ih =>
      change measureFold μ (FreeM.liftBind a cont) Set.univ ≤ 1
      by_cases h : AEMeasurable (fun b => measureFold μ (cont b)) (μ a)
      · rw [measureFold_liftBind μ a cont h, Measure.bind_apply MeasurableSet.univ h]
        calc (∫⁻ b, measureFold μ (cont b) Set.univ ∂μ a) ≤ ∫⁻ _b, 1 ∂μ a := lintegral_mono ih
          _ = μ a Set.univ := by simp
          _ ≤ 1 := measure_univ_le (μ a)
      · simp only [measureFold_liftBind_of_not_aemeasurable μ a cont h, Measure.coe_zero,
          Pi.zero_apply, zero_le]

instance isSubprobabilityMeasure_measureFold [∀ a, IsSubprobabilityMeasure (μ a)]
    [MeasurableSpace α] (program : FreeM P α) : IsSubprobabilityMeasure (measureFold μ program) :=
  ⟨measureFold_apply_univ_le_one μ program⟩

/-- A one-operation program is a probability measure whenever its continuation is an
almost-everywhere measurable family of probability measures and its answer measure is a
probability measure.

This is the continuous composition boundary. For discrete answer types the measurability
hypothesis is automatic; for genuinely continuous answers it is precisely the obligation a
Mathlib `Kernel` represents. -/
theorem isProbabilityMeasure_measureFold_liftBind [MeasurableSpace α] (a : P.A)
    [IsProbabilityMeasure (μ a)] (cont : P.B a → FreeM P α)
    (hMeasurable : AEMeasurable (fun b => measureFold μ (cont b)) (μ a))
    (hProbability : ∀ᵐ b ∂μ a, IsProbabilityMeasure (measureFold μ (cont b))) :
    IsProbabilityMeasure (measureFold μ (FreeM.liftBind a cont)) := by
  rw [measureFold_liftBind μ a cont hMeasurable]
  refine ⟨?_⟩
  rw [Measure.bind_apply MeasurableSet.univ hMeasurable]
  calc (∫⁻ b, measureFold μ (cont b) Set.univ ∂μ a) = ∫⁻ _b, 1 ∂μ a :=
        lintegral_congr_ae (hProbability.mono fun b hb => by have := hb; exact measure_univ)
    _ = 1 := by simp

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- Probability answer measures over discrete answer types fold to a probability measure,
independently of the measurable space on the result. -/
theorem isProbabilityMeasure_measureFold [∀ a, IsProbabilityMeasure (μ a)] [MeasurableSpace α]
    (program : FreeM P α) : IsProbabilityMeasure (measureFold μ program) := by
  induction program with
  | pure _ => exact ⟨by simp⟩
  | lift_bind a cont ih =>
      exact isProbabilityMeasure_measureFold_liftBind μ a cont
        Measurable.of_discrete.aemeasurable (Filter.Eventually.of_forall ih)

/-- The fold preserves bind when the folded continuation is measurable. Discrete answer types
discharge the recursive measurability obligation inside the free program. -/
theorem measureFold_bind [MeasurableSpace α] [MeasurableSpace β] (program : FreeM P α)
    (f : α → FreeM P β) (hf : Measurable fun x => measureFold μ (f x)) :
    measureFold μ (FreeM.bind program f) =
      Measure.bind (measureFold μ program) fun x => measureFold μ (f x) := by
  induction program with
  | pure x => simpa using (Measure.dirac_bind hf x).symm
  | lift_bind a cont ih =>
      change measureFold μ (FreeM.liftBind a (fun b => (cont b).bind f)) =
        Measure.bind (measureFold μ (FreeM.liftBind a cont)) (fun x => measureFold μ (f x))
      rw [measureFold_liftBind μ _ _ Measurable.of_discrete.aemeasurable,
        measureFold_liftBind μ _ _ Measurable.of_discrete.aemeasurable]
      rw [Measure.bind_bind (Measurable.of_discrete).aemeasurable hf.aemeasurable]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun b => ih b)

/-- The fold turns a measurable map of results into the pushforward measure. -/
theorem measureFold_map_of_measurable [MeasurableSpace α] [MeasurableSpace β]
    (program : FreeM P α) (f : α → β) (hf : Measurable f) :
    measureFold μ (FreeM.map f program) = (measureFold μ program).map f := by
  rw [← FreeM.bind_pure_comp f program, measureFold_bind μ program (pure ∘ f)]
  · simpa only [Function.comp_apply, measureFold_pure] using
      Measure.bind_dirac_eq_map (measureFold μ program) hf
  · change Measurable (Measure.dirac ∘ f)
    exact Measure.measurable_dirac.comp hf

/-- **Substitution is pullback.** Folding a program simulated by a free handler under answer
measures `ν` is folding the source program under the measures the implementations fold to. This
is the measure counterpart of `PFunctor.FreeM.wpFold_liftM`. -/
theorem measureFold_liftM {Q : PFunctor.{uQ, u}} [∀ b, MeasurableSpace (Q.B b)]
    [∀ b, DiscreteMeasurableSpace (Q.B b)] (ν : (b : Q.A) → Measure (Q.B b))
    (handler : (a : P.A) → FreeM Q (P.B a)) {γ : Type u} [MeasurableSpace γ]
    (program : FreeM P γ) :
    measureFold ν (program.liftM handler) =
      measureFold (fun a => measureFold ν (handler a)) program := by
  induction program with
  | pure x => rfl
  | lift_bind a cont ih =>
      change measureFold ν (FreeM.bind (handler a) fun b => (cont b).liftM handler) =
        measureFold (fun a => measureFold ν (handler a)) (FreeM.liftBind a cont)
      rw [measureFold_bind ν _ _ Measurable.of_discrete,
        measureFold_liftBind _ a cont Measurable.of_discrete.aemeasurable]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun b => ih b)

end MeasureFold

/-! ## The denotation under answer measures -/

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  {α : Type v} {β : Type w}

/-- The measure denoted by a polynomial free program: its measure fold under the answer measures
of `PFunctor.AnswerMeasure`. -/
noncomputable def denote [MeasurableSpace α] (program : FreeM P α) : Measure α :=
  measureFold AnswerMeasure.toMeasure program

@[simp]
theorem denote_pure [MeasurableSpace α] (x : α) :
    denote (pure x : FreeM P α) = Measure.dirac x := rfl

theorem denote_liftBind [MeasurableSpace α] (a : P.A) (cont : P.B a → FreeM P α)
    (h : AEMeasurable (fun b => denote (cont b)) (AnswerMeasure.toMeasure a)) :
    denote (FreeM.liftBind a cont)
      = Measure.bind (AnswerMeasure.toMeasure a) fun b => denote (cont b) :=
  measureFold_liftBind _ a cont h

/-- An unmeasurable operation continuation has zero denotation. -/
theorem denote_liftBind_of_not_aemeasurable [MeasurableSpace α]
    (a : P.A) (cont : P.B a → FreeM P α)
    (h : ¬AEMeasurable (fun b => denote (cont b)) (AnswerMeasure.toMeasure a)) :
    denote (FreeM.liftBind a cont) = 0 :=
  measureFold_liftBind_of_not_aemeasurable _ a cont h

/-- A one-operation program denotes its configured answer measure. -/
@[simp]
theorem denote_lift (a : P.A) :
    denote (FreeM.lift a : FreeM P (P.B a)) = AnswerMeasure.toMeasure a :=
  measureFold_lift _ a

/-- A one-operation program is a probability measure whenever its continuation is an
almost-everywhere measurable family of probability measures. -/
theorem isProbabilityMeasure_denote_liftBind [MeasurableSpace α] (a : P.A)
    (cont : P.B a → FreeM P α)
    (hMeasurable : AEMeasurable (fun b => denote (cont b)) (AnswerMeasure.toMeasure a))
    (hProbability : ∀ᵐ b ∂AnswerMeasure.toMeasure a,
      IsProbabilityMeasure (denote (cont b))) :
    IsProbabilityMeasure (denote (FreeM.liftBind a cont)) :=
  isProbabilityMeasure_measureFold_liftBind _ a cont hMeasurable hProbability

/-- Every free program denotes a subprobability measure. -/
theorem denote_apply_univ_le_one [MeasurableSpace α] (program : FreeM P α) :
    denote program Set.univ ≤ 1 :=
  measureFold_apply_univ_le_one _ program

/-- Every free program denotes a subprobability measure. -/
instance isSubprobabilityMeasure_denote [MeasurableSpace α] (program : FreeM P α) :
    IsSubprobabilityMeasure (denote program) :=
  ⟨denote_apply_univ_le_one program⟩

/-! ## Giry composition laws -/

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- Every program over discrete answer types denotes a probability measure, independently of
the measurable space on its output. -/
@[instance]
theorem isProbabilityMeasure_denote [MeasurableSpace α] (program : FreeM P α) :
    IsProbabilityMeasure (denote program) :=
  isProbabilityMeasure_measureFold _ program

/-- `denote` preserves bind when the denoted continuation is measurable. -/
theorem denote_bind [MeasurableSpace α] [MeasurableSpace β]
    (program : FreeM P α) (f : α → FreeM P β)
    (hf : Measurable fun x => denote (f x)) :
    denote (FreeM.bind program f) = Measure.bind (denote program) fun x => denote (f x) :=
  measureFold_bind _ program f hf

/-- `denote` preserves bind unconditionally when the program's result type is discrete. -/
theorem denote_bind_of_discrete [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (program : FreeM P α) (f : α → FreeM P β) :
    denote (FreeM.bind program f) = Measure.bind (denote program) fun x => denote (f x) :=
  denote_bind program f Measurable.of_discrete

/-- `denote` turns a measurable map of program outputs into the pushforward measure. -/
theorem denote_map_of_measurable [MeasurableSpace α] [MeasurableSpace β]
    (program : FreeM P α) (f : α → β) (hf : Measurable f) :
    denote (FreeM.map f program) = (denote program).map f :=
  measureFold_map_of_measurable _ program f hf

/-- `denote` preserves every output map from a discrete result type. -/
theorem denote_map_of_discrete [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (program : FreeM P α) (f : α → β) :
    denote (FreeM.map f program) = (denote program).map f :=
  denote_map_of_measurable program f Measurable.of_discrete

/-- Sequentially running two programs whose second execution does not depend on the first result
denotes the product of their measures. -/
theorem denote_bind_bind_prod_mk_eq_prod [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (left : FreeM P α) (right : FreeM P β) :
    denote (FreeM.bind left fun x =>
      FreeM.bind right fun y => pure (x, y)) =
        (denote left).prod (denote right) := by
  rw [denote_bind_of_discrete left, Measure.prod_eq_of_sfinite]
  exact Measure.bind_congr_right (Filter.Eventually.of_forall fun x => by
    change denote (FreeM.bind right fun y => pure (x, y)) =
      Measure.map (Prod.mk x) (denote right)
    rw [denote_bind right (fun y => pure (x, y))]
    · simpa only [denote_pure] using
        Measure.bind_dirac_eq_map (denote right) (by fun_prop)
    · change Measurable (Measure.dirac ∘ Prod.mk x)
      exact Measure.measurable_dirac.comp (by fun_prop))

end FreeM

end PFunctor
