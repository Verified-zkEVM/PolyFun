/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Basic
public import PolyFunProbability.PFunctor.AnswerMeasure
public import PolyFunProbability.ToMathlib.MeasureTheory.Measure.Subprobability

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

* `PFunctor.FreeM.denote` is the measure denoted by a free program.

## Main statements

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

universe u v w uA

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  {α : Type v} {β : Type w}

open scoped Classical in
/-- The measure denoted by a polynomial free program. A measurable continuation uses Giry bind;
an unmeasurable continuation denotes zero. Probability-mass preservation requires measurability. -/
noncomputable def denote [MeasurableSpace α] : FreeM P α → Measure α
  | .pure x => Measure.dirac x
  | .liftBind a cont =>
      if AEMeasurable (fun b => denote (cont b)) (AnswerMeasure.toMeasure a) then
        Measure.bind (AnswerMeasure.toMeasure a) fun b => denote (cont b)
      else 0

@[simp]
theorem denote_pure [MeasurableSpace α] (x : α) :
    denote (pure x : FreeM P α) = Measure.dirac x := rfl

theorem denote_liftBind [MeasurableSpace α] (a : P.A) (cont : P.B a → FreeM P α)
    (h : AEMeasurable (fun b => denote (cont b)) (AnswerMeasure.toMeasure a)) :
    denote (FreeM.liftBind a cont)
      = Measure.bind (AnswerMeasure.toMeasure a) fun b => denote (cont b) := by
  simp [denote, h]

/-- An unmeasurable operation continuation has zero denotation. -/
theorem denote_liftBind_of_not_aemeasurable [MeasurableSpace α]
    (a : P.A) (cont : P.B a → FreeM P α)
    (h : ¬AEMeasurable (fun b => denote (cont b)) (AnswerMeasure.toMeasure a)) :
    denote (FreeM.liftBind a cont) = 0 := by
  simp [denote, h]

/-- A one-operation program denotes its configured answer measure. -/
@[simp]
theorem denote_lift (a : P.A) :
    denote (FreeM.lift a : FreeM P (P.B a)) = AnswerMeasure.toMeasure a := by
  rw [FreeM.lift, denote_liftBind a pure Measure.measurable_dirac.aemeasurable]
  exact Measure.bind_dirac

/-- A one-operation program is a probability measure whenever its continuation is an
almost-everywhere measurable family of probability measures.

This is the continuous composition boundary. For discrete answer types the hypotheses are
automatic; for genuinely continuous answers they are precisely the obligations represented by
a Mathlib `Kernel`. -/
theorem isProbabilityMeasure_denote_liftBind [MeasurableSpace α] (a : P.A)
    (cont : P.B a → FreeM P α)
    (hMeasurable : AEMeasurable (fun b => denote (cont b)) (AnswerMeasure.toMeasure a))
    (hProbability : ∀ᵐ b ∂AnswerMeasure.toMeasure a,
      IsProbabilityMeasure (denote (cont b))) :
    IsProbabilityMeasure (denote (FreeM.liftBind a cont)) := by
  rw [denote_liftBind a cont hMeasurable]
  refine ⟨?_⟩
  rw [Measure.bind_apply MeasurableSet.univ hMeasurable]
  calc (∫⁻ b, denote (cont b) Set.univ ∂AnswerMeasure.toMeasure a)
      = ∫⁻ _b, 1 ∂AnswerMeasure.toMeasure a :=
        lintegral_congr_ae (hProbability.mono fun b hb => by have := hb; exact measure_univ)
    _ = 1 := by simp

/-! ## Giry composition laws -/

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- Every program over discrete answer types denotes a probability measure, independently of
the measurable space on its output. -/
@[instance]
theorem isProbabilityMeasure_denote [MeasurableSpace α] (program : FreeM P α) :
    IsProbabilityMeasure (denote program) := by
  induction program with
  | pure _ => exact ⟨by simp⟩
  | lift_bind a cont ih =>
      exact isProbabilityMeasure_denote_liftBind a cont
        Measurable.of_discrete.aemeasurable
        (Filter.Eventually.of_forall ih)

/-- `denote` preserves bind when the denoted continuation is measurable. Discrete answer types
discharge the recursive measurability obligation inside the free program. -/
theorem denote_bind [MeasurableSpace α] [MeasurableSpace β]
    (program : FreeM P α) (f : α → FreeM P β)
    (hf : Measurable fun x => denote (f x)) :
    denote (FreeM.bind program f) = Measure.bind (denote program) fun x => denote (f x) := by
  induction program with
  | pure x => simpa using (Measure.dirac_bind hf x).symm
  | lift_bind a cont ih =>
      change denote (FreeM.liftBind a (fun b => (cont b).bind f)) =
        Measure.bind (denote (FreeM.liftBind a cont)) (fun x => denote (f x))
      rw [denote_liftBind _ _ Measurable.of_discrete.aemeasurable,
        denote_liftBind _ _ Measurable.of_discrete.aemeasurable]
      rw [Measure.bind_bind (Measurable.of_discrete).aemeasurable hf.aemeasurable]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun b => ih b)

/-- `denote` preserves bind unconditionally when the program's result type is discrete. -/
theorem denote_bind_of_discrete [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (program : FreeM P α) (f : α → FreeM P β) :
    denote (FreeM.bind program f) = Measure.bind (denote program) fun x => denote (f x) :=
  denote_bind program f Measurable.of_discrete

/-- `denote` turns a measurable map of program outputs into the pushforward measure. -/
theorem denote_map_of_measurable [MeasurableSpace α] [MeasurableSpace β]
    (program : FreeM P α) (f : α → β) (hf : Measurable f) :
    denote (FreeM.map f program) = (denote program).map f := by
  rw [← FreeM.bind_pure_comp f program, denote_bind program (pure ∘ f)]
  · simpa only [Function.comp_apply, denote_pure] using
      Measure.bind_dirac_eq_map (denote program) hf
  · change Measurable (Measure.dirac ∘ f)
    exact Measure.measurable_dirac.comp hf

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

namespace FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  {α : Type v}

/-- Every free program denotes a subprobability measure. Measurable continuations preserve the
mass bound through integration; unmeasurable continuations have zero denotation. -/
theorem denote_apply_univ_le_one [MeasurableSpace α] (program : FreeM P α) :
    denote program Set.univ ≤ 1 := by
  induction program with
  | pure _ => simp
  | lift_bind a cont ih =>
      change denote (FreeM.liftBind a cont) Set.univ ≤ 1
      by_cases h : AEMeasurable (fun b => denote (cont b)) (AnswerMeasure.toMeasure a)
      · rw [denote_liftBind a cont h, Measure.bind_apply MeasurableSet.univ h]
        calc
          (∫⁻ b, denote (cont b) Set.univ ∂AnswerMeasure.toMeasure a) ≤
              ∫⁻ _b, 1 ∂AnswerMeasure.toMeasure a := lintegral_mono ih
          _ = 1 := by simp
      · simp only [denote_liftBind_of_not_aemeasurable a cont h, Measure.coe_zero,
          Pi.zero_apply, zero_le]

/-- Every free program denotes a subprobability measure. -/
instance isSubprobabilityMeasure_denote [MeasurableSpace α] (program : FreeM P α) :
    IsSubprobabilityMeasure (denote program) :=
  ⟨denote_apply_univ_le_one program⟩

end FreeM

end PFunctor
