/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Lossless
public import PolyFun.PFunctor.Free.Measure

/-!
# Measure semantics of polynomial free programs

`PFunctor.FreeM.denote` interprets a free program as a Mathlib `Measure` under the per-operation
answer measures of `PFunctor.AnswerMeasure`. This module makes that fold the `EvalDistSemantics`
of `PFunctor.FreeM P`, so `evalDist`, `prEvent` and `prFail` read it.

The instances name the universe of the results, `FreeM.{w, uA, u} P`, independently of the
universes of the operations and answers. A program over answers in `Type 1` therefore has a
measure semantics at results in `Type`, which `prEvent` needs.

The pure law holds for arbitrary answer spaces. Over discrete answer spaces the semantics is
lawful and lossless.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe w uA u

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  {α : Type w}

/-- The direct free-monad fold supplies measure semantics for a measure-valued specification. -/
noncomputable instance (priority := 20) instEvalDistSemanticsFreeM :
    EvalDistSemantics (FreeM.{w, uA, u} P) where
  denote := denote
  apply_univ_le_one := denote_apply_univ_le_one

/-- The direct free-monad measure fold preserves pure without any discreteness assumption on
oracle answers. -/
noncomputable instance (priority := 20) instLawfulPureEvalDistSemanticsFreeM :
    LawfulPureEvalDistSemantics (FreeM.{w, uA, u} P) where
  denote_pure := denote_pure

/-- With answer measures in scope, `evalDist` is definitionally the direct free-monad measure
fold. `evalDist` is the public head: this is a transport lemma, not a simp rule, so the
`evalDist`-keyed laws are the ones `simp` uses. -/
theorem evalDist_eq_denote [MeasurableSpace α] (program : FreeM P α) :
    evalDist program = denote program := rfl

/-- A one-operation program denotes its configured answer measure. -/
@[simp]
theorem evalDist_lift (a : P.A) :
    evalDist (FreeM.lift a : FreeM P (P.B a)) = AnswerMeasure.toMeasure a :=
  denote_lift a

/-- A one-operation program observed in a coarser measurable structure on its answers denotes the
configured answer measure trimmed to that structure. -/
theorem evalDist_lift_of_le (a : P.A) {m : MeasurableSpace (P.B a)}
    (hm : m ≤ ‹∀ a, MeasurableSpace (P.B a)› a) :
    @evalDist (FreeM P) _ (P.B a) m (FreeM.lift a) = (AnswerMeasure.toMeasure a).trim hm := by
  have hid : Measurable[‹∀ a, MeasurableSpace (P.B a)› a, m] (id : P.B a → P.B a) :=
    fun _ hs => hm _ hs
  have hdirac : Measurable[‹∀ a, MeasurableSpace (P.B a)› a]
      (fun b => @Measure.dirac (P.B a) m b) :=
    (@Measure.measurable_dirac _ m).comp hid
  have hcont : AEMeasurable (fun b => @denote P _ _ (P.B a) m (pure b))
      (AnswerMeasure.toMeasure a) := by
    simp only [denote_pure]
    exact hdirac.aemeasurable
  change @denote P _ _ (P.B a) m (FreeM.liftBind a pure) = _
  rw [@denote_liftBind P _ _ (P.B a) m a pure hcont]
  simp only [denote_pure]
  ext s hs
  rw [Measure.bind_apply hs hdirac.aemeasurable, trim_measurableSet_eq hm hs]
  simp only [Measure.dirac_apply' _ hs]
  exact lintegral_indicator_one (hm _ hs)

/-- A single operation denotes a probability measure, including for continuous answer spaces. -/
theorem isProbabilityMeasure_evalDist_lift (a : P.A) :
    IsProbabilityMeasure (evalDist (FreeM.lift a : FreeM P (P.B a))) := by
  rw [evalDist_lift]
  infer_instance

/-- An operation with an almost everywhere measurable continuation denotes Giry bind. -/
theorem evalDist_liftBind [MeasurableSpace α] (a : P.A) (cont : P.B a → FreeM P α)
    (h : AEMeasurable (fun b => denote (cont b)) (AnswerMeasure.toMeasure a)) :
    evalDist (FreeM.liftBind a cont) =
      Measure.bind (AnswerMeasure.toMeasure a) fun b => evalDist (cont b) :=
  denote_liftBind a cont h

/-- Integrating a single operation uses the tower law under AE-measurable continuation and
valuation hypotheses, including for continuous query answers. -/
theorem lintegral_evalDist_liftBind [MeasurableSpace α] (a : P.A)
    (cont : P.B a → FreeM P α)
    (hcont : AEMeasurable (fun b ↦ evalDist (cont b)) (AnswerMeasure.toMeasure a))
    {g : α → ENNReal} (hg : AEMeasurable g (evalDist (FreeM.liftBind a cont))) :
    ∫⁻ y, g y ∂evalDist (FreeM.liftBind a cont) =
      ∫⁻ b, ∫⁻ y, g y ∂evalDist (cont b) ∂AnswerMeasure.toMeasure a := by
  have hdenote : AEMeasurable (fun b ↦ denote (cont b)) (AnswerMeasure.toMeasure a) := by
    simpa only [evalDist_eq_denote] using hcont
  rw [evalDist_liftBind a cont hdenote] at hg ⊢
  exact Measure.lintegral_bind hcont hg

/-- A measurable pure function after one operation pushes forward its answer measure.
No discreteness assumption on the answer space is needed. The bind stays in one monad, so the
results share the universe of the answers. -/
theorem evalDist_lift_bind_pure {γ : Type u} [MeasurableSpace γ] (a : P.A) (f : P.B a → γ)
    (hf : Measurable f) :
    evalDist (FreeM.lift a >>= fun b ↦ pure (f b) : FreeM P γ) =
      (evalDist (FreeM.lift a : FreeM P (P.B a))).map f := by
  have hcont : AEMeasurable (fun b => denote (pure (f b) : FreeM P γ))
      (AnswerMeasure.toMeasure a) := by
    change AEMeasurable (Measure.dirac ∘ f) (AnswerMeasure.toMeasure a)
    exact (Measure.measurable_dirac.comp hf).aemeasurable
  change evalDist (FreeM.liftBind a (fun b => pure (f b))) = _
  rw [evalDist_liftBind (P := P) a _ hcont, evalDist_lift (P := P)]
  simp only [evalDist_pure]
  exact Measure.bind_dirac_eq_map _ hf

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

/-- Over a discrete-answer interface, every program denotes a probability measure. -/
instance (priority := 20) instLosslessEvalDistSemanticsFreeM :
    LosslessEvalDistSemantics (FreeM.{w, uA, u} P) where
  isProbabilityMeasure := isProbabilityMeasure_denote

/-- Over a discrete-answer interface, the direct measure semantics satisfies the Giry monad
laws. -/
noncomputable instance (priority := 20) instLawfulEvalDistSemanticsFreeM :
    LawfulEvalDistSemantics (FreeM.{w, uA, u} P) where
  denote_bind := denote_bind

end FreeM

end PFunctor
