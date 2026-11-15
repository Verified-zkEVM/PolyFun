/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Losslessness of measure-valued computations

A computation is lossless when it returns with probability one: its successful-output measure is
a probability measure, Mathlib's `IsProbabilityMeasure`. Bind preserves this property when its
continuation is lossless almost everywhere. Possible zero-probability branches impose no
additional obligation.

`LosslessEvalDistSemantics m` is the mixin stating that every computation of `m` is lossless, in
every measurable structure on its outputs. It is a `Prop` beside `EvalDistSemantics m`, in the
style of the lawful classes, and supplies the `IsProbabilityMeasure` instance of every
denotation.
-/

public section

open MeasureTheory

universe u v

/-- A measure semantics is lossless when every computation denotes a probability measure: no
computation fails or diverges with positive probability. -/
class LosslessEvalDistSemantics (m : Type u → Type v) [EvalDistSemantics m] : Prop where
  /-- Every computation denotes a probability measure. -/
  isProbabilityMeasure {α : Type u} [MeasurableSpace α] (mx : m α) :
    IsProbabilityMeasure (evalDist mx)

/-- Under a lossless semantics, every denotation is a probability measure. -/
instance evalDist.instIsProbabilityMeasure {m : Type u → Type v} [EvalDistSemantics m]
    [LosslessEvalDistSemantics m] {α : Type u} [MeasurableSpace α] (mx : m α) :
    IsProbabilityMeasure (evalDist mx) :=
  LosslessEvalDistSemantics.isProbabilityMeasure mx

/-- Under a lossless semantics, every computation has successful-output mass one. -/
theorem evalDist_apply_univ_of_lossless {m : Type u → Type v} [EvalDistSemantics m]
    [LosslessEvalDistSemantics m] {α : Type u} [MeasurableSpace α] (mx : m α) :
    evalDist mx Set.univ = 1 :=
  measure_univ

section

variable {m : Type u → Type v} [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]

/-- A measurable output map preserves losslessness on the chosen output spaces. -/
theorem evalDist.isProbabilityMeasure_map [LawfulMonad m]
    (mx : m α) [IsProbabilityMeasure (evalDist mx)] {f : α → β} (hf : Measurable f) :
    IsProbabilityMeasure (evalDist (f <$> mx)) := by
  constructor
  rw [evalDist_map_apply_univ mx hf, measure_univ]

/-- A lossless computation followed by almost everywhere lossless continuations is lossless. -/
theorem evalDist.isProbabilityMeasure_bind_of_ae (mx : m α) (f : α → m β)
    [IsProbabilityMeasure (evalDist mx)] (hf : Measurable fun a ↦ evalDist (f a))
    (hprob : ∀ᵐ a ∂evalDist mx, IsProbabilityMeasure (evalDist (f a))) :
    IsProbabilityMeasure (evalDist (mx >>= f)) := by
  rw [evalDist_bind mx f hf]
  refine ⟨?_⟩
  rw [Measure.bind_apply MeasurableSet.univ hf.aemeasurable]
  exact lintegral_eq_const (hprob.mono fun _ ha ↦ ha.measure_univ)

/-- For a lossless input, losslessness after bind means almost everywhere lossless continuation. -/
theorem evalDist.isProbabilityMeasure_bind_iff (mx : m α) (f : α → m β)
    [IsProbabilityMeasure (evalDist mx)] (hf : Measurable fun a ↦ evalDist (f a)) :
    IsProbabilityMeasure (evalDist (mx >>= f)) ↔
      ∀ᵐ a ∂evalDist mx, IsProbabilityMeasure (evalDist (f a)) := by
  simp only [isProbabilityMeasure_iff, evalDist_bind mx f hf,
    Measure.bind_apply MeasurableSet.univ hf.aemeasurable]
  have hfinite : (∫⁻ a, evalDist (f a) Set.univ ∂evalDist mx) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤) <| by
      calc
        (∫⁻ a, evalDist (f a) Set.univ ∂evalDist mx) ≤ ∫⁻ _ : α, 1 ∂evalDist mx :=
          lintegral_mono fun a ↦ evalDist_apply_univ_le_one (f a)
        _ = 1 := by simp
  have h : (∫⁻ a, evalDist (f a) Set.univ ∂evalDist mx) = 1 ↔
      (fun a ↦ evalDist (f a) Set.univ) =ᵐ[evalDist mx] (fun _ ↦ 1) := by
    simpa only [lintegral_const, measure_univ, mul_one] using
      lintegral_eq_iff_ae_eq_of_ae_le
        (μ := evalDist mx) (f := fun a ↦ evalDist (f a) Set.univ) (g := fun _ ↦ 1)
        hfinite
        measurable_const.aemeasurable
        (Filter.Eventually.of_forall fun a ↦ evalDist_apply_univ_le_one (f a))
  exact h

/-- Pointwise losslessness is a sufficient discrete bind rule with no source-space argument. -/
theorem evalDist.isProbabilityMeasure_bind (mx : m α) (f : α → m β)
    [DiscreteMeasurableSpace α] [IsProbabilityMeasure (evalDist mx)]
    (hprob : ∀ a, IsProbabilityMeasure (evalDist (f a))) :
    IsProbabilityMeasure (evalDist (mx >>= f)) :=
  evalDist.isProbabilityMeasure_bind_of_ae mx f Measurable.of_discrete
    (Filter.Eventually.of_forall hprob)

end
