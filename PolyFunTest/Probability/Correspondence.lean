/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Uniform
public import PolyFun.Control.Semantics.Measure

/-!
# Pushforwards of certified meanings

Regression tests for the measure pushforwards of `Control.Semantics.CertifiedMeaning` and
`Control.Semantics.CorrespondsOn`. The certified meaning `double` doubles an extended natural
number, and its implementation doubles a natural number. Under a uniform draw from a set of
natural numbers, the meaning's pushforward of the draw is the uniform measure on the encoded
doubles. Running the meaning on the encoded draw is therefore a uniform draw from them. An
implementation that doubles only below four corresponds to the same meaning on the inputs below
four, which gives the pushforward equation for a uniform draw from those inputs.
-/

public section

open MeasureTheory ProbabilityTheory EvalDist Control.Semantics

namespace PolyFunTest.Probability.Correspondence

/-- The natural numbers inside the extended natural numbers. -/
@[expose] def natEmbedding : ℕ ↪ ℕ∞ := ⟨(↑), fun _ _ ↦ ENat.natCast_inj.1⟩

@[simp]
theorem natEmbedding_apply (n : ℕ) : natEmbedding n = n := rfl

/-- Doubling: the meaning doubles in `ℕ∞`, where it also sends `⊤`, which encodes no natural
number, to `⊤`, and the implementation doubles in `ℕ`. -/
@[expose] def double : CertifiedMeaning natEmbedding natEmbedding where
  meaning n := 2 * n
  implementation n := 2 * n
  correct n := by simp

/-- The implementation of `double` is injective on every set. -/
theorem injOn_double_implementation (s : Set ℕ) : Set.InjOn double.implementation s :=
  (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)).injOn

variable {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- The meaning's pushforward of a uniform draw is the uniform measure on the encoded doubles. -/
theorem map_double_meaning [MeasurableSpace ℕ∞] [MeasurableSingletonClass ℕ∞] {mx : m ℕ}
    {s : Set ℕ} (h : IsUniformOn mx s) :
    (evalDist mx).map (double.meaning ∘ natEmbedding) =
      uniformOn (natEmbedding '' (double.implementation '' s)) := by
  rw [double.evalDist_map_meaning mx Measurable.of_discrete Measurable.of_discrete,
    (h.map_of_injOn (injOn_double_implementation s)).evalDist_eq,
    map_uniformOn_of_injOn Measurable.of_discrete natEmbedding.injective.injOn]

/-- Running the meaning on the encoded draw is a uniform draw from the encoded doubles. -/
example {mx : m ℕ} {s : Set ℕ} (h : IsUniformOn mx s) :
    IsUniformOn ((double.meaning ∘ natEmbedding) <$> mx)
      (natEmbedding '' (double.implementation '' s)) := by
  constructor
  intro _ _
  rw [evalDist_map_of_discrete, map_double_meaning h]

/-- An implementation that doubles only below four corresponds to the doubling meaning on the
inputs below four. -/
theorem correspondsOn_doubleBelowFour :
    CorrespondsOn natEmbedding natEmbedding (· < 4) double.meaning
      (fun n ↦ if n < 4 then 2 * n else 0) := by
  intro n hn
  simp [hn, double]

/-- Almost every draw from the inputs below four is admissible, so the meaning's pushforward is
the encoding of the partial implementation's output measure. -/
example [MeasurableSpace ℕ∞] [MeasurableSingletonClass ℕ∞] {mx : m ℕ}
    (h : IsUniformOn mx (Set.Iio 4)) :
    (evalDist mx).map (double.meaning ∘ natEmbedding) =
      (evalDist ((fun n ↦ if n < 4 then 2 * n else 0) <$> mx)).map natEmbedding := by
  refine correspondsOn_doubleBelowFour.evalDist_map_meaning_ae ?_ Measurable.of_discrete
    Measurable.of_discrete
  rw [ae_iff, h.evalDist_eq, uniformOn_eq_zero_iff (Set.finite_Iio 4)]
  ext n
  simp

end PolyFunTest.Probability.Correspondence
