/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure
public import PolyFun.Control.Monad.Algebra

/-!
# The expectation algebra of a measure semantics

`ExpectationWP.algebra m` integrates the value of a computation `mx : m ℝ≥0∞` against its
successful-output measure. It is an ordered monad algebra (`MAlgOrdered`) for every lawful
measure semantics, so PolyFun's program-logic bridges make it an exact weakest-precondition
interpretation, in which a postcondition's precondition is its expectation
(`ExpectationWP.algebra_μ_bind_pure`). Failure contributes zero, so the expectation is not
normalised by the success mass. The construction needs neither losslessness nor discrete outputs.

The carrier of an ordered monad algebra lies in the universe of the values of the monad, so
`ExpectationWP.algebra` applies to monads on `Type`. `ExpectationWP.algebraULift m` is the same
algebra over `ULift ℝ≥0∞`, for a monad on any universe.

Both algebras are definitions, not instances. On free programs they agree with the fold of the
integration spec (`ExpectationWP.algebra_freeM`, in `PolyFun.PFunctor.Free.Measure.Expectation`).
-/

public section

open MeasureTheory
open scoped ENNReal

universe u v

namespace ExpectationWP

/-! ## Values in `Type` -/

section Algebra

variable (m : Type → Type v) [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- The ordered algebra of nonnegative expectations under successful-output measures. -/
@[expose, instance_reducible]
noncomputable def algebra : MAlgOrdered m ℝ≥0∞ where
  μ mx := ∫⁻ x, x ∂evalDist mx
  μ_pure x := by simp
  μ_bind_mono {α} f g hfg mx := by
    let _ : MeasurableSpace α := ⊤
    change ∫⁻ y, y ∂evalDist (mx >>= f) ≤ ∫⁻ y, y ∂evalDist (mx >>= g)
    rw [lintegral_evalDist_bind_of_discrete mx f (g := fun y => y) measurable_id,
      lintegral_evalDist_bind_of_discrete mx g (g := fun y => y) measurable_id]
    exact lintegral_mono hfg

variable {m}

theorem algebra_μ (mx : m ℝ≥0∞) : (algebra m).μ mx = ∫⁻ x, x ∂evalDist mx :=
  rfl

/-- The expectation algebra sends a computation with a measurable mapped output to the integral of
the map. This is the value of `wp mx post` in its weakest-precondition interpretation. -/
theorem algebra_μ_bind_pure {α : Type} [MeasurableSpace α] (mx : m α) {post : α → ℝ≥0∞}
    (hpost : Measurable post) :
    (algebra m).μ (mx >>= fun a => pure (post a)) = ∫⁻ a, post a ∂evalDist mx := by
  have hf : Measurable fun a => evalDist (pure (post a) : m ℝ≥0∞) := by
    simpa only [evalDist_pure, Function.comp_def] using Measure.measurable_dirac.comp hpost
  rw [algebra_μ, lintegral_evalDist_bind mx _ hf (g := fun y => y) measurable_id]
  simp

end Algebra

/-! ## Values in every universe -/

section AlgebraULift

variable (m : Type u → Type v) [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- The ordered algebra of nonnegative expectations under successful-output measures, for a monad
on any universe: the expectation lifted to `ULift ℝ≥0∞`. -/
@[expose, instance_reducible]
noncomputable def algebraULift : MAlgOrdered m (ULift.{u} ℝ≥0∞) where
  μ mx := ⟨∫⁻ x, x.down ∂evalDist mx⟩
  μ_pure x := by
    change (⟨∫⁻ y, y.down ∂evalDist (pure x : m (ULift ℝ≥0∞))⟩ : ULift ℝ≥0∞) = x
    rw [evalDist_pure, lintegral_dirac' x measurable_down]
  μ_bind_mono {α} f g hfg mx := by
    let _ : MeasurableSpace α := ⊤
    change ∫⁻ y, y.down ∂evalDist (mx >>= f) ≤ ∫⁻ y, y.down ∂evalDist (mx >>= g)
    rw [lintegral_evalDist_bind_of_discrete mx f measurable_down,
      lintegral_evalDist_bind_of_discrete mx g measurable_down]
    exact lintegral_mono hfg

variable {m}

theorem algebraULift_μ (mx : m (ULift.{u} ℝ≥0∞)) :
    (algebraULift m).μ mx = ⟨∫⁻ x, x.down ∂evalDist mx⟩ :=
  rfl

/-- The lifted expectation algebra sends a computation with a measurable mapped output to the
integral of the map. -/
theorem algebraULift_μ_bind_pure {α : Type u} [MeasurableSpace α] (mx : m α)
    {post : α → ℝ≥0∞} (hpost : Measurable post) :
    (algebraULift m).μ (mx >>= fun a => pure ⟨post a⟩) = ⟨∫⁻ a, post a ∂evalDist mx⟩ := by
  have hf : Measurable fun a => evalDist (pure ⟨post a⟩ : m (ULift.{u} ℝ≥0∞)) := by
    simpa only [evalDist_pure, Function.comp_def] using
      Measure.measurable_dirac.comp (measurable_up.comp hpost)
  rw [algebraULift_μ, lintegral_evalDist_bind mx _ hf measurable_down]
  congr 1
  refine lintegral_congr fun a => ?_
  rw [evalDist_pure, lintegral_dirac' _ measurable_down]

end AlgebraULift

end ExpectationWP
