/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Deterministic

/-!
# Output measures with countable support

`CountableEvalDist m` states that the output measure of every computation is concentrated on a
countable set, in every measurable structure with measurable singletons. Countable concentration
is what lets pointwise conditional coupling witnesses be chosen almost everywhere measurably, so
it is the hypothesis of the relational algebra `ExpectationWP.couplingAlgebra`.

The deterministic carriers `Id`, `Option` and `Except ε` concentrate on at most one point. Free
programs over countable discrete answers concentrate on their possible outputs
(`PFunctor.FreeM.instCountableEvalDistFreeM`).
-/

public section

open MeasureTheory

universe u v

/-- The output measure of every computation is concentrated on a countable set, in every
measurable structure on the outputs with measurable singletons. -/
class CountableEvalDist (m : Type u → Type v) [EvalDistSemantics m] : Prop where
  /-- Each output measure is concentrated on a countable set. -/
  exists_countable_ae_mem {α : Type u} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : m α) : ∃ s : Set α, s.Countable ∧ ∀ᵐ x ∂evalDist mx, x ∈ s

/-- A Dirac measure is concentrated on its point. -/
theorem MeasureTheory.Measure.exists_countable_ae_mem_dirac {α : Type u} [MeasurableSpace α]
    [MeasurableSingletonClass α] (x : α) :
    ∃ s : Set α, s.Countable ∧ ∀ᵐ y ∂Measure.dirac x, y ∈ s :=
  ⟨{x}, Set.countable_singleton x, by
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl⟩

/-- The zero measure is concentrated on the empty set. -/
theorem MeasureTheory.Measure.exists_countable_ae_mem_zero {α : Type u} [MeasurableSpace α] :
    ∃ s : Set α, s.Countable ∧ ∀ᵐ y ∂(0 : Measure α), y ∈ s :=
  ⟨∅, Set.countable_empty, by simp⟩

/-- A deterministic total computation is concentrated on its value. -/
instance instCountableEvalDistId : CountableEvalDist Id.{u} where
  exists_countable_ae_mem mx := Measure.exists_countable_ae_mem_dirac mx.run

/-- An optional result is concentrated on its value, if any. -/
instance instCountableEvalDistOption : CountableEvalDist Option.{u} where
  exists_countable_ae_mem
    | none => Measure.exists_countable_ae_mem_zero
    | some x => Measure.exists_countable_ae_mem_dirac x

/-- An exceptional result is concentrated on its successful value, if any. -/
instance instCountableEvalDistExcept {ε : Type u} : CountableEvalDist (Except.{u, v} ε) where
  exists_countable_ae_mem
    | .error _ => Measure.exists_countable_ae_mem_zero
    | .ok x => Measure.exists_countable_ae_mem_dirac x
