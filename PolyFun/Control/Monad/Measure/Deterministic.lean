/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Event
public import PolyFun.Control.Monad.Measure.Failure

/-!
# Successful-output measures for deterministic computations

`Id` returns its unique value with Dirac measure, so its semantics is lossless. `Option` and
`Except` assign Dirac measure to successful values and zero measure to failures. Error values need
no measurable structure when only successful outputs are observed. These interpretations satisfy
the measurable Giry laws.
-/

public section

open MeasureTheory

universe u v

/-- A deterministic total computation denotes its Dirac output measure. -/
noncomputable instance (priority := 20) instEvalDistSemanticsId : EvalDistSemantics Id.{u} where
  denote mx := Measure.dirac mx.run
  apply_univ_le_one _ := by simp

/-- The unique returned value determines a deterministic computation's measure. -/
@[simp, grind norm]
theorem Id.evalDist_eq_dirac {α : Type u} [MeasurableSpace α] (mx : Id α) :
    evalDist mx = Measure.dirac mx.run := rfl

/-- Every deterministic total computation denotes a probability measure. -/
instance Id.isProbabilityMeasure_evalDist {α : Type u} [MeasurableSpace α] (mx : Id α) :
    IsProbabilityMeasure (evalDist mx) := by
  rw [Id.evalDist_eq_dirac]
  infer_instance

/-- Deterministic total computations never fail. -/
instance (priority := 20) instLosslessEvalDistSemanticsId : LosslessEvalDistSemantics Id.{u} where
  isProbabilityMeasure := Id.isProbabilityMeasure_evalDist

/-- Deterministic total computations respect the measurable Giry laws. -/
instance (priority := 20) instLawfulEvalDistSemanticsId : LawfulEvalDistSemantics Id.{u} where
  denote_pure _ := rfl
  denote_bind mx _ hf := (Measure.dirac_bind hf mx.run).symm

/-- A deterministic optional result denotes zero on failure and a Dirac measure on success. -/
noncomputable instance (priority := 20) instEvalDistSemanticsOption :
    EvalDistSemantics Option.{u} where
  denote mx := mx.elim 0 Measure.dirac
  apply_univ_le_one mx := by cases mx <;> simp

/-- An absent optional result has no successful-output mass. -/
@[simp, grind =]
theorem Option.evalDist_none {α : Type u} [MeasurableSpace α] :
    evalDist (none : Option α) = 0 := rfl

/-- Deterministic optional failure has zero successful-output measure. -/
instance (priority := 20) instLawfulFailureEvalDistSemanticsOption :
    LawfulFailureEvalDistSemantics Option.{u} where
  denote_failure := Option.evalDist_none

/-- A present optional result has its Dirac output measure. -/
@[simp, grind =]
theorem Option.evalDist_some {α : Type u} [MeasurableSpace α] (x : α) :
    evalDist (some x : Option α) = Measure.dirac x := rfl

/-- A present optional result denotes a probability measure. -/
instance Option.isProbabilityMeasure_evalDist_some {α : Type u} [MeasurableSpace α] (x : α) :
    IsProbabilityMeasure (evalDist (some x : Option α)) := by
  rw [Option.evalDist_some]
  infer_instance

/-- Deterministic optional computations respect the measurable Giry laws. -/
instance (priority := 20) instLawfulEvalDistSemanticsOption :
    LawfulEvalDistSemantics Option.{u} where
  denote_pure _ := rfl
  denote_bind mx f hf := by
    cases mx with
    | none => exact (Measure.bind_zero_left fun x ↦ evalDist (f x)).symm
    | some x => exact (Measure.dirac_bind hf x).symm

/-- A deterministic exceptional result assigns mass only to its successful output. The header
names the universe of the results, so the instance applies at every universe. -/
noncomputable instance (priority := 20) instEvalDistSemanticsExcept {ε : Type u} :
    EvalDistSemantics (Except.{u, v} ε) where
  denote mx := match mx with
    | .error _ => 0
    | .ok x => Measure.dirac x
  apply_univ_le_one mx := by cases mx <;> simp

/-- An exceptional result has no successful-output mass. -/
@[simp, grind =]
theorem Except.evalDist_error {ε : Type u} {α : Type v} [MeasurableSpace α] (error : ε) :
    evalDist (Except.error error : Except ε α) = 0 := rfl

/-- A successful exceptional result has its Dirac output measure. -/
@[simp, grind =]
theorem Except.evalDist_ok {ε : Type u} {α : Type v} [MeasurableSpace α] (x : α) :
    evalDist (Except.ok x : Except ε α) = Measure.dirac x := rfl

/-- A successful exceptional result denotes a probability measure. -/
instance Except.isProbabilityMeasure_evalDist_ok {ε : Type u} {α : Type v}
    [MeasurableSpace α] (x : α) :
    IsProbabilityMeasure (evalDist (Except.ok x : Except ε α)) := by
  rw [Except.evalDist_ok]
  infer_instance

/-- Deterministic exceptional computations respect the measurable Giry laws. -/
instance (priority := 20) instLawfulEvalDistSemanticsExcept {ε : Type u} :
    LawfulEvalDistSemantics (Except.{u, v} ε) where
  denote_pure _ := rfl
  denote_bind mx f hf := by
    cases mx with
    | error _ => exact (Measure.bind_zero_left fun x ↦ evalDist (f x)).symm
    | ok x => exact (Measure.dirac_bind hf x).symm

/-! ## Events of deterministic computations -/

/-- An absent optional result makes every event impossible. -/
@[simp, grind =]
theorem Option.prEvent_none : prEvent (none : Option Prop) = 0 := by
  rw [prEvent_def, Option.evalDist_none, Measure.coe_zero, Pi.zero_apply]

/-- A present optional proposition has probability one exactly when it holds. -/
@[simp, grind =]
theorem Option.prEvent_some (P : Prop) [Decidable P] :
    prEvent (some P) = if P then 1 else 0 :=
  prEvent_pure_prop (m := Option) P

/-- No event of an absent optional result succeeds. -/
@[grind =]
theorem Option.prEvent_map_none {α : Type} (p : α → Prop) :
    prEvent (p <$> (none : Option α)) = 0 :=
  Option.prEvent_none

/-- An event of a present optional result has probability one exactly when it holds. -/
@[grind =]
theorem Option.prEvent_map_some {α : Type} (p : α → Prop) (x : α) [Decidable (p x)] :
    prEvent (p <$> some x) = if p x then 1 else 0 :=
  Option.prEvent_some (p x)

/-- An exceptional result makes every event impossible. -/
@[simp, grind =]
theorem Except.prEvent_error {ε : Type u} (error : ε) :
    prEvent (Except.error error : Except ε Prop) = 0 := by
  rw [prEvent_def, Except.evalDist_error, Measure.coe_zero, Pi.zero_apply]

/-- A successful exceptional proposition has probability one exactly when it holds. -/
@[simp, grind =]
theorem Except.prEvent_ok {ε : Type u} (P : Prop) [Decidable P] :
    prEvent (Except.ok P : Except ε Prop) = if P then 1 else 0 :=
  prEvent_pure_prop (m := Except ε) P

/-- No event of an exceptional result succeeds. -/
@[grind =]
theorem Except.prEvent_map_error {ε : Type u} {α : Type} (p : α → Prop) (error : ε) :
    prEvent (p <$> (Except.error error : Except ε α)) = 0 :=
  Except.prEvent_error error

/-- An event of a successful exceptional result has probability one exactly when it holds. -/
@[grind =]
theorem Except.prEvent_map_ok {ε : Type u} {α : Type} (p : α → Prop) (x : α)
    [Decidable (p x)] : prEvent (p <$> (Except.ok x : Except ε α)) = if p x then 1 else 0 :=
  Except.prEvent_ok (p x)
