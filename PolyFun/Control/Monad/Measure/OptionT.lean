/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Failure
public import ToCslib.MeasureTheory.Measure.Option

/-!
# Successful-output measure semantics for optional computations

An `OptionT` computation denotes the pullback of its underlying `Option`-valued measure along the
measurable embedding `some`.

The map and monad laws use the base monad's measure laws. The full bind law only requires
measurability of the successful-output family. A pullback space recording the full continuation
outcomes refines the selected source space, and the map law transports its measure back.

Successful-output semantics turns a sampled guard into a condition on the sampled value. The
intermediate measurable space is internal to the observation law, and wrapped computations are
observed through their present values. Lifting a computation into `OptionT` adds no failure.

The instances have priority 20, below the default, as in VCVio, so that an instance for a monad
that unfolds to `OptionT m` takes precedence over these generic ones.
-/

public section

open MeasureTheory
open scoped EvalDistSemantics

universe u v

/-- Interpret successful `OptionT` results by pulling the run measure back along `some`. -/
noncomputable instance (priority := 20) instEvalDistSemanticsOptionT
    {m : Type u → Type v} [EvalDistSemantics m] :
    EvalDistSemantics (OptionT m) where
  denote mx := (evalDist mx.run).comap some
  apply_univ_le_one mx :=
    calc
      (evalDist mx.run).comap some Set.univ = evalDist mx.run (some '' Set.univ) :=
        Option.measurableEmbedding_some.comap_apply _ _
      _ ≤ evalDist mx.run Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ 1 := evalDist_apply_univ_le_one mx.run

/-- Unfold the successful-output semantics to Mathlib's pullback along `some`. -/
theorem OptionT.evalDist_eq_comap_some
    {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : OptionT m α) :
    evalDist mx = (evalDist mx.run).comap some := by
  rfl

/-- An `OptionT` computation denotes the `dropNone` of its run: the `none` branch is discarded
mass, not an output. -/
theorem OptionT.evalDist_eq_dropNone
    {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : OptionT m α) :
    evalDist mx = (evalDist mx.run).dropNone :=
  (Measure.dropNone_eq_comap_some _).symm

/-- The successful-output measure of an optional computation on an event is the run
measure of the corresponding `some` outcomes. -/
theorem OptionT.evalDist_apply
    {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : OptionT m α) {event : Set α} :
    evalDist mx event = evalDist mx.run (some '' event) :=
  Option.measurableEmbedding_some.comap_apply _ _

/-- The successful mass of an optional computation is the mass of present values in its run. -/
@[simp]
theorem OptionT.evalDist_apply_univ
    {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : OptionT m α) :
    evalDist mx Set.univ = evalDist mx.run {value | value.isSome} :=
  by
    rw [OptionT.evalDist_apply]
    congr 1
    ext value
    cases value <;> simp

/-- Pure optional computations have Dirac successful-output semantics. -/
theorem OptionT.evalDist_pure
    {m : Type u → Type v} [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (x : α) :
    evalDist (pure x : OptionT m α) = Measure.dirac x := by
  rw [OptionT.evalDist_eq_comap_some, OptionT.run_pure, _root_.evalDist_pure,
    ← Measure.dropNone_eq_comap_some, Measure.dropNone_dirac_some]

/-- Optional semantics preserves pure whenever the base semantics does. -/
instance (priority := 20) instLawfulPureEvalDistSemanticsOptionT
    {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulPureEvalDistSemantics m] : LawfulPureEvalDistSemantics (OptionT m) where
  denote_pure := OptionT.evalDist_pure

/-- Optional failure has no successful-output mass. -/
theorem OptionT.evalDist_failure
    {m : Type u → Type v} [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] : evalDist (failure : OptionT m α) = 0 := by
  rw [OptionT.evalDist_eq_comap_some,
    show (failure : OptionT m α).run = pure none from rfl, _root_.evalDist_pure,
    ← Measure.dropNone_eq_comap_some, Measure.dropNone_dirac_none]

/-- Optional failure has zero measure whenever the base semantics preserves pure. -/
instance (priority := 20) instLawfulFailureEvalDistSemanticsOptionT
    {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulPureEvalDistSemantics m] : LawfulFailureEvalDistSemantics (OptionT m) where
  denote_failure := OptionT.evalDist_failure

/-- Lifting a computation into `OptionT` preserves its successful-output measure. -/
@[simp]
theorem OptionT.evalDist_lift
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) :
    evalDist (OptionT.lift mx) = evalDist mx := by
  rw [OptionT.evalDist_eq_comap_some, OptionT.run_lift,
    LawfulMonad.bind_pure_comp, _root_.evalDist_map mx Option.measurable_some,
    Option.measurableEmbedding_some.comap_map]

/-- A monadic lift into the optional monad preserves the successful-output measure. -/
@[simp]
theorem OptionT.evalDist_liftM
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) :
    evalDist (liftM mx : OptionT m α) = evalDist mx :=
  OptionT.evalDist_lift mx

/-- Lifting a lossless computation into the optional monad preserves its probability measure. -/
instance OptionT.isProbabilityMeasure_evalDist_lift
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) [IsProbabilityMeasure (evalDist mx)] :
    IsProbabilityMeasure (evalDist (OptionT.lift mx)) := by
  rw [OptionT.evalDist_lift]
  infer_instance

/-- A monadic lift into the optional monad preserves a known probability measure. -/
instance OptionT.isProbabilityMeasure_evalDist_liftM
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) [IsProbabilityMeasure (evalDist mx)] :
    IsProbabilityMeasure (evalDist (liftM mx : OptionT m α)) :=
  OptionT.isProbabilityMeasure_evalDist_lift mx

/-- A measurable map of successful optional results is the measure pushforward. -/
theorem OptionT.evalDist_map
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : OptionT m α) (f : α → β) (hf : Measurable f) :
    evalDist (f <$> mx) = (evalDist mx).map f := by
  simp only [OptionT.evalDist_eq_comap_some, ← Measure.dropNone_eq_comap_some]
  rw [OptionT.run_map, _root_.evalDist_map mx.run (by fun_prop), Measure.dropNone_map _ f hf]

/-- A measurable family of full run measures suffices to compose optional denotations. -/
theorem OptionT.evalDist_bind
    {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : OptionT m α) (f : α → OptionT m β)
    (hf : Measurable fun x => evalDist (f x).run) :
    evalDist (mx >>= f) = Measure.bind (evalDist mx) fun x => evalDist (f x) := by
  simp_rw [OptionT.evalDist_eq_comap_some]
  simp_rw [← Measure.dropNone_eq_comap_some]
  have hCont : (fun value : Option α =>
      evalDist (value.elim (pure none) fun x => (f x).run)) =
      (fun value => value.elim (Measure.dirac none) fun x => evalDist (f x).run) := by
    funext value
    cases value <;> simp only [Option.elim_none, Option.elim_some, _root_.evalDist_pure]
  have hBindCont : Measurable fun value : Option α =>
      evalDist (value.elim (pure none) fun x => (f x).run) := by
    rw [hCont]
    exact Option.measurable_elim' _ hf
  rw [OptionT.run_bind, Option.elimM,
    _root_.evalDist_bind mx.run
      (fun value => value.elim (pure none) fun x => (f x).run) hBindCont]
  rw [hCont]
  exact Measure.dropNone_bind (evalDist mx.run) (fun x => evalDist (f x).run) hf

/-- Discrete intermediate values discharge the run-measurability premise of
`OptionT.evalDist_bind`. -/
theorem OptionT.evalDist_bind_of_discrete
    {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (mx : OptionT m α) (f : α → OptionT m β) :
    evalDist (mx >>= f) = Measure.bind (evalDist mx) fun x => evalDist (f x) :=
  OptionT.evalDist_bind mx f Measurable.of_discrete

/-- Optional semantics satisfies the measurable-bind law for successful-output families. The
full-run observer refines the source space, whose identity map transports the source measure. -/
instance (priority := 20) instLawfulEvalDistSemanticsOptionT
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] :
    LawfulEvalDistSemantics (OptionT m) where
  denote_bind {α β} mα mβ mx f hf := by
    let mObs := mα ⊔ MeasurableSpace.comap (fun x ↦ evalDist (f x).run) inferInstance
    have hId : @Measurable α α mObs mα id :=
      Measurable.of_comap_le (by simpa only [MeasurableSpace.comap_id] using
        (le_sup_left : mα ≤ mObs))
    have hRun : @Measurable α (Measure (Option β)) mObs _
        (fun x ↦ evalDist (f x).run) := Measurable.of_comap_le le_sup_right
    have hmap := @OptionT.evalDist_map m _ _ _ _ α α mObs mα mx id hId
    rw [id_map] at hmap
    rw [hmap, @Measure.bind_map α α mObs mα β mβ _ _ _
      (@Measurable.aemeasurable α α mObs mα id _ hId) hf.aemeasurable]
    exact @OptionT.evalDist_bind m _ _ _ α β mObs mβ mx f hRun

/-- The successful-output measure of sampling and then guarding is the measure of the
corresponding Boolean event. This statement is independent of which global `OptionT`
semantics wins instance synthesis. -/
@[simp]
theorem OptionT.dropNone_evalDist_run_bind_guard_apply_univ
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) [DecidablePred p] :
    (evalDist (do let x ← mx; (guard (p x) : OptionT m Unit).run)).dropNone Set.univ =
      evalDist (do let x ← mx; pure (p x)) {True} := by
  let : MeasurableSpace α := MeasurableSpace.comap p inferInstance
  have hp : Measurable p := comap_measurable p
  have hpSet : MeasurableSet {x | p x} := by
    simpa only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true] using
      hp (measurableSet_singleton True)
  have hselect : Measurable fun x ↦ if p x then some () else none :=
    Measurable.ite hpSet measurable_const measurable_const
  have hrun : (do let x ← mx; (guard (p x) : OptionT m Unit).run) =
      (do let x ← mx; pure (if p x then some () else none)) := by
    apply bind_congr
    intro x
    by_cases hx : p x <;> simp [hx]
  rw [Measure.dropNone_apply_univ, hrun, LawfulMonad.bind_pure_comp,
    LawfulMonad.bind_pure_comp]
  rw [_root_.evalDist_map_apply mx hselect Option.measurableSet_isSome,
    _root_.evalDist_map_apply mx hp (measurableSet_singleton True)]
  congr 1
  ext x
  simp

/-! ## Events of optional computations -/

namespace OptionT

/-- Successful events are the events of present values in the underlying run. -/
theorem prEvent_eq_run {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : OptionT m α) (p : α → Prop) :
    prEvent (p <$>ₘ mx) = prEvent ((fun value ↦ value.elim False p) <$> mx.run) := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete,
    OptionT.evalDist_apply]
  congr 1
  ext value
  cases value <;> simp

/-- Lifting into the optional monad preserves the probability of an observed event. -/
@[simp↓ high, grind norm↓]
theorem prEvent_lift {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) :
    prEvent (p <$>ₘ OptionT.lift mx) = prEvent (p <$> mx) := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete,
    OptionT.evalDist_lift]

/-- A monadic lift into the optional monad preserves the probability of an observed event. -/
@[simp↓ high, grind norm↓]
theorem prEvent_liftM {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) :
    prEvent (p <$>ₘ (liftM mx : OptionT m α)) = prEvent (p <$> mx) :=
  prEvent_lift mx p

/-- A guard contributes its condition to the observed event after a lifted draw. -/
@[simp↓ high, grind norm↓]
theorem prEvent_bind_guard {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p q : α → Prop) [DecidablePred p] :
    prEvent (OptionT.lift mx >>= fun x ↦ (fun _ ↦ q x) <$>ₘ (guard (p x) : OptionT m Unit)) =
      prEvent ((fun x ↦ p x ∧ q x) <$> mx) := by
  classical
  let : MeasurableSpace α := ⊤
  have h (x : α) : prEvent ((fun _ ↦ q x) <$>ₘ (guard (p x) : OptionT m Unit)) =
      if p x ∧ q x then 1 else 0 := by
    by_cases hp : p x <;> by_cases hq : q x <;> simp [guard, hp, hq]
  rw [prEvent_bind_of_discrete, OptionT.evalDist_lift]
  simp_rw [h]
  rw [prEvent_eq_evalDist_of_discrete]
  simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using
    lintegral_indicator_one (μ := evalDist mx)
      (MeasurableSet.of_discrete (s := {x | p x ∧ q x}))

/-- A lifted draw followed by a guard puts its successful event mass at the unit output. -/
@[simp↓ high]
theorem evalDist_lift_bind_guard {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) [DecidablePred p] :
    evalDist (do let x ← OptionT.lift mx; guard (p x)) =
      prEvent (p <$> mx) • Measure.dirac () := by
  apply Measure.ext_of_singleton
  rintro ⟨⟩
  rw [← prEvent_eq_evalDist_singleton]
  simp

/-- A monadic lift followed by a guard puts its successful event mass at the unit output. -/
@[simp↓ high]
theorem evalDist_liftM_bind_guard {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) [DecidablePred p] :
    evalDist (do let x ← (liftM mx : OptionT m α); guard (p x)) =
      prEvent (p <$> mx) • Measure.dirac () :=
  evalDist_lift_bind_guard mx p

/-- A successful event of a wrapped computation is the event of present values that satisfy it
in the underlying computation. -/
theorem prEvent_mk {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m (Option α)) (p : α → Prop) :
    prEvent (p <$>ₘ OptionT.mk mx) = prEvent ((fun o ↦ o.elim False p) <$> mx) := by
  rw [prEvent_eq_run, OptionT.run_mk]

/-- Lifting into the optional monad adds no failure. -/
@[simp]
theorem prFail_lift {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type u} (mx : m α) :
    prFail (OptionT.lift mx) = prFail mx := by
  let : MeasurableSpace α := ⊤
  rw [prFail_eq_one_sub_evalDist_univ, prFail_eq_one_sub_evalDist_univ, OptionT.evalDist_lift]

/-- A monadic lift into the optional monad adds no failure. -/
@[simp]
theorem prFail_liftM {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type u} (mx : m α) :
    prFail (liftM mx : OptionT m α) = prFail mx :=
  prFail_lift mx

end OptionT
