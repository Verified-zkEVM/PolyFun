/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Control.Monad.Hom
public import PolyFun.Control.Monad.Measure.ExceptT
public import PolyFun.Control.Monad.Measure.OptionT

/-!
# Bundled measure observations

`SemanticsVia` factors a computation through an internal monad and an external
measure-valued observer, with the observer's measurable-space choice explicit and its
subprobability mass certified. Observation need not preserve bind: a fixed environment, initial
state, or output projection may hide internal effects at the observation boundary.

The bundles select interpretations as data, without choosing a global semantics instance.
Optional and exceptional observations retain unsuccessful runs as missing successful-output mass.
-/

public section

open MeasureTheory

universe u v w

/-- Bundled subprobability semantics factoring a surface monad through an internal monad.

`interpret` is a monad morphism into the internal monad; `observe` need not be one, and takes
the output measurable space explicitly, since observing a `Measure α` requires one. Running the
internal computation may fix hidden state or discard auxiliary structure before the final
denotation is exposed. Failure or nontermination is represented by missing mass. -/
structure SemanticsVia (m : Type u → Type v) [Monad m] where
  /-- Internal semantic monad. -/
  Sem : Type u → Type w
  /-- Monad structure carried by the internal semantics. -/
  [instMonadSem : Monad Sem]
  /-- Interpret a surface computation in the internal semantic monad. -/
  interpret : m →ᵐ Sem
  /-- Observe successful outputs as a Mathlib measure. -/
  observe : {α : Type u} → [MeasurableSpace α] → Sem α → Measure α
  /-- Every observation has total mass at most one. -/
  observe_apply_univ_le_one : ∀ {α : Type u} [MeasurableSpace α] (mx : Sem α),
    observe mx Set.univ ≤ 1

instance {m : Type u → Type v} [Monad m] (sem : SemanticsVia m) : Monad sem.Sem :=
  sem.instMonadSem

namespace SemanticsVia

variable {m : Type u → Type v} [Monad m] {α : Type u}

/-- The visible measure denoted by a computation under a bundled semantics. -/
@[expose]
noncomputable def evalDist (sem : SemanticsVia m) [MeasurableSpace α]
    (mx : m α) : Measure α :=
  sem.observe (sem.interpret mx)

@[simp]
theorem evalDist_apply_univ_le_one (sem : SemanticsVia m) [MeasurableSpace α]
    (mx : m α) : sem.evalDist mx Set.univ ≤ 1 :=
  sem.observe_apply_univ_le_one (sem.interpret mx)

/-- Every bundled observation is a subprobability measure. -/
instance evalDist.instIsSubprobabilityMeasure (sem : SemanticsVia m)
    [MeasurableSpace α] (mx : m α) : IsSubprobabilityMeasure (sem.evalDist mx) :=
  ⟨sem.evalDist_apply_univ_le_one mx⟩

/-- Failure probability is the mass missing from the successful-output measure. -/
@[expose]
noncomputable def prFail (sem : SemanticsVia m) [MeasurableSpace α]
    (mx : m α) : ENNReal :=
  1 - sem.evalDist mx Set.univ

@[simp]
theorem prFail_le_one (sem : SemanticsVia m) [MeasurableSpace α]
    (mx : m α) : sem.prFail mx ≤ 1 :=
  tsub_le_self

/-- Package a global `EvalDistSemantics` instance as a local bundled semantics. -/
@[expose]
protected noncomputable def ofEvalDistSemantics (m : Type u → Type v) [Monad m]
    [EvalDistSemantics m] : SemanticsVia m where
  Sem := m
  instMonadSem := inferInstance
  interpret := MonadHom.id m
  observe := fun mx ↦ EvalDistSemantics.denote mx
  observe_apply_univ_le_one := fun mx ↦ EvalDistSemantics.apply_univ_le_one mx

@[simp]
theorem ofEvalDistSemantics_evalDist (mx : m α) [EvalDistSemantics m]
    [MeasurableSpace α] :
    (SemanticsVia.ofEvalDistSemantics m).evalDist mx = _root_.evalDist mx := by
  rfl

/-- Under lawful semantics, the bundled failure probability of a global semantics is its
failure probability `prFail`, in every measurable structure on the outputs. -/
theorem ofEvalDistSemantics_prFail [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MeasurableSpace α] (mx : m α) :
    (SemanticsVia.ofEvalDistSemantics m).prFail mx = _root_.prFail mx :=
  (prFail_eq_one_sub_evalDist_univ mx).symm

/-- Bundling a lossless denotation preserves its probability-measure certificate. -/
instance ofEvalDistSemantics.instIsProbabilityMeasure [EvalDistSemantics m]
    [MeasurableSpace α] (mx : m α) [IsProbabilityMeasure (_root_.evalDist mx)] :
    IsProbabilityMeasure ((SemanticsVia.ofEvalDistSemantics m).evalDist mx) :=
  inferInstanceAs (IsProbabilityMeasure (_root_.evalDist mx))

/-- Bundle the successful-output semantics of an optional computation. Its observation
measures present outputs and retains any underlying failure as missing mass. -/
@[expose]
protected noncomputable def optionT (m : Type u → Type v) [Monad m]
    [EvalDistSemantics m] : SemanticsVia (OptionT m) where
  Sem := OptionT m
  instMonadSem := inferInstance
  interpret := MonadHom.id (OptionT m)
  observe := fun mx ↦ (_root_.evalDist mx.run).comap some
  observe_apply_univ_le_one := fun mx ↦
    by simpa only [OptionT.evalDist_eq_comap_some] using
      _root_.evalDist_apply_univ_le_one mx

@[simp]
theorem optionT_evalDist (mx : OptionT m α) [EvalDistSemantics m]
    [MeasurableSpace α] :
    (SemanticsVia.optionT m).evalDist mx = (_root_.evalDist mx.run).dropNone := by
  exact (Measure.dropNone_eq_comap_some _).symm

/-- Optional bundling preserves a known successful-output probability certificate. -/
instance optionT.instIsProbabilityMeasure [EvalDistSemantics m]
    [MeasurableSpace α] (mx : OptionT m α) [IsProbabilityMeasure (_root_.evalDist mx)] :
    IsProbabilityMeasure ((SemanticsVia.optionT m).evalDist mx) := by
  rw [optionT_evalDist, Measure.dropNone_eq_comap_some, ← OptionT.evalDist_eq_comap_some]
  infer_instance

/-- Bundle the successful-output semantics of `ExceptT`. Errors remain observable
in the run measure and are discarded only by the `Except.ok` observation at this boundary. -/
@[expose]
protected noncomputable def exceptT (ε : Type u) [MeasurableSpace ε]
    (m : Type u → Type v) [Monad m] [EvalDistSemantics m] :
    SemanticsVia (ExceptT ε m) where
  Sem := ExceptT ε m
  instMonadSem := inferInstance
  interpret := MonadHom.id (ExceptT ε m)
  observe := fun mx ↦ (_root_.evalDist mx.run).comap Except.ok
  observe_apply_univ_le_one := fun mx ↦
    by simpa only [ExceptT.evalDist_eq_comap_ok] using
      _root_.evalDist_apply_univ_le_one mx

@[simp]
theorem exceptT_evalDist (ε : Type u) [MeasurableSpace ε]
    (mx : ExceptT ε m α) [EvalDistSemantics m] [MeasurableSpace α] :
    (SemanticsVia.exceptT ε m).evalDist mx = (_root_.evalDist mx.run).comap Except.ok := by
  rfl

/-- Exceptional bundling preserves a known successful-output probability certificate. -/
instance exceptT.instIsProbabilityMeasure {ε : Type u} [MeasurableSpace ε]
    [EvalDistSemantics m] [MeasurableSpace α] (mx : ExceptT ε m α)
    [IsProbabilityMeasure (_root_.evalDist mx)] :
    IsProbabilityMeasure ((SemanticsVia.exceptT ε m).evalDist mx) := by
  rw [exceptT_evalDist, ← ExceptT.evalDist_eq_comap_ok]
  infer_instance

end SemanticsVia
