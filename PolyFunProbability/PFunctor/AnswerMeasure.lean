/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Basic
public import Mathlib.Probability.UniformOn

/-!
# Answer measures for a polynomial interface

`PFunctor.AnswerMeasure` assigns a probability measure to the answers of each operation. A free
program over the interface then denotes a measure on its results (`PFunctor.FreeM.denote`).

The measurable structure on answer types is a separate instance family rather than a field,
following Mathlib's separation of `MeasurableSpace` from the measures it carries. Answer types
need not be discrete; the composition laws assume `DiscreteMeasurableSpace` where they need it.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe u uA

namespace PFunctor

/-- Per-operation answer measures for a polynomial interface. -/
class AnswerMeasure (P : PFunctor.{uA, u}) [∀ a, MeasurableSpace (P.B a)] where
  /-- The distribution of answers to an operation. -/
  toMeasure : (a : P.A) → Measure (P.B a)
  /-- Answering an operation is lossless. -/
  isProbabilityMeasure : ∀ a, IsProbabilityMeasure (toMeasure a)

attribute [instance] AnswerMeasure.isProbabilityMeasure

/-- Uniform answer measures for finite, nonempty answer types.

This is deliberately not an instance: measure semantics remain an explicit choice at each use
site, and are never inferred merely from finiteness. -/
@[reducible]
noncomputable def AnswerMeasure.uniformOfFiniteNonempty (P : PFunctor.{uA, u})
    [∀ a, Finite (P.B a)] [∀ a, Nonempty (P.B a)] [∀ a, MeasurableSpace (P.B a)] :
    P.AnswerMeasure where
  toMeasure _ := uniformOn Set.univ
  isProbabilityMeasure _ := inferInstance

end PFunctor
