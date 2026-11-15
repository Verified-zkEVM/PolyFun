/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Measure
public import PolyFun.Control.Monad.Measure.Deterministic

/-!
# Partial results through the optional semantics

`DomainResult ε` is not a monad: its bind takes a continuous continuation. A partial result
reaches the generic measure semantics through `toOption` and the deterministic semantics of
`Option`. That semantics keeps a value and sends bottom and every error to failure.

A result `d` then denotes the values of its Dirac measure (`DomainResult.evalDist_toOption`).
Its failure probability is the failure mass of that measure (`DomainResult.prFail_toOption`).
The semantics does not distinguish bottom from an error; the measure on results does.
-/

public section

open MeasureTheory

universe u

namespace DomainResult

variable {ε : Type*} {α : Type u} [MeasurableSpace α]

/-- The optional semantics of a partial result is the measure of the values of its Dirac
measure. -/
@[simp]
theorem evalDist_toOption (d : DomainResult ε α) :
    evalDist d.toOption = success (Measure.dirac d) := by
  induction d using inductionOn <;> simp

/-- Under the optional semantics, a partial result fails with the failure mass of its Dirac
measure: zero at a value, and one at bottom or an error. -/
theorem prFail_toOption (d : DomainResult ε α) :
    prFail d.toOption = failureMass (Measure.dirac d) := by
  rw [prFail_eq_defect, evalDist_toOption, defect_success_eq_failureMass]

end DomainResult
