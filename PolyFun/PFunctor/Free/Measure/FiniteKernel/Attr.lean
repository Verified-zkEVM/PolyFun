/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# The `expected_cost` simp attribute

`PolyFun.PFunctor.Free.Measure.FiniteKernel` registers the equations for folding expected charges
and integrating continuations against explicit point masses and their mixtures.
-/

public section

/-- Simplification rules for expected-charge folds and atomic answer measures. -/
register_simp_attr expected_cost
