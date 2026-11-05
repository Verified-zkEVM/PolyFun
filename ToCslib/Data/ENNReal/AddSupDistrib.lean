/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Order.AddSupDistrib
public import Mathlib.Basic.ENNReal.Operations

/-!
# Addition distributes over suprema in `ℝ≥0∞`

The `AddSupDistrib ℝ≥0∞` instance, from `ENNReal.add_sSup`. It lives in its own module so that the
worst-case costs of PolyFun's core stay free of the reals: import it to take costs in `ℝ≥0∞`.
-/

public section

open scoped ENNReal

instance ENNReal.instAddSupDistrib : AddSupDistrib ℝ≥0∞ where
  add_sSup_le _ _ hs := (ENNReal.add_sSup hs).le
