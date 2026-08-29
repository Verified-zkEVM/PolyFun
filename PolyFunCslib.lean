/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFunCslib.Backend
public import PolyFunCslib.Nontriviality
public import PolyFunCslib.PPoly

/-!
# PolyFun's optional cslib-backed layer

This umbrella exposes the adapter between PolyFun computations and the
machine-grounded definitions maintained in `ToCslib`. It is a separate Lake
library and is intentionally absent from the dependency-light `PolyFun` root.
-/
