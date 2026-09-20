/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToCslib.Algebra.Polynomial
public import ToCslib.Control.ForIn
public import ToCslib.Control.Monad.HomTransport
public import ToCslib.Data.BitVec
public import ToCslib.Data.PFunctor.Free.Basic
public import ToCslib.Data.PFunctor.Free.Loops
public import ToCslib.Order.LeanOrder

/-!
# Extensions of the pinned cslib library

This library stages reusable extensions of the pinned cslib, Mathlib, and core APIs: free-monad
lemmas in cslib's simp normal form, transport of loop combinators along monad morphisms,
`PureForIn` instances, the bridge from Mathlib's complete lattices to core's `Lean.Order`,
single-bit overwrites on bitvectors, and monotonicity of natural-number polynomial evaluation.
It imports core, cslib, and Mathlib only — never `PolyFun`, a concrete complexity backend, or any
downstream oracle or cryptographic semantics. `PolyFun` imports the modules it needs explicitly;
`ComplexityBackends` may do the same.
-/
