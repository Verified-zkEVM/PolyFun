/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Elias Judin
-/

module

public import ToCslib.Computability.BitEncoding
public import ToCslib.Computability.PolyTime
public import ToCslib.Computability.SingleTape.BasicMachines
public import ToCslib.Computability.SingleTape.Counting
public import ToCslib.Computability.SingleTape.Snoc
public import ToCslib.Control.ForIn
public import ToCslib.Control.Monad.HomTransport
public import ToCslib.Data.BitVec
public import ToCslib.Data.PFunctor.Free.Basic
public import ToCslib.Data.PFunctor.Free.Loops
public import ToCslib.Order.LeanOrder

/-!
# Extensions of the pinned cslib library

This library stages reusable extensions of the pinned cslib API: free-monad lemmas in cslib's
simp normal form, transport of loop combinators along monad morphisms, `PureForIn` instances,
the bridge from Mathlib's complete lattices to core's `Lean.Order`, and local machine and
complexity theory (encoded polynomial-time families, machine constructions, and counting
separation). It imports cslib and Mathlib only — never PolyFun's realizability theory or any
downstream oracle or cryptographic semantics. `PolyFun` imports the free-monad slice
explicitly; optional backend libraries import the machine modules without adding concrete
machine extensions to the generic `PolyFun` umbrella.
-/
