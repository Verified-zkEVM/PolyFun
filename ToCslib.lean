/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToCslib.Algebra.Polynomial
public import ToCslib.Algebra.PolynomialGrowth
public import ToCslib.Control.ForIn
public import ToCslib.Control.Monad.HomTransport
public import ToCslib.Data.BitVec
public import ToCslib.Data.ENNReal.AddSupDistrib
public import ToCslib.Data.Fin.Cases
public import ToCslib.Data.Fin.Lattice
public import ToCslib.Data.Fin.MOfFn
public import ToCslib.Data.PFunctor.Free.Basic
public import ToCslib.Data.PFunctor.Free.Loops
public import ToCslib.MeasureTheory.Function.AEMeasurable
public import ToCslib.MeasureTheory.MeasurableSpace.Except
public import ToCslib.MeasureTheory.MeasurableSpace.Instances
public import ToCslib.MeasureTheory.MeasurableSpace.Option
public import ToCslib.MeasureTheory.MeasurableSpace.Sum
public import ToCslib.MeasureTheory.Measure.AEBind
public import ToCslib.MeasureTheory.Measure.Coupling
public import ToCslib.MeasureTheory.Measure.Coupling.Bind
public import ToCslib.MeasureTheory.Measure.Except
public import ToCslib.MeasureTheory.Measure.Option
public import ToCslib.MeasureTheory.Measure.Prop
public import ToCslib.MeasureTheory.Measure.Subprobability
public import ToCslib.Order.AddSupDistrib
public import ToCslib.Order.Admissible
public import ToCslib.Order.DiscreteOmegaCompletePartialOrder
public import ToCslib.Order.LeanOrder
public import ToCslib.Order.OmegaCompletePartialOrder
public import ToCslib.Order.PrefixRecursion
public import ToCslib.Order.SumOmegaCompletePartialOrder
public import ToCslib.Order.WithBotOmegaCompletePartialOrder
public import ToCslib.Probability.Kernel.Subprobability
public import ToCslib.Probability.UniformOn

/-!
# Extensions of the pinned cslib library

This library stages reusable extensions of the pinned cslib, Mathlib, and core APIs: free-monad
lemmas in cslib's simp normal form, transport of loop combinators along monad morphisms,
`PureForIn` instances, the bridge from Mathlib's complete lattices to core's `Lean.Order`,
least fixed points, admissible predicates, and discrete, lifted, and disjoint-sum carriers over
Mathlib's omega-complete partial orders, finite prefix recursion, direct compilation of
`Fin.cases`, monadic sequencing of `Fin`-indexed families, single-bit overwrites on bitvectors,
monotonicity of natural-number polynomial evaluation, polynomial growth against `2 ^ n`, and,
under `MeasureTheory` and `Probability`, measure and kernel lemmas in paths that mirror Mathlib's.
It imports core, cslib, and Mathlib only — never `PolyFun`, a concrete complexity backend, or any
downstream oracle or cryptographic semantics. `PolyFun` imports the modules it needs explicitly;
`ComplexityBackends` may do the same.
-/
