/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Discrete measurable-space instances for bit vectors

Mathlib equips a selection of standard countable types with the discrete σ-algebra `⊤` in
`Mathlib.MeasureTheory.MeasurableSpace.Instances` — `Bool`, `ℕ`, `ℤ`, `ℚ`, `Fin n`, `ZMod n`
among them. `BitVec n` is not on that list, although sampling statements over fixed-width words
are phrased over it.

The instances follow the upstream file's style, so this compatibility layer can be removed if
Mathlib gains the same instances.

## Why `⊤` rather than a blanket instance

There is deliberately no `[Finite α] → MeasurableSpace α := ⊤` instance. It would overlap the
concrete instances above and other selected σ-algebras on finite types: finiteness alone does not
choose a measurable space. Once a space is selected, Mathlib derives `DiscreteMeasurableSpace α`
from `Countable α` and `MeasurableSingletonClass α`. Discrete measurable structure is opted into
per type, exactly as upstream does it. Continuous types retain their canonical Borel structures.
-/

public section

-- upstream candidate

/-- `BitVec n` is finite, hence countable.

Mathlib derives `Fintype (BitVec n)` from `FinEnum (BitVec n)` (`Mathlib.Data.FinEnum`), which this
module deliberately does not import; the `Finite` instance is restated here so that this module
stands alone: without `Countable` in scope,
`MeasurableSingletonClass.toDiscreteMeasurableSpace` does not fire, and the discrete structure
below fails to propagate to products and function types, from which sampling statements over
words are built. `Finite` is `Prop`-valued, so this cannot conflict with any `Fintype`
instance. -/
instance BitVec.instFinite (n : ℕ) : Finite (BitVec n) :=
  Finite.of_injective BitVec.toFin fun _ _ h => BitVec.toFin_inj.mp h

instance BitVec.instMeasurableSpace (n : ℕ) : MeasurableSpace (BitVec n) := ⊤

instance BitVec.instMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (BitVec n) := ⟨fun _ => trivial⟩

instance BitVec.instDiscreteMeasurableSpace (n : ℕ) :
    DiscreteMeasurableSpace (BitVec n) := inferInstance
