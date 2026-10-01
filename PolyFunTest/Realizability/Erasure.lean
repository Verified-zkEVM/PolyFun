/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Erasure
public import PolyFunTest.Realizability.QuantitativeBoundedClosure

/-!
# Arbitrary recosting does not preserve work bounds

An immediate return charges initialization and final readout even though its trace is empty.
Changing each local charge from zero to one invalidates the original zero-work bound.
-/

public section

open PFunctor PFunctor.DynSystem.DynComputation
open PFunctor.QuantitativeBoundedClosureTest

example : ¬(returnRealization.recost (fun _ _ _ _ _ _ _ ↦ 1)).RunsWithin
    (fun _ ↦ (0 : ExecutionCost)) := by
  intro h
  have hc := (h.cost_le PUnit.unit (.nil _)).1
  change 1 + 0 + 0 + 1 ≤ 0 at hc
  omega

example (input : PUnit) :
    (returnRealization.recost (fun _ _ _ _ _ _ _ ↦ 1)).machine.denote input =
      returnRealization.machine.denote input := rfl
