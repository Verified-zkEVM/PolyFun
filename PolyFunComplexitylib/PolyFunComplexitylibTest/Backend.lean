/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunComplexitylib.Adequacy.Iterate
import PolyFunComplexitylib.Backend.SingleTape

/-!
# The polynomial-time step class and its quantitative backend

Instance canaries for every structural mixin PolyFun's realizability closure uses, the exact
composition-cost equation, and the universe signatures of the backend.
-/

open PFunctor PolyFunComplexitylib Turing.MultiTapeTM

/-- Products are available at every universe. -/
example : polyTimeStepClass.{3}.HasProd := inferInstance

/-- Sums, options and distributivity are available at universe `0`. -/
example : polyTimeStepClass.{0}.HasSum := inferInstance
example : polyTimeStepClass.{0}.HasOption := inferInstance
example : polyTimeStepClass.{0}.IsDistributive := inferInstance

/-- Admissibility is complexitylib's polynomial-time predicate. -/
example {A B : Type} (ea : A ↪ List Bool) (eb : B ↪ List Bool) (f : A → B) :
    polyTimeStepClass.Hom ea eb f = ComputableTidilyInPolyTime f ea eb := rfl

/-- The composition cost is exactly the two charges plus the linear connection charge. -/
example {A B D : Type} {ea : A ↪ List Bool} {eb : B ↪ List Bool} {ed : D ↪ List Bool}
    {f : A → B} {g : B → D} (cf : quantitative.Realizer ea eb f)
    (cg : quantitative.Realizer eb ed g) (a : A) :
    quantitative.cost (quantitative.compose cf cg) a =
      quantitative.cost cf a + quantitative.cost cg (f a) + quantitative.composeOverhead cf cg a :=
  QuantitativeStepClass.HasExactComposition.cost_compose_eq cf cg a

/-- Every charge is backed by a run of the realizer's own machine. -/
example {A B : Type} {ea : A ↪ List Bool} {eb : B ↪ List Bool} {f : A → B}
    (c : quantitative.Realizer ea eb f) (a : A) :
    c.machine.ComputesTidilyInTimeAndSpace (ea a) (eb (f a)) (quantitative.cost c a) (c.space a) :=
  quantitative_adequate c a

set_option pp.universes true in
/--
info: polyTimeStepClass.{u_1} : StepClass.{u_1, u_1}
-/
#guard_msgs in
#check @polyTimeStepClass

set_option pp.universes true in
/--
info: quantitative.{u_1} : QuantitativeStepClass.{u_1, u_1, max 1 u_1} polyTimeStepClass.{u_1}
-/
#guard_msgs in
#check @quantitative
