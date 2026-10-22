/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunComplexitylib

/-!
# Axiom canaries for the headline bridges

Every headline result depends only on the standard axioms.
-/

/--
info: 'Cslib.OracleComp.hasQueryBounds_iff_isRollBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.OracleComp.hasQueryBounds_iff_isRollBound

/--
info: 'Cslib.DecisionTree.complexity_eq_queryComplexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.DecisionTree.complexity_eq_queryComplexity

/--
info: 'PFunctor.FreeM.queryComplexity_le_card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PFunctor.FreeM.queryComplexity_le_card

/-- info: 'Cslib.Communication.Protocol.run_eq_foldFreeM' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.Communication.Protocol.run_eq_foldFreeM

/-- info: 'Cslib.Stateful.eval_eq_runFree' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.Stateful.eval_eq_runFree

/--
info: 'PolyFunComplexitylib.instIsDistributivePolyTimeStepClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PolyFunComplexitylib.instIsDistributivePolyTimeStepClass

/--
info: 'PolyFunComplexitylib.instHasExactCompositionQuantitative' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PolyFunComplexitylib.instHasExactCompositionQuantitative

/--
info: 'PolyFunComplexitylib.isOraclePPTOn_iterate_pure_of_code' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PolyFunComplexitylib.isOraclePPTOn_iterate_pure_of_code
