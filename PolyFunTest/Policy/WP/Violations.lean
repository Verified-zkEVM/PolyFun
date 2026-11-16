/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

import PolyFunTest.Policy.WP.Check
public import PolyFunTest.Policy.WP.Fixtures.GlobalInstance
public import PolyFunTest.Policy.WP.Fixtures.GlobalSpec

/-!
# The program-logic checks report planted violations

The fixtures under `PolyFunTest.Policy.WP.Fixtures` plant violations of the two rules that
`PolyFunTest.Policy.WP` checks, beside registrations that the rules allow. Run over the fixtures,
the checks report exactly the planted violations.
-/

/-- error: PolyFunTest.Policy.WP.Fixtures.GlobalInstance declares PolyFunTest.Policy.WP.Fixtures.plantedWPMonad, a global instance of Std.WP.WPMonad. Install an interpretation as a construction, and as a `scoped` instance where a scope should select it.
---
error: PolyFunTest.Policy.WP.Fixtures.GlobalInstance declares PolyFunTest.Policy.WP.Fixtures.plantedExtendedWPMonad, a global instance of PolyFunTest.Policy.WP.Fixtures.PlantedWPMonad. Install an interpretation as a construction, and as a `scoped` instance where a scope should select it.
-/
#guard_msgs in
#check_wp_instances PolyFunTest.Policy.WP.Fixtures

/-- error: PolyFunTest.Policy.WP.Fixtures.GlobalSpec registers PFunctor.FreeM.Spec.lift as a global `@[spec]` rule, and the rule is not on `specAllowlist`. Register a rule tied to one reading with `scoped spec` in the scope of that reading.
---
error: PolyFunTest.Policy.WP.Fixtures.GlobalSpec registers PolyFunTest.Policy.WP.Fixtures.planted_lift_angelic as a global `@[spec]` rule, and the rule is not on `specAllowlist`. Register a rule tied to one reading with `scoped spec` in the scope of that reading.
-/
#guard_msgs in
#check_wp_specs PolyFunTest.Policy.WP.Fixtures

/- The check tells the planted global registration of the demonic rule from its registration in
its reading's scope. -/
/--
info: PFunctor.FreeM.Spec.lift:
  `@[spec]` rule scoped in PFunctor.FreeM.DemonicWP, from PolyFun.PFunctor.Free.Do
  global `@[spec]` rule, from PolyFunTest.Policy.WP.Fixtures.GlobalSpec
-/
#guard_msgs in
#wp_registrations PFunctor.FreeM.Spec.lift
