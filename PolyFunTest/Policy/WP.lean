/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

import PolyFunTest.Policy.WP.Check
public import ComplexityBackends
public import PolyFun
public import ToCslib

/-!
# PolyFun's libraries follow the core program-logic rules

The production libraries are imported with no scope open, and the commands of
`PolyFunTest.Policy.WP.Check` read the instances and `@[spec]` rules that their modules register.
No module declares a global interpretation instance, every global `@[spec]` rule is on the
allowlist, and every rule on the allowlist is registered globally. `scripts/check-modules.sh`
checks the other two rules, on imports and on `vcgen`.
-/

/-- info: no global instance of an interpretation class -/
#guard_msgs in
#check_wp_instances PolyFun ToCslib ComplexityBackends

/-- info: 24 global `@[spec]` registrations, all of rules on `specAllowlist` -/
#guard_msgs in
#check_wp_specs PolyFun ToCslib ComplexityBackends

/-- info: every rule on `specAllowlist` is registered globally -/
#guard_msgs in
#check_wp_allowlist PolyFun ToCslib ComplexityBackends

/-! ## Readings register their rules in their scopes -/

/--
info: PFunctor.FreeM.DemonicWP.instWPMonad:
  instance scoped in PFunctor.FreeM.DemonicWP, from PolyFun.PFunctor.Free.Do
-/
#guard_msgs in
#wp_registrations PFunctor.FreeM.DemonicWP.instWPMonad

/--
info: PFunctor.FreeM.Spec.lift:
  `@[spec]` rule scoped in PFunctor.FreeM.DemonicWP, from PolyFun.PFunctor.Free.Do
-/
#guard_msgs in
#wp_registrations PFunctor.FreeM.Spec.lift

/--
info: PFunctor.FreeM.Spec.liftBind:
  `@[spec]` rule scoped in PFunctor.FreeM.DemonicWP, from PolyFun.PFunctor.Free.Do
-/
#guard_msgs in
#wp_registrations PFunctor.FreeM.Spec.liftBind

/--
info: PFunctor.FreeM.Spec.lift_angelic:
  `@[spec]` rule scoped in PFunctor.FreeM.AngelicWP, from PolyFun.PFunctor.Free.Do
-/
#guard_msgs in
#wp_registrations PFunctor.FreeM.Spec.lift_angelic

/--
info: Std.WP.Spec.tell_WriterT:
  `@[spec]` rule scoped in WriterT.MonoidWP, from PolyFun.Control.Monad.WriterT.WP
-/
#guard_msgs in
#wp_registrations Std.WP.Spec.tell_WriterT

/--
info: Std.WP.Spec.tell_WriterT_append:
  `@[spec]` rule scoped in WriterT.AppendWP, from PolyFun.Control.Monad.WriterT.WP
-/
#guard_msgs in
#wp_registrations Std.WP.Spec.tell_WriterT_append

/-! ## Generic rules are global -/

/--
info: PFunctor.FreeM.Spec.bind:
  global `@[spec]` rule, from PolyFun.PFunctor.Free.Do
-/
#guard_msgs in
#wp_registrations PFunctor.FreeM.Spec.bind

/- Core states `Spec.tryCatch_MonadExcept`, and PolyFun registers it. -/
/--
info: Std.WP.Spec.tryCatch_MonadExcept:
  global `@[spec]` rule, from PolyFun.Control.Do.Spec
-/
#guard_msgs in
#wp_registrations Std.WP.Spec.tryCatch_MonadExcept
