/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.ExactWP

/-!
# Fixture: global interpretation instances

Two planted violations of the rule that no module declares a global instance of an interpretation
class: a global `WPMonad` instance, and a global instance of a class that extends `WPMonad`. The
module also declares instances that the rule allows, which the check must not report: the
projection of that class to `WPMonad`, a scoped `WPMonad` instance, and a global `ExactWPMonad`
fact. Only `PolyFunTest.Policy.WP.Violations` imports this module.
-/

public section

namespace PolyFunTest.Policy.WP.Fixtures

open Std.WP

/-- A planted violation: a global `WPMonad` instance. -/
instance plantedWPMonad : WPMonad (StateT Nat Id) (Nat → Prop) EStack⟨⟩ := inferInstance

/-- A class that extends `WPMonad`. -/
class PlantedWPMonad (m : Type → Type) (Pred EPred : outParam Type) [Monad m] [Assertion Pred]
    [Assertion EPred] extends WPMonad m Pred EPred

/-- A planted violation: a global instance of a class that extends `WPMonad`. -/
instance plantedExtendedWPMonad : PlantedWPMonad (StateT Nat Id) (Nat → Prop) EStack⟨⟩ := {}

namespace PlantedScope

/-- A scoped `WPMonad` instance, which the rule allows. -/
scoped instance plantedScopedWPMonad : WPMonad (ReaderT Nat Id) (Nat → Prop) EStack⟨⟩ :=
  inferInstance

end PlantedScope

/-- A global `Prop`-valued fact about an interpretation, which the rule allows. -/
instance plantedExactWPMonad : ExactWPMonad (StateT Nat Id) (Nat → Prop) EStack⟨⟩ :=
  inferInstance

end PolyFunTest.Policy.WP.Fixtures
