/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Do

/-!
# Fixture: global `@[spec]` rules of one reading

Two planted violations of the rule that a `@[spec]` rule tied to one reading is registered in the
scope of that reading: the demonic rule `PFunctor.FreeM.Spec.lift` registered globally, and an
angelic rule declared with a global `@[spec]` attribute. The module also makes registrations that
the rule allows, which the check must not report: the generic rule `PFunctor.FreeM.Spec.bind`, on
the allowlist, registered globally again, and the angelic rule registered in a scope. Only
`PolyFunTest.Policy.WP.Violations` imports this module.
-/

public section

namespace PolyFunTest.Policy.WP.Fixtures

open Std.WP

/- A planted violation: a demonic rule registered globally. -/
attribute [spec] PFunctor.FreeM.Spec.lift

/- A rule on the allowlist, registered globally, which the rule allows. -/
attribute [spec] PFunctor.FreeM.Spec.bind

section Angelic

open scoped PFunctor.FreeM.AngelicWP

/-- A planted violation: an angelic rule declared with a global `@[spec]` attribute. -/
@[spec]
theorem planted_lift_angelic {P : PFunctor.{0, 0}} (a : P.A) (Q : P.B a → Prop) (E : EStack⟨⟩) :
    Triple (PFunctor.FreeM.lift (P := P) a) (∃ b, Q b) Q E :=
  PFunctor.FreeM.Spec.lift_angelic a Q E

end Angelic

namespace PlantedScope

/- An angelic rule registered in a scope, which the rule allows. -/
attribute [scoped spec] PFunctor.FreeM.Spec.lift_angelic

end PlantedScope

end PolyFunTest.Policy.WP.Fixtures
