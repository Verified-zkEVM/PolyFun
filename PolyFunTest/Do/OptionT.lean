/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Do.Spec

/-!
# `OptionT` on core's `vcgen`

`failure`, `OptionT.lift`, and `guard` in `OptionT` over core's `Prop` reading of `Id` decompose
through the rules of `PolyFun.Control.Do.Spec`: a guard reports its failing branch through the
failure postcondition, which a precondition must rule out when that postcondition is `False`. The
module acknowledges the tactic's experimental status with `set_option experimental.vcgen true`;
`PolyFunTest.Do.Algebra` pins the diagnostic itself.
-/

public section

open Std.WP

set_option experimental.vcgen true

/-- Division that fails on a zero divisor. -/
def checkedDiv (a b : Nat) : OptionT Id Nat := do
  let q ← OptionT.lift (pure (a / b) : Id Nat)
  guard (b ≠ 0)
  pure q

/- With a nonzero divisor the guard passes, so the failure postcondition may be `False`. -/
example (a b : Nat) :
    ⦃ b ≠ 0 ⦄ checkedDiv a b ⦃ fun q => q = a / b; estack⟨fun _ => False⟩ ⦄ := by
  vcgen [checkedDiv]
  simp_all

/- A zero divisor reaches the failure postcondition. -/
example (a : Nat) :
    ⦃ True ⦄ checkedDiv a 0 ⦃ fun _ => False; estack⟨fun _ => True⟩ ⦄ := by
  vcgen [checkedDiv]
  simp_all

/- `failure` establishes exactly the failure postcondition. -/
example : ⦃ True ⦄ (failure : OptionT Id Nat) ⦃ fun _ => False; estack⟨fun _ => True⟩ ⦄ := by
  vcgen
