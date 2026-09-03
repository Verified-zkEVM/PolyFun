/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support.WP
public import PolyFun.Control.Monad.Support.Instances
public import PolyFun.Control.Do.Spec

/-!
# `try … catch` on core's `vcgen`

`try … catch` elaborates to `MonadExcept.tryCatch`, whose lifting specification core states as
`Spec.tryCatch_MonadExcept` without registering it; `PolyFun.Control.Do.Spec` registers it, and
these examples pin that a `try … catch` block over the demonic interpretation of `SetM`, lifted
to `ExceptT` by core's transformer instance, decomposes into verification conditions instead of
stopping with "no spec found". The uncaught exception of the raw program is reported through an
honest exception postcondition. Each `vcgen` call asserts the experimental-tactic diagnostic
with `#guard_msgs`, keeping `mvcgen.warning` enabled.
-/

public section

open Std.Internal.Do MonadAttach

/-- The demonic interpretation of `SetM`, installed locally; core lifts it to `ExceptT`. -/
local instance instWPMonadSetMDemonic : WPMonad SetM Prop EPost.Nil :=
  toWPMonadDemonic

/-- Division that throws on a zero divisor. -/
def safeDiv (a b : Nat) : ExceptT String SetM Nat := do
  if b = 0 then throw "division by zero"
  pure (a / b)

/-- Recovery from the exception with a default result. -/
def divOrDefault (a b : Nat) : ExceptT String SetM Nat := do
  try safeDiv a b catch _ => pure 0

/- The raw program's exception is reported through the exception postcondition. -/
/--
warning: The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it. Avoid using it in production projects.
-/
#guard_msgs in
example (a b : Nat) :
    ⦃ True ⦄ safeDiv a b
      ⦃ fun r => b ≠ 0 ∧ r = a / b; ⟨fun e => b = 0 ∧ e = "division by zero", ⟨⟩⟩ ⦄ := by
  vcgen [safeDiv]
  all_goals simp_all

/- `try … catch` decomposes through the registered `Spec.tryCatch_MonadExcept`: one condition
per branch of the caught program. -/
/--
warning: The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it. Avoid using it in production projects.
-/
#guard_msgs in
example (a b : Nat) : ⦃ True ⦄ divOrDefault a b ⦃ fun r => r = a / b ∨ r = 0 ⦄ := by
  vcgen [divOrDefault, safeDiv]
  all_goals simp
