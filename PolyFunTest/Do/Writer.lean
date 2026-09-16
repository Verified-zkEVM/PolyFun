/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Do.Spec
public import PolyFun.Control.Monad.Support.WP
public import PolyFun.Control.Monad.Support.Instances
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# `WriterT` on core's `vcgen`

`WriterT.instWPMonad` lifts any core interpretation through Mathlib's writer transformer with a
log-indexed carrier, and the `@[spec]` rules of `PolyFun.Control.Do.Spec` let `vcgen` step
through `tell`, lifted base computations, and `run`. The log is a free monoid so that what was
written is visible as a list. Each `vcgen` call asserts the experimental-tactic diagnostic with
`#guard_msgs`, keeping `mvcgen.warning` enabled.
-/

public section

open Std.Internal.Do MonadAttach

/-- Log two numbers around a lifted computation. -/
def logTwo (a b : Nat) : WriterT (FreeMonoid Nat) Id Nat := do
  tell (FreeMonoid.of a)
  let s ← (pure (a + b) : Id Nat)
  tell (FreeMonoid.of b)
  pure s

/- The postcondition sees the log accumulated so far; `tell` extends it on the right. -/
/--
warning: The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it. Avoid using it in production projects.
-/
#guard_msgs in
example (a b : Nat) :
    ⦃ fun w => w = 1 ⦄ logTwo a b ⦃ fun r w => r = a + b ∧ w.toList = [a, b] ⦄ := by
  vcgen [logTwo]
  simp_all

/- `run` starts from the empty log. -/
/--
warning: The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it. Avoid using it in production projects.
-/
#guard_msgs in
example (a b : Nat) :
    ⦃ True ⦄ (logTwo a b).run ⦃ fun p => p.1 = a + b ∧ p.2.toList = [a, b] ⦄ := by
  vcgen [logTwo]
  simp_all

/-- The demonic interpretation of `SetM`, installed locally; `WriterT.instWPMonad` lifts it. -/
local instance instWPMonadSetMDemonic : WPMonad SetM Prop EPost.Nil :=
  toWPMonadDemonic

/-- A nondeterministic choice between an element and its successor. -/
def choose (x : Nat) : SetM Nat := ({x, x + 1} : Set Nat)

/-- Log the input, choose, log the choice. -/
def logChoice (x : Nat) : WriterT (FreeMonoid Nat) SetM Nat := do
  tell (FreeMonoid.of x)
  let y ← (choose x : SetM Nat)
  tell (FreeMonoid.of y)
  pure y

/- Over a nondeterministic base the log records the choice made; the nondeterministic leaf has no
registered specification and is discharged against the support. -/
/--
warning: The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it. Avoid using it in production projects.
-/
#guard_msgs in
example (x : Nat) :
    ⦃ fun w => w = 1 ⦄ logChoice x
      ⦃ fun r w => (r = x ∨ r = x + 1) ∧ w.toList = [x, r] ⦄ := by
  vcgen -errorOnMissingSpec [logChoice]
  change AllOutputs _ (choose x)
  intro y hy
  have hy' : y ∈ ({x, x + 1} : Set Nat) := SetM.canReturn_iff.mp hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy'
  simp_all
