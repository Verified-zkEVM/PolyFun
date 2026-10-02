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

`WriterT.MonoidWP.instWPMonad` lifts a core interpretation through Mathlib's writer transformer with
a log-indexed carrier. The `@[spec]` rules of `PolyFun.Control.Do.Spec` let `vcgen` step through
`tell`, lifted base computations, and `run`. The log is a free monoid so that what was written is
visible as a list. The module acknowledges the tactic's experimental status with `set_option
experimental.vcgen true`; `PolyFunTest.Do.Algebra` pins the diagnostic itself.
-/

public section

open Std.WP MonadAttach

set_option experimental.vcgen true

/- Importing the bridge leaves the writer interpretation unselected. -/
example : True := by
  fail_if_success
    have := inferInstanceAs
      (WPMonad (WriterT (FreeMonoid Nat) Id) (FreeMonoid Nat → Prop) EStack⟨⟩)
  trivial

open scoped WriterT.MonoidWP

/-- Log two numbers around a lifted computation. -/
def logTwo (a b : Nat) : WriterT (FreeMonoid Nat) Id Nat := do
  tell (FreeMonoid.of a)
  let s ← (pure (a + b) : Id Nat)
  tell (FreeMonoid.of b)
  pure s

/- The postcondition sees the log accumulated so far; `tell` extends it on the right. -/
example (a b : Nat) :
    ⦃ fun w => w = 1 ⦄ logTwo a b ⦃ fun r w => r = a + b ∧ w.toList = [a, b] ⦄ := by
  vcgen [logTwo]
  simp_all

/- `run` starts from the empty log. -/
example (a b : Nat) :
    ⦃ True ⦄ (logTwo a b).run ⦃ fun p => p.1 = a + b ∧ p.2.toList = [a, b] ⦄ := by
  vcgen [logTwo]
  simp_all

/-- The demonic interpretation of `SetM`, lifted by the scoped writer interpretation. -/
local instance instWPMonadSetMDemonic : WPMonad SetM Prop EStack⟨⟩ :=
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
example (x : Nat) :
    ⦃ fun w => w = 1 ⦄ logChoice x
      ⦃ fun r w => (r = x ∨ r = x + 1) ∧ w.toList = [x, r] ⦄ := by
  vcgen -errorOnMissingSpec [logChoice]
  change AllOutputs _ (choose x)
  intro y hy
  have hy' : y ∈ ({x, x + 1} : Set Nat) := SetM.canReturn_iff.mp hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy'
  simp_all
