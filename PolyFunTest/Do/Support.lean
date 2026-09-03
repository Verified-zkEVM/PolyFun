/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Support.WP
public import Std.Tactic.Do

/-!
# Exact support on core's `vcgen`

The demonic interpretation of a monad with exact support, installed locally, lets `vcgen`
decompose `do` blocks whose leaves are then discharged against the support: `wp` is the
"always" judgment by `rfl`, core's triple is the guarded judgment, and a sound triple converts
back into a support fact through `allOutputs_of_wp`. The angelic interpretation is checked to
compute the "sometimes" judgment.
-/

public section

set_option mvcgen.warning false

open Std.Internal.Do MonadAttach

/-- The demonic interpretation of `SetM`, installed locally. -/
local instance instWPMonadSetMDemonic : WPMonad SetM Prop EPost.Nil :=
  toWPMonadDemonic

/-- A nondeterministic choice followed by a deterministic step. -/
def choose12 : SetM Nat := do
  let x ← (({1, 2} : Set Nat) : SetM Nat)
  pure (x + 1)

/-- `wp` is the "always" judgment. -/
example (x : SetM Nat) (post : Nat → Prop) (epost : EPost.Nil) :
    wp x post epost = AllOutputs post x :=
  rfl

/-- `vcgen` decomposes the bind chain; the nondeterministic leaf has no registered
specification, so its verification condition is left as a support fact. -/
theorem choose12_spec : ⦃ True ⦄ choose12 ⦃ fun r => r = 2 ∨ r = 3 ⦄ := by
  vcgen -errorOnMissingSpec [choose12]
  intro a ha
  have ha' : a ∈ ({1, 2} : Set Nat) := SetM.canReturn_iff.mp ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
  change AllOutputs (fun r => r = 2 ∨ r = 3) (pure (a + 1) : SetM Nat)
  rw [allOutputs_pure]
  omega

/-- A sound triple converts back into a support fact. -/
example : AllOutputs (fun r => r = 2 ∨ r = 3) choose12 := by
  have := toWPMonadDemonic_lawfulWPMonadAttach (m := SetM)
  refine allOutputs_of_wp ?_
  intro _
  simpa only [Lean.Order.ofProp_prop_eq] using choose12_spec.le_wp trivial

/-- The demonic interpretation is conjunctive. -/
example (x : SetM Nat) :
    @WPConjunctive (SetM Nat) Nat Prop EPost.Nil _ _ (instWPMonadSetMDemonic.toWP Nat) x :=
  toWPMonadDemonic_wpConjunctive x

/-- The angelic interpretation computes the "sometimes" judgment. -/
example (x : SetM Nat) (post : Nat → Prop) (epost : EPost.Nil) :
    ((toWPMonadAngelic (m := SetM)).toWP Nat).wp x post epost = SomeOutput post x :=
  rfl
