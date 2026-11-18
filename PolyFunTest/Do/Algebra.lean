/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Do.Fixtures

/-!
# Ordered monad algebras on core's `vcgen`

An ordered monad algebra installed as a `WPMonad` drives core's `vcgen`: the generic
`Spec.pure` / `Spec.bind` rules apply, the derived `wp` is the algebra of the mapped program by
`rfl`, and core's triple unfolds to Mathlib's order on the carrier. The base algebra below is
the identity algebra on the deterministic monad `Det` of `PolyFunTest.Do.Fixtures` at the carrier
`ℕ∞`, the shape a quantitative carrier takes; the `Prop` carrier is exercised through the support
layer instead. The monad is a fresh copy of `Id` so that no global core instance competes with
the one that its scope installs. The algebra also preserves binary meets, so its interpretation
is conjunctive (`MAlgOrdered.wpConjunctive_toWP`) and core's `Triple.and` applies.
The single `vcgen` call pins the experimental-tactic diagnostic with `#guard_msgs`; the other
`PolyFunTest/Do/` modules acknowledge it with `set_option experimental.vcgen true` instead.
-/

public section

open Std.WP PolyFunTest
open scoped PolyFunTest.Det.ENatWP

/-- The derived `wp` is the algebra of the mapped program, definitionally. -/
example (x : Det Nat) (post : Nat → ℕ∞) (epost : EStack⟨⟩) :
    wp x post epost = MAlgOrdered.μ (x >>= fun a => pure (post a)) :=
  rfl

/- `vcgen` decomposes a `do` block through the installed algebra. -/
/--
warning: The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it; `set_option experimental.vcgen true` acknowledges its experimental status and silences this warning.
-/
#guard_msgs in
example (c : ℕ∞) :
    ⦃ c ⦄ (do let x ← pure 1; pure (x + 1) : Det Nat) ⦃ fun r => if r = 2 then c else ⊥ ⦄ := by
  vcgen
  change c ≤ _
  simp

/-- Core's triple through the derived interpretation is Mathlib's order on the carrier. -/
example (x : Det Nat) (pre : ℕ∞) (post : Nat → ℕ∞) :
    Triple x pre post Lean.Order.bot ↔ pre ≤ MAlgOrdered.μ (x >>= fun a => pure (post a)) :=
  MAlgOrdered.toWP_triple_iff x pre post Lean.Order.bot

/-- The identity algebra preserves binary meets, so its interpretation is conjunctive at every
program, and core's `Triple.and` combines two triples about one program. -/
example (x : Det Nat) (a b : ℕ∞) (p q : Nat → ℕ∞) (h₁ : ⦃ a ⦄ x ⦃ p ⦄) (h₂ : ⦃ b ⦄ x ⦃ q ⦄) :
    Triple x (Lean.Order.meet a b) (Lean.Order.meet p q)
      (Lean.Order.meet Lean.Order.bot Lean.Order.bot) :=
  haveI := MAlgOrdered.wpConjunctive_toWP x fun _ _ => le_rfl
  Triple.and h₁ h₂
