/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Algebra.WP
public import Std.Tactic.Do
public import Mathlib.Data.ENat.Lattice

/-!
# Ordered monad algebras on core's `vcgen`

An ordered monad algebra installed locally as a `WPMonad` drives core's `vcgen`: the generic
`Spec.pure` / `Spec.bind` rules apply, the derived `wp` is `MAlgOrdered.wp` by `rfl`, and
core's triple is PolyFun's. The base algebra below is the identity algebra on a deterministic
monad at the carrier `ℕ∞`, the shape a quantitative carrier takes; the `Prop` carrier is
exercised through the support layer instead. The monad is a fresh copy of `Id` so that no
global core instance competes with the locally installed one.
-/

public section

set_option mvcgen.warning false

open Std.Internal.Do

/-- A deterministic monad with no global weakest-precondition instance. -/
@[expose]
def Det (α : Type) : Type := α

instance : Monad Det where
  pure a := a
  bind x f := f x

instance : LawfulMonad Det :=
  LawfulMonad.mk' Det (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

/-- The identity ordered algebra on `Det` at the extended naturals. -/
noncomputable local instance instMAlgOrderedDetENat : MAlgOrdered Det ℕ∞ where
  μ x := x
  μ_pure _ := rfl
  μ_bind_mono _ _ h x := h x

/-- Its core interpretation, installed locally. -/
noncomputable local instance instWPMonadDetENat : WPMonad Det ℕ∞ EPost.Nil :=
  MAlgOrdered.toWPMonad

/-- Agreement with PolyFun's `wp` is definitional. -/
example (x : Det Nat) (post : Nat → ℕ∞) (epost : EPost.Nil) :
    wp x post epost = MAlgOrdered.wp x post :=
  rfl

/-- `vcgen` decomposes a `do` block through the locally installed algebra. -/
example (c : ℕ∞) :
    ⦃ c ⦄ (do let x ← pure 1; pure (x + 1) : Det Nat) ⦃ fun r => if r = 2 then c else ⊥ ⦄ := by
  vcgen
  change c ≤ _
  simp

/-- Core's triple through the derived interpretation is PolyFun's triple. -/
example (x : Det Nat) (pre : ℕ∞) (post : Nat → ℕ∞) :
    Triple x pre post Lean.Order.bot ↔ MAlgOrdered.Triple pre x post :=
  MAlgOrdered.toWP_triple_iff x pre post Lean.Order.bot
