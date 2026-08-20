/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Std.Tactic.Do
public import PolyFun.Control.Monad.Support

/-!
# Core `Std.Do` Enablement

This file is the *only* PolyFun root importing `Std.Tactic.Do`; every other use of
the core `Std.Do` weakest-precondition framework and the `mvcgen` tactic must go
through it (or through `PolyFun.PFunctor.Free.Do`), keeping the dependency on the
evolving upstream API quarantined.

It provides constructions — deliberately not instances — that transport core
`Std.Do` structure onto PolyFun's monads:

* `MonadHom.transportWP` / `MonadHom.transportWPMonad` pull a `WP`/`WPMonad`
  structure back along a monad morphism `F : m →ᵐ n`, so a monad that interprets
  into an `mvcgen`-ready stack inherits its predicate-transformer semantics.
* `MonadSupport.toWP` / `MonadSupport.toWPMonad` give any supported monad the
  demonic (almost-sure) interpretation at the `.pure` post shape: `wp x Q` holds
  when every possible output of `x` satisfies `Q`.

Downstream libraries choose where to register these (scoped or local); a global
instance here would clash with registrations on reducible unfoldings of the same
monads downstream.
-/

@[expose] public section

universe u v w

open Std.Do

namespace MonadHom

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  {ps : PostShape.{u}}

/-- Transport a core `Std.Do.WP` structure along a monad morphism: interpret
`x : m α` by the predicate transformer of its image `F x`. Not an instance —
downstream registers it at chosen carriers. -/
@[instance_reducible]
def transportWP (F : m →ᵐ n) [WP n ps] : WP m ps where
  wp x := WP.wp (F x)

/-- The transported structure is a `WPMonad` whenever the target is and the
source is a lawful monad. Not an instance. -/
@[instance_reducible]
def transportWPMonad (F : m →ᵐ n) [LawfulMonad m] [WPMonad n ps] : WPMonad m ps where
  toLawfulMonad := inferInstance
  toWP := F.transportWP
  wp_pure a := by
    change WP.wp (F (pure a)) = _
    rw [F.mmap_pure]
    exact WPMonad.wp_pure a
  wp_bind x f := by
    change WP.wp (F (x >>= f)) = _
    rw [F.mmap_bind]
    exact WPMonad.wp_bind (F x) fun a => F (f a)

end MonadHom

namespace MonadSupport

variable {m : Type u → Type v} [Monad m] [MonadSupport m]

theorem allOutputs_postCond_and {α : Type u} (x : m α)
    (Q₁ Q₂ : PostCond α .pure) :
    AllOutputs (fun a => ((Q₁.and Q₂).1 a).down) x ↔
      AllOutputs (fun a => (Q₁.1 a).down) x ∧ AllOutputs (fun a => (Q₂.1 a).down) x := by
  rw [← allOutputs_and]
  exact Iff.of_eq (congrArg (AllOutputs · x) (funext fun a => rfl))

/-- The demonic (almost-sure) `Std.Do.WP` structure of a supported monad at the
`.pure` post shape: `wp x Q` asserts that every possible output of `x` satisfies
the success postcondition. Not an instance. -/
@[instance_reducible]
def toWP : WP m .pure where
  wp x :=
    { trans := fun Q => ⌜AllOutputs (fun a => (Q.1 a).down) x⌝
      conjunctiveRaw := fun Q₁ Q₂ =>
        SPred.pure_congr (allOutputs_postCond_and x Q₁ Q₂) }

/-- The demonic interpretation is a `WPMonad` for any lawful supported monad.
Not an instance. -/
@[instance_reducible]
def toWPMonad [LawfulMonad m] : WPMonad m .pure where
  toLawfulMonad := inferInstance
  toWP := MonadSupport.toWP
  wp_pure a := by
    ext Q
    exact allOutputs_pure _ a
  wp_bind x f := by
    ext Q
    exact allOutputs_bind _ x f

end MonadSupport
