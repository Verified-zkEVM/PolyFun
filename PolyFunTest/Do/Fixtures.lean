/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Algebra.WP
public import PolyFun.Control.Monad.Support.WP
public import PolyFun.Control.Monad.Support.Instances
public import Mathlib.Data.ENat.Lattice

/-!
# Shared fixtures for the program-logic tests

Readings that several modules of `PolyFunTest/Do/` install, packaged as the library packages its
own: a construction, and a scope that installs it.

* `Det` is a fresh copy of `Id`, so that no global core instance competes with a locally
  installed one. `Det.mAlgOrderedENat` is its identity ordered algebra at the extended naturals,
  and `open scoped PolyFunTest.Det.ENatWP` installs the algebra and its core interpretation
  `MAlgOrdered.toWPMonad`. A module that installs another interpretation of `Det` installs the
  algebra alone, with `attribute [local instance] Det.mAlgOrderedENat`.
* `open scoped PolyFunTest.SetMDemonicWP` installs the demonic reading of `SetM`
  (`MonadAttach.toWPMonadDemonic`).
-/

@[expose] public section

open Std.WP

namespace PolyFunTest

/-- A deterministic monad with no global weakest-precondition instance. -/
def Det (α : Type) : Type := α

instance : Monad Det where
  pure a := a
  bind x f := f x

instance : LawfulMonad Det :=
  LawfulMonad.mk' Det (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

namespace Det

/-- The identity ordered algebra on `Det` at the extended naturals. -/
@[instance_reducible]
noncomputable def mAlgOrderedENat : MAlgOrdered Det ℕ∞ where
  μ x := x
  μ_pure _ := rfl
  μ_bind_mono _ _ h x := h x

namespace ENatWP

/-- The identity algebra on `Det`, installed by the scope. -/
noncomputable scoped instance instMAlgOrdered : MAlgOrdered Det ℕ∞ :=
  mAlgOrderedENat

/-- The core interpretation of the identity algebra, installed by the scope. -/
noncomputable scoped instance instWPMonad : WPMonad Det ℕ∞ EStack⟨⟩ :=
  MAlgOrdered.toWPMonad

end ENatWP

end Det

namespace SetMDemonicWP

/-- The demonic reading of `SetM`, installed by the scope. -/
scoped instance instWPMonad : WPMonad SetM Prop EStack⟨⟩ :=
  MonadAttach.toWPMonadDemonic

end SetMDemonicWP

end PolyFunTest
