/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Batteries.Control.LawfulMonadState

/-!
# `MonadState.set` as `MonadStateOf.set`

Batteries' `LawfulMonadState` API phrases its laws with `MonadStateOf.set` and `MonadState.get`
(`monadStateOf_get_eq_get` rewrites the namespaced `get`). `monadState_set_eq_monadStateOf_set`
rewrites the `MonadState` form of `set` into the `MonadStateOf` form those laws use.
-/

@[expose] public section

universe u v

/-- The `set` of the `MonadState` instance induced by `MonadStateOf` is `MonadStateOf.set`. -/
@[simp] theorem monadState_set_eq_monadStateOf_set {m : Type u → Type v} {σ : Type u}
    [MonadStateOf σ m] : (MonadState.set : σ → m PUnit) = MonadStateOf.set := rfl
