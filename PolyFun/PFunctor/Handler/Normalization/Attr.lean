/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Handler.Stateful

/-!
# Handler normalization attribute

This module declares the `handler_nf` simp attribute. The structural handler
rules are registered by `PolyFun.PFunctor.Handler.Normalization`.
-/

@[expose] public section

/-- Simp set for structural normalization of free and stateful handlers. -/
register_simp_attr handler_nf
