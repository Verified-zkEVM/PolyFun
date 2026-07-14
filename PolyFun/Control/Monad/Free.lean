/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
module

public import Cslib.Foundations.Control.Monad.Free

/-!
# Generic free monad

This module re-exports cslib's canonical functor-generic free monad, `Cslib.FreeM`.
PolyFun does not extend this generic construction; its universe-preserving polynomial
free-monad API lives in [`PolyFun.PFunctor.Free.Basic`](../../PFunctor/Free/Basic.lean).
-/
