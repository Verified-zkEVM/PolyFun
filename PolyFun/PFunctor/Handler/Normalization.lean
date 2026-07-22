/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Mathlib.Control.Monad.Writer
public import PolyFun.PFunctor.Handler.Normalization.Attr

/-!
# Handler normalization

The `handler_nf` simp set exposes the next structural layer of a free or
stateful handler computation. It unfolds `FreeM.liftM`,
`PFunctor.Handler.Stateful.run`, and the standard `StateT` and `WriterT`
run operations without importing a tactic framework.

Use `simp only [handler_nf]` when a proof needs a stable, explicit handler
normal form. Downstream libraries can extend the set with equations for their
own handler combinators.
-/

@[expose] public section

attribute [handler_nf]
  PFunctor.FreeM.liftM_pure
  PFunctor.FreeM.liftM_lift_bind
  PFunctor.FreeM.liftM_bind
  PFunctor.FreeM.liftM_lift
  PFunctor.Handler.Stateful.run_pure
  PFunctor.Handler.Stateful.run_lift
  PFunctor.Handler.Stateful.run_liftBind
  PFunctor.Handler.Stateful.run_bind
  PFunctor.Handler.Stateful.reindex_apply
  StateT.run_bind
  StateT.run_get
  StateT.run_set
  StateT.run_modifyGet
  StateT.run_pure
  StateT.run_monadLift
  WriterT.run_bind
  WriterT.run_map
  WriterT.run_liftM
  WriterT.run_pure
  WriterT.run_tell
