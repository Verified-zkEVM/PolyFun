/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Handler.Free

/-!
# Stateful monadic handlers

`PFunctor.Handler.Stateful m S q` is the canonical effectful Mealy interface
for a polynomial functor `q`: each query reads a state `S`, performs effects in
`m`, and returns both a dependent answer and the next state. It is a transparent
name for `Handler (StateT S m) q`, not a second machine representation.

The `run` operation interprets a finite `FreeM q` program through such a
handler. Reindexing by a free handler composes a finite query implementation
with an arbitrary effectful stateful handler; `run_reindex` is the corresponding
fusion law.

This interface does not turn `Responder` itself into a monadic dynamical
system. A pure responder exposes a complete `Section q` before any query is
selected and has separate pure `answer` and `next` maps. An arbitrary value of
`m (q.B a × S)` cannot be split into those maps, and moving `m` through the
dependent product of all query answers is not available for a general monad.
Thus `Responder` is exactly the `m := Id` specialization; effectful consumers
should use `Handler.Stateful` directly.

The primitive `run_pure` and `run_liftBind` equations need only `Monad m`.
Equations that identify derived `FreeM` operations, including `run_lift`,
`run_bind`, and the reindexing laws, require `LawfulMonad m`.
-/

@[expose] public section

universe u uA uA' uA'' v

namespace PFunctor
namespace Handler

namespace Stateful

variable {m : Type u → Type v} {S : Type u} [Monad m]
variable {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
variable {R : PFunctor.{uA'', u}}

/-- Lift a stateless monadic handler into a stateful handler that preserves the
state. -/
def lift (h : Handler m P) : Stateful m S P :=
  fun query => StateT.lift (h query)

/-- Interpret a finite free program through a stateful handler from an explicit
initial state. -/
def run (h : Stateful m S P) {α : Type u}
    (program : FreeM P α) (state : S) : m (α × S) :=
  (program.liftM h).run state

@[simp]
theorem run_pure (h : Stateful m S P) {α : Type u}
    (value : α) (state : S) :
    h.run (pure value : FreeM P α) state = pure (value, state) :=
  rfl

@[simp]
theorem run_lift [LawfulMonad m] (h : Stateful m S P)
    (query : P.A) (state : S) :
    h.run (FreeM.lift query) state = (h query).run state := by
  change (FreeM.liftM h (FreeM.lift query)).run state = _
  rw [FreeM.liftM_lift]

theorem run_liftBind (h : Stateful m S P)
    {α : Type u} (query : P.A) (next : P.B query → FreeM P α)
    (state : S) :
    h.run (FreeM.liftBind query next) state =
      (h query).run state >>= fun result => h.run (next result.1) result.2 := by
  change (FreeM.liftM h (FreeM.lift query >>= next)).run state =
    (h query).run state >>= fun result =>
      (FreeM.liftM h (next result.1)).run result.2
  rw [FreeM.liftM_lift_bind, StateT.run_bind]

/-- Executing a bind first executes the prefix, then continues from its value
and final state. -/
theorem run_bind [LawfulMonad m] (h : Stateful m S P)
    {α β : Type u} (program : FreeM P α) (next : α → FreeM P β)
    (state : S) :
    h.run (program >>= next) state =
      h.run program state >>= fun result => h.run (next result.1) result.2 := by
  rw [run, FreeM.liftM_bind, StateT.run_bind]
  rfl

/-- Reindex an effectful stateful handler contravariantly along a free handler.
Each source query runs its finite target program against `h`. -/
def reindex (implementation : Handler (FreeM Q) P)
    (h : Stateful m S Q) : Stateful m S P :=
  fun query state => h.run (implementation query) state

@[simp]
theorem reindex_apply (implementation : Handler (FreeM Q) P)
    (h : Stateful m S Q) (query : P.A) (state : S) :
    (h.reindex implementation query).run state =
      h.run (implementation query) state :=
  rfl

/-- Running a reindexed handler is the same as first translating the whole
program by the free handler and then running the target handler. -/
theorem run_reindex [LawfulMonad m]
    (implementation : Handler (FreeM Q) P) (h : Stateful m S Q)
    {α : Type u} (program : FreeM P α) (state : S) :
    (h.reindex implementation).run program state =
      h.run (program.liftM implementation) state := by
  exact congrArg (fun computation => computation.run state)
    (FreeM.liftM_comp program implementation h).symm

@[simp]
theorem reindex_id [LawfulMonad m] (h : Stateful m S P) :
    h.reindex (Handler.id P) = h := by
  funext query state
  change h.run (FreeM.lift query) state = (h query).run state
  exact run_lift h query state

/-- Stateful-handler reindexing is contravariantly functorial in categorical
free-handler composition order. -/
theorem reindex_comp [LawfulMonad m]
    (second : Handler (FreeM R) Q)
    (first : Handler (FreeM Q) P)
    (h : Stateful m S R) :
    (h.reindex second).reindex first = h.reindex (second.comp first) := by
  funext query state
  exact run_reindex second h (first query) state

end Stateful
end Handler
end PFunctor
