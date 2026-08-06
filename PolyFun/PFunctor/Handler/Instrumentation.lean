/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Mathlib.Control.Monad.Writer
public import PolyFun.PFunctor.Handler

/-!
# Instrumenting Monadic Handlers

This module provides effect-generic constructions for polynomial-functor
handlers. `liftTarget` changes the target monad through `MonadLiftT`, while
`preInsert` and `postInsert` add a side effect before or after each handled
operation. The writer specializations record response-independent or
response-dependent traces without depending on any oracle-specific API.
-/

public section

universe u v w uA

namespace PFunctor
namespace Handler

variable {P : PFunctor.{uA, u}}
variable {m : Type u → Type v} {n : Type u → Type w}

/-- Lift every operation of a handler into a new target monad. -/
-- Keep this structural adapter transparent: dependent handler result types
-- frequently need its pointwise reduction during elaboration.
@[expose] def liftTarget (n : Type u → Type w) [MonadLiftT m n]
    (handler : Handler m P) : Handler n P :=
  fun operation => liftM (handler operation)

@[simp]
theorem liftTarget_apply (n : Type u → Type w) [MonadLiftT m n]
    (handler : Handler m P) (operation : P.A) :
    handler.liftTarget n operation = liftM (handler operation) :=
  by rfl

/-- Lifting a handler to its current target has no effect. -/
@[simp]
theorem liftTarget_self (handler : Handler m P) :
    handler.liftTarget m = handler :=
  by rfl

/-- Run an effect before handling each operation.

The inserted effect is unconditional: it still runs when the underlying
handler subsequently fails. Its result is discarded. -/
def preInsert [Monad n] [MonadLiftT m n] {α : Type u}
    (handler : Handler m P) (before : P.A → n α) : Handler n P :=
  fun operation => before operation *> liftM (handler operation)

@[simp, grind =]
theorem preInsert_apply [Monad n] [MonadLiftT m n] {α : Type u}
    (handler : Handler m P) (before : P.A → n α) (operation : P.A) :
    handler.preInsert before operation =
      before operation *> liftM (handler operation) :=
  by rfl

/-- Run an effect after handling each operation.

The inserted effect may depend on the response and is skipped if the
underlying handler fails. Its result is discarded. -/
def postInsert [Monad n] [MonadLiftT m n] {α : Type u}
    (handler : Handler m P) (after : (operation : P.A) → P.B operation → n α) :
    Handler n P :=
  fun operation => do
    let response ← liftM (handler operation)
    let _ ← after operation response
    return response

@[simp, grind =]
theorem postInsert_apply [Monad n] [MonadLiftT m n] {α : Type u}
    (handler : Handler m P) (after : (operation : P.A) → P.B operation → n α)
    (operation : P.A) :
    handler.postInsert after operation = do
      let response ← liftM (handler operation)
      let _ ← after operation response
      return response :=
  by rfl

/-! ## Writer traces -/

variable [Monad m]

/-- Record a response-independent trace before each handled operation. -/
def withTraceBefore {ω : Type u} [Monoid ω]
    (handler : Handler m P) (trace : P.A → ω) : Handler (WriterT ω m) P :=
  handler.preInsert fun operation => tell (trace operation)

@[simp, grind =]
theorem withTraceBefore_apply {ω : Type u} [Monoid ω]
    (handler : Handler m P) (trace : P.A → ω) (operation : P.A) :
    handler.withTraceBefore trace operation = (do
      tell (trace operation)
      handler operation) :=
  by rfl

/-- Response-independent writer tracing is before-insertion of `tell`. -/
theorem withTraceBefore_eq_preInsert {ω : Type u} [Monoid ω]
    (handler : Handler m P) (trace : P.A → ω) :
    handler.withTraceBefore trace =
      handler.preInsert (fun operation => tell (trace operation)) := by
  rfl

/-- Record a response-dependent trace after each handled operation. -/
def withTrace {ω : Type u} [Monoid ω]
    (handler : Handler m P) (trace : (operation : P.A) → P.B operation → ω) :
    Handler (WriterT ω m) P :=
  handler.postInsert fun operation response => tell (trace operation response)

@[simp, grind =]
theorem withTrace_apply {ω : Type u} [Monoid ω]
    (handler : Handler m P) (trace : (operation : P.A) → P.B operation → ω)
    (operation : P.A) :
    handler.withTrace trace operation = do
      let response ← handler operation
      tell (trace operation response)
      return response :=
  by rfl

/-- Response-dependent writer tracing is after-insertion of `tell`. -/
theorem withTrace_eq_postInsert {ω : Type u} [Monoid ω]
    (handler : Handler m P) (trace : (operation : P.A) → P.B operation → ω) :
    handler.withTrace trace =
      handler.postInsert (fun operation response => tell (trace operation response)) := by
  rfl

/-- Append-flavoured response-independent tracing. -/
def withTraceAppendBefore {ω : Type u} [EmptyCollection ω] [Append ω]
    (handler : Handler m P) (trace : P.A → ω) : Handler (WriterT ω m) P :=
  handler.preInsert fun operation => tell (trace operation)

@[simp, grind =]
theorem withTraceAppendBefore_apply {ω : Type u} [EmptyCollection ω] [Append ω]
    (handler : Handler m P) (trace : P.A → ω) (operation : P.A) :
    handler.withTraceAppendBefore trace operation = (do
      tell (trace operation)
      handler operation) :=
  by rfl

/-- Append-flavoured before-tracing is before-insertion of `tell`. -/
theorem withTraceAppendBefore_eq_preInsert {ω : Type u}
    [EmptyCollection ω] [Append ω]
    (handler : Handler m P) (trace : P.A → ω) :
    handler.withTraceAppendBefore trace =
      handler.preInsert (fun operation => tell (trace operation)) := by
  rfl

/-- Append-flavoured response-dependent tracing. -/
def withTraceAppend {ω : Type u} [EmptyCollection ω] [Append ω]
    (handler : Handler m P) (trace : (operation : P.A) → P.B operation → ω) :
    Handler (WriterT ω m) P :=
  handler.postInsert fun operation response => tell (trace operation response)

@[simp, grind =]
theorem withTraceAppend_apply {ω : Type u} [EmptyCollection ω] [Append ω]
    (handler : Handler m P) (trace : (operation : P.A) → P.B operation → ω)
    (operation : P.A) :
    handler.withTraceAppend trace operation = do
      let response ← handler operation
      tell (trace operation response)
      return response :=
  by rfl

/-- Append-flavoured after-tracing is after-insertion of `tell`. -/
theorem withTraceAppend_eq_postInsert {ω : Type u}
    [EmptyCollection ω] [Append ω]
    (handler : Handler m P) (trace : (operation : P.A) → P.B operation → ω) :
    handler.withTraceAppend trace =
      handler.postInsert (fun operation response => tell (trace operation response)) := by
  rfl

end Handler
end PFunctor
