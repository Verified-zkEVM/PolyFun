/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Instrumentation
public import PolyFun.PFunctor.Handler.Free
public import PolyFun.Control.Monad.Hom.Writer

/-!
# Trace erasure for free handler interpretation

Discarding writer output is a monad morphism. Naturality of the universal fold
therefore transports the one-operation erasure law to every finite free program.
-/

public section

universe u v uA

namespace PFunctor.Handler

variable {p : PFunctor.{uA, u}} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  {ω α : Type u}

/-- Before-tracing a free node prefixes its observation to the continuation's writer output. -/
theorem run_liftM_withTraceBefore_liftBind [Monoid ω] (handler : Handler m p)
    (trace : p.A → ω) (a : p.A) (next : p.B a → FreeM p α) :
    (FreeM.liftM (handler.withTraceBefore trace) (.liftBind a next)).run =
      (handler a >>= fun answer =>
        (fun out : α × ω => (out.1, trace a * out.2)) <$>
          (FreeM.liftM (handler.withTraceBefore trace) (next answer)).run) := by
  change ((handler.withTraceBefore trace a) >>=
    fun answer => FreeM.liftM (handler.withTraceBefore trace) (next answer)).run = _
  simp [withTraceBefore_apply, bind_map_left, map_bind]

variable [EmptyCollection ω] [Append ω]

/-- Erasing response-dependent trace output recovers the uninstrumented fold. -/
theorem fst_map_run_liftM_withTraceAppend (handler : Handler m p)
    (trace : (a : p.A) → p.B a → ω) (program : FreeM p α) :
    Prod.fst <$> (FreeM.liftM (handler.withTraceAppend trace) program).run =
      FreeM.liftM handler program := by
  change WriterT.eraseHom (∅ : ω) (· ++ ·)
    (FreeM.liftM (handler.withTraceAppend trace) program) = _
  rw [FreeM.liftM_natural]
  congr 1
  funext operation
  simp [withTraceAppend_apply]

end PFunctor.Handler
