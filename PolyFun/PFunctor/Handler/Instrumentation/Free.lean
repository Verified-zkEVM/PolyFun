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
  {ω α : Type u} [EmptyCollection ω] [Append ω]

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
