/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.ResumptionWithTau
public import PolyFun.PFunctor.Dynamical.DynComputation.Resumable

/-! # Resumable execution of interaction trees

A silent step consumes chunk budget but never invokes the visible-event handler. Pausing retains
the exact tree residual; a finite budget makes no claim of termination or productivity.
Physical IO belongs to the interpreter, not to this representation adapter.
-/

public section

namespace ITree

universe uA u uM

/-- Interpret visible operations normally and acknowledge silent steps internally. -/
@[expose] def withSilentSteps {P : PFunctor.{uA, u}} {m : Type u → Type uM} [Monad m]
    (handler : PFunctor.Handler m P) : PFunctor.Handler m (P + PFunctor.y.{uA, u}) :=
  PFunctor.Handler.sum handler (fun _ => Pure.pure PUnit.unit)

/-- The exact tree/resumption representation, with visible and silent events both budgeted. -/
@[expose] def machine {P : PFunctor.{uA, u}} {α : Type u} :
    PFunctor.DynSystem.DynComputation (P + PFunctor.y.{uA, u}) (ITree P α) α :=
  .ofResumption toResumptionWithTau

@[simp] theorem withSilentSteps_visible {P : PFunctor.{uA, u}}
    {m : Type u → Type uM} [Monad m] (handler : PFunctor.Handler m P) (operation : P.A) :
    withSilentSteps handler (.inl operation) = handler operation := rfl

@[simp] theorem withSilentSteps_silent {P : PFunctor.{uA, u}}
    {m : Type u → Type uM} [Monad m] (handler : PFunctor.Handler m P) :
    withSilentSteps handler (.inr PUnit.unit) = Pure.pure PUnit.unit := rfl

end ITree
