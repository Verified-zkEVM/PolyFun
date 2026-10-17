/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Machine
public import PolyFun.PFunctor.Dynamical.DynComputation.Resumable
public import PolyFun.PFunctor.Handler.Sum

/-! # Resumable execution of interaction trees

A silent step consumes chunk budget but never invokes the visible-event handler. Pausing retains
the exact tree residual; a finite budget makes no claim of termination or productivity.
Physical IO belongs to the interpreter, not to this representation adapter.
-/

public section

namespace ITree

universe uA u uM

/-- The exact tree/resumption representation, with visible and silent events both budgeted. -/
@[expose] def machine {P : PFunctor.{uA, u}} {α : Type u} :
    PFunctor.DynSystem.DynComputation (P + PFunctor.y.{uA, u}) (ITree P α) α :=
  toDynComputation

end ITree
