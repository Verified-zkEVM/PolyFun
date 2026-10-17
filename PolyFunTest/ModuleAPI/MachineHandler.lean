/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.PFunctor.Handler.Machine.Behavior
import PolyFun.ITree.DomainLaws

/-! # Public API checks for composed services and continuous interpretations -/

public section

open PFunctor PFunctor.DynSystem

-- The dependent answer type and higher universe remain visible across ordinary imports.
example {P Q : PFunctor.{1, 1}} {S A B : Type 1}
    (h : MachineHandler P Q S) (client : A → FreeM P B) (input : A) (state : S) :
    ITree.WeakBisim (ITree.ofResumptionWithTau ((h.compile client).denote (input, state)))
      (h.execute (client input) state).toITree :=
  h.compile_weakBisim_execute client input state

example {P Q : PFunctor.{1, 1}} {S A B : Type 1}
    (h : MachineHandler P Q S) (caller : DynComputation.{1} P A B)
    (phase : MachineHandler.Phase h caller.State) :
    (h.dispatch caller).view phase = h.dispatchStep caller phase :=
  h.view_dispatch caller phase

example {P : PFunctor} {α β D : Type} [OmegaCompletePartialOrder D] [OrderBot D]
    (ret : β → D) (alg : Resumption.ContinuousAlgebra P D)
    (tree : Resumption P α) (next : α → Resumption P β) :
    Resumption.denote ret alg (Resumption.bind tree next) =
      Resumption.denote (fun a => Resumption.denote ret alg (next a)) alg tree :=
  Resumption.denote_bind ret alg tree next
