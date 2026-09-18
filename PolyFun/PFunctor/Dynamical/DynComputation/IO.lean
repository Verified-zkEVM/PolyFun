/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.Resumable

/-! # Executing returning dynamical computations through Lean IO

The loop resumes bounded chunks and never replays already handled queries. It imposes
no termination assumption: an environment can keep a computation running indefinitely.
-/

public section

namespace PFunctor.DynSystem.DynComputation

universe uA uα

/-- The IO loop resumes bounded chunks; neither a chunk boundary nor a pause implies completion. -/
def runIO {p : PFunctor.{uA, 0}} {α : Type uα} {β : Type} (machine : DynComputation.{0} p α β)
    (handler : Handler IO p) (state : machine.State) : IO β := do
  let mut current := state
  repeat
    match ← runChunk machine handler 128 current with
    | .done value => return value
    | .paused residual => current := residual

end PFunctor.DynSystem.DynComputation
