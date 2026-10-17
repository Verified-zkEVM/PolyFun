/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Machine.Behavior
public import PolyFun.ITree.Machine
meta import PolyFun.PFunctor.Handler.Machine.Defs
meta import PolyFun.PFunctor.Dynamical.DynComputation.Resumable
meta import PolyFun.ITree.Machine

/-!
# Shared state and retained execution in compiled services

Two calls share a counter. Each call performs two primitive effects; pausing
inside the first call and continuing performs exactly four effects overall.
The tests execute the public chunk runners with an injected deterministic source.
-/

@[expose] public section

namespace MachineHandlerTest

open PFunctor PFunctor.DynSystem

abbrev Service : PFunctor := PUnit y^ Nat
abbrev Bits : PFunctor := PUnit y^ Bool

def handler : MachineHandler Service Bits Nat := fun _ => .ofFreeM fun count => do
  let _ ← FreeM.lift (P := Bits) PUnit.unit
  let _ ← FreeM.lift (P := Bits) PUnit.unit
  pure (count, count + 1)

def client (_ : Unit) : FreeM Service (Nat × Nat) := do
  let first ← FreeM.lift PUnit.unit
  let second ← FreeM.lift PUnit.unit
  pure (first, second)

def machine := handler.compile client

def draw : Handler (StateM Nat) Bits := fun _ => do
  let count ← get
  set (count + 1)
  pure (count % 2 == 0)

def run (first second : Nat) : Option ((Nat × Nat) × Nat) × Nat :=
  let action := do
    let chunk ← machine.startChunk (ITree.withSilentSteps draw) first ((), 0)
    let result ← machine.continueChunk (ITree.withSilentSteps draw) second chunk
    pure result.result
  action.run 0

run_cmd do
  unless run 8 0 == (some ((0, 1), 2), 4) do
    throwError "complete dispatch lost the shared service state"
  unless run 2 6 == (some ((0, 1), 2), 4) do
    throwError "resumption replayed or lost primitive effects"
  unless run 3 0 == (none, 2) do
    throwError "service return was confused with caller return"
  unless run 0 0 == (none, 0) do
    throwError "zero fuel performed an effect"
  unless run 8 100 == (some ((0, 1), 2), 4) do
    throwError "continuing a returned client performed an effect"

end MachineHandlerTest
