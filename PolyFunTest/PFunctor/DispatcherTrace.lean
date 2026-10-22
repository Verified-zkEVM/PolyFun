/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Machine.Trace
public import PolyFunTest.PFunctor.MachineHandler
meta import PolyFun.PFunctor.Handler.Machine.Trace
meta import PolyFunTest.PFunctor.MachineHandler

/-!
# Executable dispatcher prefix decomposition

Every cutoff of a two-call execution distinguishes completed service work from
an unfinished call. A completed service body remains unfinished at the caller
level until the administrative return transition occurs.
-/

public section

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation MachineHandlerTest

namespace DispatcherTraceTest

/-- Two complete calls, each performing two primitive effects. -/
def completeTrace : machine.ExecutionTrace
    (.caller (client ()) 0) (.caller (pure (0, 1)) 2) := by
  refine ExecutionTrace.query (machine := machine) (position := Sum.inr PUnit.unit)
    (by rfl) PUnit.unit ?_
  refine ExecutionTrace.query (machine := machine) (position := Sum.inl PUnit.unit)
    (by rfl) false ?_
  refine ExecutionTrace.query (machine := machine) (position := Sum.inl PUnit.unit)
    (by rfl) true ?_
  refine ExecutionTrace.query (machine := machine) (position := Sum.inr PUnit.unit)
    (by rfl) PUnit.unit ?_
  refine ExecutionTrace.query (machine := machine) (position := Sum.inr PUnit.unit)
    (by rfl) PUnit.unit ?_
  refine ExecutionTrace.query (machine := machine) (position := Sum.inl PUnit.unit)
    (by rfl) true ?_
  refine ExecutionTrace.query (machine := machine) (position := Sum.inl PUnit.unit)
    (by rfl) false ?_
  refine ExecutionTrace.query (machine := machine) (position := Sum.inr PUnit.unit)
    (by rfl) PUnit.unit ?_
  exact .nil _


private def takeTrace {start finish : machine.State} (fuel : Nat)
    (trace : machine.ExecutionTrace start finish) :
    (result : machine.State) × machine.ExecutionTrace start result :=
  match fuel, trace with
  | 0, _ => ⟨start, .nil start⟩
  | _ + 1, .nil state => ⟨state, .nil state⟩
  | fuel + 1, .query hv answer tail =>
      let rest := takeTrace fuel tail
      ⟨rest.1, .query hv answer rest.2⟩

/-- Read completed calls, completed work, unfinished work and unmatched entry. -/
def describe {phase : MachineHandler.Phase handler (.ofFreeM client)}
    (view : MachineHandler.DispatchPrefix handler (.ofFreeM client) (client ()) 0 phase) :
    Nat × Nat × Nat × Nat :=
  match view with
  | .caller past => (past.callerTrace.length, past.primitiveSteps, 0, 0)
  | .handler past body => (past.callerTrace.length, past.primitiveSteps, body.length, 1)

/-- Decompose an actual execution prefix at its selected cutoff. -/
def prefixCounts (fuel : Nat) : Nat × Nat × Nat × Nat :=
  let trace := takeTrace fuel completeTrace
  describe (MachineHandler.DispatchPrefix.decompose trace.2)

run_cmd do
  let expected := #[(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 1), (0, 0, 2, 1),
    (1, 2, 0, 0), (1, 2, 0, 1), (1, 2, 1, 1), (1, 2, 2, 1), (2, 4, 0, 0)]
  for fuel in [:expected.size] do
    unless prefixCounts fuel == expected[fuel]! do
      throwError "dispatcher decomposition lost call boundaries or unfinished work at {fuel}"

end DispatcherTraceTest
