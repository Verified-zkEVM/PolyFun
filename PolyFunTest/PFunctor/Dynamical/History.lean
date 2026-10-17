/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.PFunctor.Dynamical.DynComputation.History
meta import PolyFun.PFunctor.Dynamical.DynComputation.History

/-!+# Histories retain execution without replay

A two-query machine is observed for longer than its execution. Its stateful
interpreter records exactly two calls, while every later coordinate retains the
returned result. Zero fuel retains the initial state without invoking the handler.
-/

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation

namespace PolyFunTest.History

private abbrev tick : PFunctor := ⟨Unit, fun _ => Unit⟩

private abbrev twice : DynComputation tick Nat Nat := .ofStep
  (fun n => if n < 2 then .inr ⟨(), fun _ => n + 1⟩ else .inl n) id

private def countCalls : Handler (StateM Nat) tick := fun _ => modify (· + 1)

/-- Check effect counts and all retained coordinates, including absorption and zero fuel. -/
public def checkHistory : IO Unit := do
  let (history, calls) := ((twice.unrollHistory 5 (twice.init 0)).liftM countCalls).run 0
  unless calls == 2 do throw (IO.userError s!"history replayed effects: {calls} calls")
  for i in List.finRange 6 do
    match history i with
    | .paused state =>
      unless i.val < 2 && state == i.val do
        throw (IO.userError s!"unexpected paused history at {i.val}: {state}")
    | .done value =>
      unless 2 ≤ i.val && value == 2 do
        throw (IO.userError s!"unexpected returned history at {i.val}: {value}")
  let (initial, initialCalls) :=
    ((twice.unrollHistory 0 (twice.init 0)).liftM countCalls).run 0
  unless initialCalls == 0 do throw (IO.userError "zero fuel invoked the handler")
  match initial 0 with
  | .paused 0 => pure ()
  | _ => throw (IO.userError "zero fuel lost the initialized state")
  IO.println "checkHistory: ok"

/-- info: checkHistory: ok -/
#guard_msgs in
#eval checkHistory

end PolyFunTest.History
