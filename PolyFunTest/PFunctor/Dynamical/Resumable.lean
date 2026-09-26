/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.IO
meta import PolyFun.PFunctor.Dynamical.DynComputation.IO

/-! # Dependent responses, residual states, and real IO chunk boundaries -/

@[expose] public section

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation

namespace PolyFunTest.Resumable

/-- Query `n` accepts precisely a number no greater than `n`. -/
def signature : PFunctor where
  A := Nat
  B n := Fin (n + 1)

/-- A counter whose environment selects its next state through a dependent response. -/
abbrev counter : DynComputation signature Nat Nat := DynComputation.ofStep
  (fun n => match n with
    | 0 => .inl 0
    | n + 1 => .inr ⟨n + 1, fun answer => answer.val⟩) id

/-- Select the preceding counter value, respecting the query's response type. -/
def decrement (n : Nat) : Fin (n + 1) := ⟨n - 1, by omega⟩

/-- Count actual handler invocations independently of the machine state. -/
def counting : Handler (StateM Nat) signature := fun n => do
  modify (· + 1)
  return decrement n

/-- Check pause, resume, empty-interface return, and failure without simulated IO. -/
def checkChunks : IO Unit := do
  let (zero, count₀) := (counter.runChunk counting 0 5).run 0
  let .paused 5 := zero | throw (IO.userError "zero fuel lost the residual state")
  unless count₀ == 0 do throw (IO.userError "zero fuel performed an effect")
  let (first, count₁) := (counter.runChunk counting 2 5).run 0
  let .paused 3 := first | throw (IO.userError "wrong intermediate state")
  let (last, count₂) := (counter.runChunk counting 3 3).run count₁
  let .done 0 := last | throw (IO.userError "exact fuel did not recognize completion")
  unless count₂ == 5 do throw (IO.userError "resumption repeated or lost effects")
  let (whole, count₃) := (counter.runChunk counting 5 5).run 0
  let .done 0 := whole | throw (IO.userError "combined chunk did not finish")
  unless count₃ == count₂ do throw (IO.userError "chunk composition changed effects")
  let empty : DynComputation (0 : PFunctor.{0, 0}) Nat Nat := DynComputation.ofFn (· + 1)
  let .done 8 := empty.runChunk (m := Id) (fun position => nomatch position) 0 (empty.init 7)
    | throw (IO.userError "empty interface required fuel")
  let failed := counter.runChunk (m := Except String) (fun _ => .error "unavailable") 3 5
  match failed with
  | .error "unavailable" => pure ()
  | _ => throw (IO.userError "handler failure was hidden")
  IO.println "checkChunks: ok"
/-- Exercise the actual IO loop across two chunk boundaries. -/
def checkIO : IO Unit := do
  let calls ← IO.mkRef 0
  let handler : Handler IO signature := fun n => do
    calls.modify (· + 1)
    return decrement n
  let result ← counter.runIO handler 257
  unless result == 0 && (← calls.get) == 257 do
    throw (IO.userError "IO chunk boundaries repeated or lost effects")
  let terminal ← counter.runIO (fun _ => throw (IO.userError "terminal state queried")) 0
  unless terminal == 0 do throw (IO.userError "terminal state changed its result")
  let failedCalls ← IO.mkRef (0 : Nat)
  let failed ← try
    let _ ← counter.runIO (fun n => do
      failedCalls.modify (· + 1)
      if (← failedCalls.get) == 129 then
        throw (IO.userError "failure after chunk boundary")
      return decrement n) 257
    pure false
  catch error => pure (error.toString == "failure after chunk boundary")
  unless failed && (← failedCalls.get) == 129 do
    throw (IO.userError "IO resumption hid failure or repeated effects")
  IO.println "checkIO: ok"
/-- info: checkChunks: ok -/
#guard_msgs in
#eval checkChunks
/-- info: checkIO: ok -/
#guard_msgs in
#eval checkIO

end PolyFunTest.Resumable
