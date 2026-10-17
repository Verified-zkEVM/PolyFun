/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.HandlerMachine
public import PolyFun.PFunctor.Handler.Machine.Admission
meta import PolyFun.PFunctor.Free.HandlerMachine
meta import PolyFun.PFunctor.Handler.Machine.Admission

/-!
# Explicit handler-dispatch regression examples

Even a handler with no inner queries needs two administrative transitions. A second canary
executes an adaptive caller with two-query handlers and checks both counters at completion.
-/

public section

open PFunctor FreeM FreeM.HandlerMachine

namespace PolyFunTest.HandlerMachine

/-- Boolean requests and responses for the caller and the handler. -/
abbrev interface : PFunctor := ⟨Bool, fun _ => Bool⟩

/-- One uniform dispatcher that answers every position without an inner query. -/
@[expose] def immediate (position : Bool) : FreeM interface Bool := pure (!position)

/-- Execute a finite dispatcher prefix with deterministic Boolean answers. -/
@[expose] def execute (impl : Bool → FreeM interface Bool) (fuel : ℕ)
    (program : FreeM interface Bool) : Prefix interface interface Bool :=
  FreeM.liftM (P := interface) (m := Id) (fun position => !position)
    (runPrefix (P := interface) (Q := interface) impl fuel (.caller program))

/-- A handler whose second inner operation depends on its first answer. -/
@[expose] def twoQueries (position : Bool) : FreeM interface Bool := do
  let answer ← FreeM.lift (P := interface) position
  FreeM.lift (P := interface) answer

/-- A caller whose second outer position depends on its handler's first returned answer. -/
@[expose] def adaptive : FreeM interface Bool := do
  let answer ← FreeM.lift (P := interface) false
  FreeM.lift (P := interface) answer

-- The generic completion theorem uses component bounds, not a bound on the completed dispatcher.
example : MonadAttach.AllOutputs (fun out => ∃ value, out.phase = Phase.caller (FreeM.pure value))
    (runPrefix twoQueries (2 * (2 + 2)) (.caller adaptive)) := by
  apply runPrefix_complete
  · change 0 < 2 ∧ ∀ _ : Bool, 0 < 1 ∧ ∀ _ : Bool, True
    simp
  · intro position
    change 0 < 2 ∧ ∀ _ : Bool, 0 < 1 ∧ ∀ _ : Bool, True
    simp

/-- A signature with genuinely different dependent answer types. -/
abbrev mixed : PFunctor := ⟨Bool, fun | true => Nat | false => Bool⟩

/-- One request returns without a primitive effect; the other performs one query. -/
def mixedHandler : Handler (FreeM interface) mixed
  | true => pure 7
  | false => FreeM.lift false

/-- The second call's Boolean answer controls the use of the first call's natural answer. -/
def mixedClient : FreeM mixed Nat := do
  let value ← FreeM.lift (P := mixed) true
  let increment ← FreeM.lift (P := mixed) false
  return if increment then value + 1 else value

/-- Exercise the actual shared runner, including a pause inside a dependent handler. -/
def checkFiniteDispatcher : IO Unit := do
  for (fuel, expected) in [(0, (none, 0, 0)), (1, (none, 1, 0)),
      (2, (some false, 2, 0)), (5, (some false, 2, 0))] do
    let out := execute immediate fuel (FreeM.lift true)
    unless (result out.phase, out.administrative, out.queries) == expected do
      throw (IO.userError s!"incorrect immediate-handler prefix at fuel {fuel}")
  for (fuel, expected) in [(0, (none, 0, 0)), (1, (none, 1, 0)),
      (2, (none, 1, 1)), (7, (none, 3, 4)), (8, (some false, 4, 4))] do
    let out := execute twoQueries fuel adaptive
    unless (result out.phase, out.administrative, out.queries) == expected do
      throw (IO.userError s!"incorrect adaptive-handler prefix at fuel {fuel}")
  let logged : Handler (StateM (List Bool)) interface := fun position => do
    modify (· ++ [position])
    return !position
  let (first, firstLog) :=
    ((runPrefix twoQueries 2 (.caller adaptive)).liftM logged).run []
  let (second, completeLog) :=
    ((runPrefix twoQueries 6 first.phase).liftM logged).run firstLog
  unless completeLog == [false, true, false, true] && result second.phase == some false &&
      first.administrative + second.administrative == 4 && first.queries + second.queries == 4 do
    throw (IO.userError "resuming replayed a query or lost dispatcher accounting")
  let dependent := FreeM.liftM (P := interface) (m := Id) (fun position => !position)
    (runPrefix mixedHandler 5 (.caller mixedClient))
  unless (result dependent.phase, dependent.administrative, dependent.queries) == (some 8, 4, 1) do
    throw (IO.userError "dependent handler answers or transition counts were lost")
  let admission (fuel : Nat) (_ : Bool) (state : PUnit × Nat) :
      Except String (Nat × (PUnit × Nat)) :=
    if state.2 = 0 then .error "refused" else .ok (fuel, (state.1, state.2 - 1))
  let timeout (_ : Bool) (_ : PUnit) (_ : FreeM interface Bool) := ("timeout", PUnit.unit)
  let capped := (service twoQueries).admitted (admission 1) timeout
  let (timedOut, timeoutLog) := (((adaptive.liftM capped).run).run (PUnit.unit, 1)).liftM
    logged |>.run []
  unless timedOut.1 == .error "timeout" && timedOut.2.2 == 0 && timeoutLog == [false] do
    throw (IO.userError "timeout lost its debit or continued the client")
  let admittedOnce := (service twoQueries).admitted (admission 2) timeout
  let (refused, refusalLog) := (((adaptive.liftM admittedOnce).run).run (PUnit.unit, 1)).liftM
    logged |>.run []
  unless refused.1 == .error "refused" && refused.2.2 == 0 && refusalLog == [false, true] do
    throw (IO.userError "refusal performed a query or lost earlier effects")
  IO.println "checkFiniteDispatcher: ok"

/-- info: checkFiniteDispatcher: ok -/
#guard_msgs in
#eval checkFiniteDispatcher

end PolyFunTest.HandlerMachine
