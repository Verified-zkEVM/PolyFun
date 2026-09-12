/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.HandlerMachine

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

-- An answer is ready inside the handler after entry, but still has to reach the caller.
example : result (execute immediate 1 (FreeM.lift true)).phase = none := by rfl
example : (execute immediate 1 (FreeM.lift true)).administrative = 1 := by rfl
example : (execute immediate 1 (FreeM.lift true)).queries = 0 := by rfl

example : result (execute immediate 2 (FreeM.lift true)).phase = some false := by rfl
example : (execute immediate 2 (FreeM.lift true)).administrative = 2 := by rfl

/-- A handler whose second inner operation depends on its first answer. -/
@[expose] def twoQueries (position : Bool) : FreeM interface Bool := do
  let answer ← FreeM.lift (P := interface) position
  FreeM.lift (P := interface) answer

/-- A caller whose second outer position depends on its handler's first returned answer. -/
@[expose] def adaptive : FreeM interface Bool := do
  let answer ← FreeM.lift (P := interface) false
  FreeM.lift (P := interface) answer

example : result (execute twoQueries 7 adaptive).phase = none := by rfl
example : result (execute twoQueries 8 adaptive).phase = some false := by rfl
example : (execute twoQueries 8 adaptive).administrative = 4 := by rfl
example : (execute twoQueries 8 adaptive).queries = 4 := by rfl

-- The generic completion theorem uses component bounds, not a bound on the completed dispatcher.
example : MonadAttach.AllOutputs (fun out => ∃ value, out.phase = Phase.caller (FreeM.pure value))
    (runPrefix twoQueries (2 * (2 + 2)) (.caller adaptive)) := by
  apply runPrefix_complete
  · change 0 < 2 ∧ ∀ _ : Bool, 0 < 1 ∧ ∀ _ : Bool, True
    simp
  · intro position
    change 0 < 2 ∧ ∀ _ : Bool, 0 < 1 ∧ ∀ _ : Bool, True
    simp

end PolyFunTest.HandlerMachine
