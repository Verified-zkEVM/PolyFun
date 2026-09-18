/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Basic
public import PolyFun.PFunctor.Handler

/-!
# Requests, programs, and handlers

A program asks two dependent questions. Changing its handler changes the answers without
changing the program. The README excerpt is checked against this module by the documentation
integrity checker. Import this module to explore the definitions in `PolyFunExamples.Requests`.
-/

@[expose] public section

namespace PolyFunExamples.Requests

-- BEGIN README
/-- A request is a natural number; its response is another natural number. -/
abbrev Request : PFunctor := ⟨Nat, fun _ => Nat⟩

/-- The first answer determines the second request. -/
def twoRequests : PFunctor.FreeM Request (Nat × Nat) := do
  let first ← PFunctor.FreeM.lift (P := Request) 3
  let second ← PFunctor.FreeM.lift (P := Request) first
  return (first, second)

/-- This handler answers a request by incrementing it. -/
def increment : PFunctor.Handler Id Request := fun n => n + 1

example : twoRequests.liftM increment = (4, 5) := rfl
-- END README

/-- A different interpretation of the same requests. -/
def double : PFunctor.Handler Id Request := fun n => 2 * n

/-- Changing the handler also changes the second request. -/
theorem twoRequests_double : twoRequests.liftM double = (6, 12) := rfl

end PolyFunExamples.Requests
