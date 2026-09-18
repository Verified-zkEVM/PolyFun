/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.Run

/-!
# A counter with explicit state

The counter exposes its accumulated total and adds each input to it. Finite runs keep
the final state, and traces retain the output before and after each input. The append law
explains how to continue a run from its current state.
-/

@[expose] public section

namespace PolyFunExamples.Machines

open PFunctor

/-- State and output are the accumulated sum; the environment supplies each increment. -/
def counter : MooreMachine Nat Nat Nat :=
  id ⇆ fun (total : Nat) (input : Nat) => total + input

example : counter.run 0 [1, 2, 3] = 6 := rfl

example : counter.trace 0 [1, 2] = [0, 1, 3] := rfl

/-- Running two input lists consecutively preserves the accumulated state. -/
theorem counter_run_append (initial : Nat) (first second : List Nat) :
    counter.run initial (first ++ second) =
      counter.run (counter.run initial first) second :=
  counter.run_append initial first second

end PolyFunExamples.Machines
