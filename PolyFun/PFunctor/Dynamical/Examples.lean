/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Combinators
public import PolyFun.PFunctor.Dynamical.Run

/-!
# Examples of dynamical systems

Small worked examples that exercise the `Dynamical` API and double as regression
tests: a counter Moore machine and its finite runs, the lens round-trip, and the
wrapper/parallel combinators.
-/

@[expose] public section

namespace PFunctor

namespace DynSystem.Examples

/-- A running-sum counter: state is the accumulated total, the output is the total
itself, and each input is added to the state. -/
def counter : MooreMachine ℕ ℕ := MooreMachine.mk' id (· + ·)

example : counter.run (0 : ℕ) [1, 2, 3] = (6 : ℕ) := rfl

example : counter.outputOn (0 : ℕ) [1, 2, 3] = 6 := rfl

example : counter.trace (0 : ℕ) [1, 2] = [0, 1, 3] := rfl

/-- `run` is compatible with list concatenation. -/
example (st : ℕ) (is js : List ℕ) :
    counter.run st (is ++ js) = counter.run (counter.run st is) js :=
  counter.run_append st is js

/-- The lens round-trip is definitional. -/
example {p : PFunctor} (s : DynSystem p) : ofLens s.toLens = s := rfl

/-- Wrapping with the identity lens is a no-op. -/
example {p : PFunctor} (s : DynSystem p) : wrap (Lens.id p) s = s := rfl

/-- A deterministic automaton whose state accumulates the `xor` of its inputs,
starting from `true`. -/
def parity : DetAutomaton Bool Bool where
  State := Bool
  output := id
  transition := fun b i => Bool.xor b i
  start := true

example : parity.accepts [true, true] := by decide

example : ¬ parity.accepts [true] := by decide

end DynSystem.Examples

end PFunctor
