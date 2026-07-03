/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Behavior
public import PolyFun.PFunctor.Dynamical.Run

/-!
# Examples of dynamical systems

Small worked examples that exercise the `Dynamical` API and double as regression
tests: a counter Moore machine and its finite runs, the lens round-trip, the
wrapper/parallel combinators, a genuinely mode-dependent (non-Moore) system, and
the closed-loop feedback / stream behaviour.
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
def parity : DeterministicAutomaton Bool Bool where
  State := Bool
  output := id
  transition := Bool.xor
  start := true

example : parity.accepts [true, true] := by decide

example : ¬ parity.accepts [true] := by decide

/-! ## A mode-dependent system

A genuinely non-Moore interface whose available directions depend on the position:
in the `true` mode there is a single silent direction, while in the `false` mode the
direction is a `Bool`. This exercises the dependent `update : (s) → p.B (expose s) → State`. -/

/-- An interface with two modes: `true` exposes a `Unit` of directions, `false`
exposes a `Bool` of directions. -/
def gate : PFunctor := ⟨Bool, fun b => bif b then Unit else Bool⟩

/-- A system over `gate`: from the `true` mode it advances silently to `false`; from
the `false` mode the incoming `Bool` direction becomes the next mode. -/
def gateSys : DynSystem gate where
  State := Bool
  expose := id
  update := fun s => match s with
    | true => fun _ => false
    | false => id

example : gateSys.expose true = true := rfl

example : gateSys.update true () = false := rfl

example : gateSys.update false true = true := rfl

/-! ## Feedback and streams -/

/-- Closing the counter by always feeding back the input `1` makes it advance by one
each step, so its closed-loop output stream is the identity on time. -/
example : counter.feedbackStream (fun _ => 1) (0 : ℕ) 3 = 3 := rfl

/-- One step of the closed-loop recurrence. -/
example : counter.feedbackStream (fun _ => 1) (0 : ℕ) 1
    = counter.feedbackStream (fun _ => 1) (counter.transition (0 : ℕ) 1) 0 :=
  counter.feedbackStream_succ (fun _ => 1) (0 : ℕ) 0

/-- The output stream on a constant input stream. -/
example : counter.outputStream (0 : ℕ) (fun _ => 1) 3 = 3 := rfl

/-- Streams agree with finite runs on every prefix. -/
example (n : ℕ) :
    counter.stateStream (0 : ℕ) (fun _ => 1) n
      = counter.run (0 : ℕ) ((List.range n).map (fun _ => 1)) :=
  counter.stateStream_eq_run (0 : ℕ) (fun _ => 1) n

end DynSystem.Examples

end PFunctor
