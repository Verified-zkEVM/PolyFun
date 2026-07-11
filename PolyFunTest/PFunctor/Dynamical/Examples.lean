/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.Unfold
public import PolyFun.PFunctor.Dynamical.Behavior
public import PolyFun.PFunctor.Dynamical.Combinators
public import PolyFun.PFunctor.Dynamical.Run
public import PolyFun.PFunctor.Dynamical.System

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

/-! ## The universe polynomial and generic orbits -/

/-- A machine-style system over the universe polynomial: the exposed position is
the type of currently enabled events. From `n`, choosing `true` increments and
`false` stays. -/
def toggle : DynSystem univ where
  State := ℕ
  expose := fun _ => Bool
  update := fun n b => if b then n + 1 else n

example : toggle.update (3 : ℕ) true = (4 : ℕ) := rfl

example : toggle.out (3 : ℕ) = ⟨Bool, fun b => if b then (4 : ℕ) else (3 : ℕ)⟩ := rfl

/-- The input-stream orbit of the counter as a generic `Run`. -/
example : (counter.streamRun (0 : ℕ) fun _ => 2).state 3 = (6 : ℕ) := rfl

/-- Reading stable event labels off a generic run. -/
def parityEvent : counter.EventMap Bool := fun _ (i : ℕ) => i % 2 == 0

example : (counter.streamRun (0 : ℕ) fun _ => 2).eventsUpTo parityEvent 2 = [true, true] := rfl

/-- The unique orbit of a closed system is its state iterate. -/
example : ((counter.feedback fun _ => 1).iterateRun (0 : ℕ)).state 5 = (5 : ℕ) := rfl

/-- Every run of a Moore machine is its input-driven state stream. -/
example (r : DynSystem.Run counter) (n : ℕ) :
    r.state n = counter.stateStream r.initial r.dir n :=
  counter.state_eq_stateStream r n

/-- Zero-step reachability is reflexive. -/
example : toggle.ReachableIn 0 (3 : ℕ) (3 : ℕ) := .refl toggle (3 : ℕ)

/-- Two increments reach `5` from `3` in two steps. -/
example : toggle.ReachableIn 2 (3 : ℕ) (5 : ℕ) :=
  .step true (.step true (.refl toggle (5 : ℕ)))

/-! ## Asynchronous choice -/

/-- One `choiceProd` step advances exactly the chosen side. -/
example :
    (counter.choiceProd counter).update ((0 : ℕ), (5 : ℕ)) (.inl (3 : ℕ))
      = ((3 : ℕ), (5 : ℕ)) := rfl

example :
    (counter.choiceProd counter).update ((0 : ℕ), (5 : ℕ)) (.inr (7 : ℕ))
      = ((0 : ℕ), (12 : ℕ)) := rfl

/-! ## Behavior trees and ITree unfolding -/

/-- The defining equation of the terminal-coalgebra behavior. -/
example : M.dest (counter.behavior (2 : ℕ))
    = ⟨(2 : ℕ), fun (i : ℕ) => counter.behavior (2 + i)⟩ :=
  counter.dest_behavior (2 : ℕ)

/-- Observational equivalence is reflexive by definition. -/
example : DynSystem.ObsEq counter counter (3 : ℕ) (3 : ℕ) := rfl

/-- The cofree trajectory is the self-labeled behavior tree. -/
example (st : ℕ) : counter.trajectory st = M.selfLabel (counter.behavior st) :=
  counter.trajectory_eq_selfLabel_behavior st

/-- The ITree unfolding is the query-embedding of the behavior tree. -/
example (st : ℕ) : counter.toITree st = M.toITree (counter.behavior st) :=
  counter.toITree_eq_toITree_behavior st

end DynSystem.Examples

end PFunctor
