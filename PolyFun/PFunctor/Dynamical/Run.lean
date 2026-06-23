/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Basic

/-!
# Running Moore machines on finite inputs

Niu–Spivak §4.1: a Moore machine consumes a sequence of inputs, threading the
state through its transition function and observing an output at each visited
state. This file provides the finite-run semantics.

* `MooreMachine.stepM` — a single input step.
* `MooreMachine.run` — the final state after folding a list of inputs.
* `MooreMachine.trace` — the list of outputs observed along the way (classical
  Moore semantics: one more output than inputs, including the initial output).
* `MooreMachine.outputOn` — the final output after consuming a word.
* `DetAutomaton.accepts` — language membership for a Boolean automaton.
-/

@[expose] public section

universe u uO uI

namespace PFunctor

namespace MooreMachine

variable {O : Type uO} {I : Type uI}

/-- A single input step of a Moore machine. -/
def stepM (m : MooreMachine O I) (st : m.State) (i : I) : m.State :=
  m.transition st i

/-- The state reached after consuming a list of inputs from `st`. -/
def run (m : MooreMachine O I) (st : m.State) : List I → m.State :=
  List.foldl (fun s i => m.stepM s i) st

/-- The list of outputs observed while consuming a word, including the initial
output. Its length is `inputs.length + 1`. -/
def trace (m : MooreMachine O I) (st : m.State) : List I → List O
  | [] => [m.output st]
  | i :: is => m.output st :: m.trace (m.stepM st i) is

/-- The final output after consuming a word from `st`. -/
def outputOn (m : MooreMachine O I) (st : m.State) (is : List I) : O :=
  m.output (m.run st is)

@[simp] theorem run_nil (m : MooreMachine O I) (st : m.State) : m.run st [] = st := rfl

@[simp] theorem run_cons (m : MooreMachine O I) (st : m.State) (i : I) (is : List I) :
    m.run st (i :: is) = m.run (m.stepM st i) is := rfl

theorem run_append (m : MooreMachine O I) (st : m.State) (is js : List I) :
    m.run st (is ++ js) = m.run (m.run st is) js := by
  simp [run, List.foldl_append]

@[simp] theorem trace_length (m : MooreMachine O I) (st : m.State) (is : List I) :
    (m.trace st is).length = is.length + 1 := by
  induction is generalizing st with
  | nil => rfl
  | cons i is ih => simp [trace, ih]

end MooreMachine

namespace DetAutomaton

variable {I : Type uI}

/-- Whether a Boolean deterministic automaton accepts a word: its final output is
`true`. -/
def accepts (a : DetAutomaton Bool I) (w : List I) : Prop :=
  a.toMooreMachine.outputOn a.start w = true

instance (a : DetAutomaton Bool I) (w : List I) : Decidable (a.accepts w) :=
  inferInstanceAs (Decidable (_ = true))

end DetAutomaton

end PFunctor
