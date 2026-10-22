/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Run
public import Cslib.Computability.Automata.DA.Basic
public import Mathlib.Computability.DFA

/-!
# Moore machines as CSLib and Mathlib automata

A Moore machine `S y^ S ⇆ O y^ I` is a functional transition system together with an output map,
and a `DeterministicAutomaton` adds a start state. This file identifies them with CSLib's `FLTS`,
`Automata.DA` and `Automata.DA.FinAcc` and with Mathlib's `DFA`, so that the run, acceptance and
language theory of those libraries applies:

* `MooreMachine.toFLTS`, with `MooreMachine.run` as CSLib's multistep transition `FLTS.mtr`
  (`run_eq_mtr`);
* `DeterministicAutomaton.toDA`, whose infinite run is the stream-driven state
  (`stateStream_eq_run_toDA`);
* for Boolean output, `DeterministicAutomaton.toFinAcc` and `DeterministicAutomaton.toDFA`, which
  accept exactly the words that `DeterministicAutomaton.Accepts` accepts.

Each bridge keeps the state, input and output universes independent.
-/

@[expose] public section

universe u uO uI

namespace PFunctor

namespace MooreMachine

variable {S : Type u} {O : Type uO} {I : Type uI}

/-- The functional transition system of a Moore machine: its transition function, forgetting
the output. -/
def toFLTS (m : MooreMachine S O I) : Cslib.FLTS S I := ⟨m.transition⟩

@[simp] theorem toFLTS_tr (m : MooreMachine S O I) : m.toFLTS.tr = m.transition := rfl

/-- The state reached on a word is CSLib's multistep transition. -/
theorem run_eq_mtr (m : MooreMachine S O I) (st : S) (is : List I) :
    m.run st is = m.toFLTS.mtr st is := rfl

end MooreMachine

namespace DeterministicAutomaton

variable {O : Type uO} {I : Type uI}

/-- The CSLib deterministic automaton of a `DeterministicAutomaton`, forgetting the output. -/
def toDA (a : DeterministicAutomaton.{u} O I) : Cslib.Automata.DA a.State I :=
  { a.toMooreMachine.toFLTS with start := a.start }

/-- The CSLib infinite run of `a.toDA` is the stream-driven state of the Moore machine. -/
theorem stateStream_eq_run_toDA (a : DeterministicAutomaton.{u} O I)
    (xs : Cslib.ωSequence I) (n : ℕ) :
    a.toMooreMachine.stateStream a.start xs n = a.toDA.run xs n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [MooreMachine.stateStream_succ, ih]; rfl

/-- The CSLib automaton on finite words of a Boolean `DeterministicAutomaton`: its accepting
states are those with output `true`. -/
def toFinAcc (a : DeterministicAutomaton.{u} Bool I) : Cslib.Automata.DA.FinAcc a.State I :=
  { a.toDA with accept := {s | a.output s = true} }

/-- `toFinAcc` accepts exactly the words that `a` accepts. -/
theorem accepts_toFinAcc_iff (a : DeterministicAutomaton.{u} Bool I) (w : List I) :
    Cslib.Automata.Acceptor.Accepts a.toFinAcc w ↔ a.Accepts w := Iff.rfl

/-- The Mathlib `DFA` of a Boolean `DeterministicAutomaton`: its accepting states are those with
output `true`. -/
def toDFA (a : DeterministicAutomaton.{u} Bool I) : DFA I a.State where
  step := a.transition
  start := a.start
  accept := {s | a.output s = true}

/-- Evaluating `toDFA` on a word is running the Moore machine from the start state. -/
theorem eval_toDFA (a : DeterministicAutomaton.{u} Bool I) (w : List I) :
    a.toDFA.eval w = a.toMooreMachine.run a.start w := rfl

/-- The language of `toDFA` consists of the words that `a` accepts. -/
theorem mem_accepts_toDFA (a : DeterministicAutomaton.{u} Bool I) (w : List I) :
    w ∈ a.toDFA.accepts ↔ a.Accepts w := Iff.rfl

end DeterministicAutomaton

end PFunctor
