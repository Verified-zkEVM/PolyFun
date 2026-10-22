/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Automata

/-!
# Moore machines as CSLib and Mathlib automata

A parity automaton, read through Mathlib's `DFA` and CSLib's `DA.FinAcc`, and the identification
of `MooreMachine.run` with CSLib's `FLTS.mtr` at independent universes.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.Dynamical.AutomataExamples

open _root_.PFunctor

/-- Accepts the words with an odd number of `true` letters. -/
def parity : DeterministicAutomaton.{0} Bool Bool where
  State := Bool
  output := id
  transition state letter := xor state letter
  start := false

example : parity.Accepts [true, false] := by decide

example : [true, false] ∈ parity.toDFA.accepts :=
  (parity.mem_accepts_toDFA _).mpr (by decide)

example : Cslib.Automata.Acceptor.Accepts parity.toFinAcc [false, true] :=
  (parity.accepts_toFinAcc_iff _).mpr (by decide)

/-- Mathlib's `DFA` lemmas apply to the bridged automaton. -/
example (w v : List Bool) :
    parity.toDFA.evalFrom parity.toDFA.start (w ++ v) =
      parity.toDFA.evalFrom (parity.toDFA.evalFrom parity.toDFA.start w) v :=
  parity.toDFA.evalFrom_of_append _ w v

example {S : Type 2} {O : Type} {I : Type 1} (m : MooreMachine S O I) (st : S)
    (is js : List I) : m.run st (is ++ js) = m.toFLTS.mtr (m.toFLTS.mtr st is) js := by
  rw [m.run_eq_mtr, Cslib.FLTS.mtr_append_eq]

end PolyFunTest.PFunctor.Dynamical.AutomataExamples
