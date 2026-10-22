/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Complexity.Computability.Probabilistic.Oracle.Composition
public import PolyFunComplexitylib.Backend.Quantitative

/-!
# Adequacy for closed iterated machines

PolyFun realizes a machine by a state, code for its initial state and code for its step. For a
closed deterministic machine, which issues no oracle calls, complexitylib's bounded-iteration rule
turns codes from `PolyFunComplexitylib.quantitative` and a round count computed in polynomial time
into strict oracle polynomial time against every external oracle, provided each step grows the
encoded state by a bounded amount.

A machine whose steps issue typed queries additionally needs word encodings of its interface's
positions and answers; complexitylib's rule `Cslib.Probability.IsOraclePPTOn.iterateWith_spec`
covers that case once a step is certified.

## Main results

* `PolyFunComplexitylib.isOraclePPTOn_iterate_of_code`: the iterated machine is strict oracle PPT.
* `PolyFunComplexitylib.isOraclePPTOn_iterate_pure_of_code`: the same for its result, as a pure
  function of the input.
-/

@[expose] public section

namespace PolyFunComplexitylib

open Turing.MultiTapeTM Cslib Cslib.Probability

variable {Operation α σ : Type} [DecidableEq Operation] [Finite Operation]
  {input : α ↪ List Bool} {stateEncoding : σ ↪ List Bool}
  {initial : α → σ} {step : σ → σ} {count : α → ℕ}

/-- Iterating deterministic steps returns the iterated function. -/
theorem iterate_pure_eq {Operation : Type} (step : σ → σ) (n : ℕ) (initial : σ) :
    OracleComp.iterate (spec := probOracleSpec fun _ : Operation × List Bool => List Bool) n
      (fun s => pure (step s)) initial = pure (step^[n] initial) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [OracleComp.iterate, ih, pure_bind, Function.iterate_succ_apply']

/-- Iterating a polynomial-time step a polynomially computed number of times, with additively
bounded growth of the encoded state, is strict oracle PPT against every external oracle. -/
theorem isOraclePPTOn_iterate_of_code (cinitial : PolyTimeCode input stateEncoding initial)
    (cstep : PolyTimeCode stateEncoding stateEncoding step)
    (hcount : ComputableTidilyInPolyTime count input encUnary) {growth : ℕ}
    (hgrowth : ∀ s, (stateEncoding (step s)).length ≤ (stateEncoding s).length + growth) :
    IsOraclePPTOn (Operation := Operation) input stateEncoding
      (fun a => OracleComp.iterate (count a) (fun s => pure (step s)) (initial a)) :=
  IsOraclePPTOn.iterate_of_bounded_growth hcount cinitial.computableTidilyInPolyTime
    cstep.computableTidilyInPolyTime.isOraclePPTOn fun s next hnext => by
      rw [ProbOracleComp.eq_of_mem_support_pure hnext]
      exact hgrowth s

/-- The result of polynomially many polynomial-time steps with bounded growth is strict oracle
PPT as a pure function of the input. -/
theorem isOraclePPTOn_iterate_pure_of_code (cinitial : PolyTimeCode input stateEncoding initial)
    (cstep : PolyTimeCode stateEncoding stateEncoding step)
    (hcount : ComputableTidilyInPolyTime count input encUnary) {growth : ℕ}
    (hgrowth : ∀ s, (stateEncoding (step s)).length ≤ (stateEncoding s).length + growth) :
    IsOraclePPTOn (Operation := Operation) input stateEncoding
      (fun a => pure (step^[count a] (initial a))) :=
  (isOraclePPTOn_iterate_of_code cinitial cstep hcount hgrowth).congr fun a _ _ _ => by
    rw [iterate_pure_eq]

end PolyFunComplexitylib
