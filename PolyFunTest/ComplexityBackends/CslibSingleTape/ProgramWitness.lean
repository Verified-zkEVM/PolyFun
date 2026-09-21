/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.Adequacy
public import ComplexityBackends.CslibSingleTape.ProgramWitness
public import PolyFunTest.ComplexityBackends.CslibSingleTape.PPoly

/-!
# Canaries for per-parameter program witnesses and per-step adequacy

The P/poly fixtures of `PolyFunTest.ComplexityBackends.CslibSingleTape.PPoly` become generic
program witnesses at every parameter, with the constant `runBoundCost` as their second-order
bound. The adequacy canaries evaluate `cost_adequate` and `run_length_le_cost` on a constant
code.
-/

open PFunctor PFunctor.DynSystem.DynComputation ComplexityBackends.CslibSingleTape
  ComplexityBackends.CslibSingleTape.PPoly

@[expose] public section

namespace PolyFunTest.ComplexityBackends.CslibSingleTape.ProgramWitness

open PolyFunTest.ComplexityBackends.CslibSingleTape.PPoly

/-! ## The constant run bound of an immediately returning certificate -/

example (n : ℕ) : (runBoundCost boolRealization n).work = boolRealization.totalTime.eval n :=
  rfl

example (n : ℕ) : (runBoundCost boolRealization n).queries = 0 := by
  simp [runBoundCost, boolRealization]

example (n : ℕ) : (runBoundCost boolRealization n).traffic = 0 := by
  simp [runBoundCost, boolRealization]

example (n : ℕ) :
    (runBoundCost boolRealization n).peakStateSize = boolRealization.state.bound.eval n :=
  rfl

example (n : ℕ) : (runBoundCost boolRealization n).peakHeadSize =
    1 + (boolBoundary.output.widBound.eval n + boolBoundary.position.widBound.eval n) :=
  rfl

/-! ## The bridge at every parameter -/

/-- The querying step certificate is a generic program witness at each parameter. -/
noncomputable def boolStepProgramWitness (n : ℕ) :
    PolynomialProgramWitness Backend.quantitative (boolStepBoundary.toGeneric n)
      (totalContract n) (boolQueryProgram n) :=
  boolStepWitness.toPolynomialProgramWitness n

example (n : ℕ) :
    (boolStepProgramWitness n).realization = boolStepRealization.toQuantitative n :=
  rfl

/-- Under every response model the bridge's bound is the constant `runBoundCost`. -/
example (n : ℕ) (model : (totalContract (bd := boolStepBoundary) n).Model) (value : Bool) :
    (boolStepProgramWitness n).runBound.bound model value =
      runBoundCost boolStepRealization n := by
  simp only [boolStepProgramWitness]
  rw [PolynomialRunBound.bound_apply, Witness.toPolynomialProgramWitness_polynomial,
    ExecutionCostPolynomial.eval_const]
  rfl

example (n : ℕ) : (runBoundCost boolStepRealization n).queries = 1 := by
  simp [runBoundCost, boolStepRealization]

/-! ## Per-step adequacy on a constant code -/

/-- The constant-`true` code at the Boolean encoding. -/
noncomputable def constTrueCode :
    EncPolyTime (BitEncFam.bool.enc 0) (BitEncFam.bool.enc 0) (fun _ : Bool ↦ true) :=
  EncPolyTime.const _ _ true

/-- Some halting run of the constant machine stays within the cost envelope. -/
example (value : Bool) :
    ∃ t ≤ Backend.quantitative.cost constTrueCode value,
      Relation.RelatesInSteps constTrueCode.polyTime.tm.TransitionRelation
        (constTrueCode.polyTime.tm.initCfg (BitEncFam.bool.enc 0 value))
        (constTrueCode.polyTime.tm.haltCfg (BitEncFam.bool.enc 0 true)) t :=
  Backend.cost_adequate constTrueCode value

/-- Every halting run of the constant machine stays within the cost envelope. -/
example (value : Bool) {t : ℕ}
    (h : Relation.RelatesInSteps constTrueCode.polyTime.tm.TransitionRelation
      (constTrueCode.polyTime.tm.initCfg (BitEncFam.bool.enc 0 value))
      (constTrueCode.polyTime.tm.haltCfg (BitEncFam.bool.enc 0 true)) t) :
    t ≤ Backend.quantitative.cost constTrueCode value :=
  Backend.run_length_le_cost constTrueCode value h

end PolyFunTest.ComplexityBackends.CslibSingleTape.ProgramWitness
