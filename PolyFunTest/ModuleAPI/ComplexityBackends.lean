/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.Adequacy
public import ComplexityBackends.CslibSingleTape.Nontriviality
public import ComplexityBackends.CslibSingleTape.ProgramWitness

/-!
# The single-tape backend through ordinary imports

Consumers reach the backend's separation, its execution-work envelope, its description measure,
its per-parameter program witnesses and its per-step adequacy through public statements only;
`Boundary.toGeneric` and `EncPolyTime.size` are opaque, so the named cost and size laws are the
API.
-/

@[expose] public section

namespace PolyFunTest.ModuleAPI.ComplexityBackends

open PFunctor PFunctor.DynSystem.DynComputation
open _root_.ComplexityBackends.CslibSingleTape _root_.ComplexityBackends.CslibSingleTape.PPoly

/-- The constant-`true` family at the coin boundary, immediately returning. -/
def constProgram : (n : ℕ) → BitVec n → FreeM (CoinFam n) Bool := fun _ _ ↦ FreeM.pure true

example : ∃ function : (n : ℕ) → BitVec n → Bool,
    ¬ IsPPolyBy coinBoundary (fun n value ↦ FreeM.pure (function n value)) :=
  exists_not_isPPolyBy_pure

example (witness : Witness coinBoundary constProgram) (n : ℕ) (value : BitVec n)
    {finish : (witness.realization.machine n).State}
    (trace : witness.realization.ExecutionTrace n
      ((witness.realization.machine n).init value) finish) :
    ((witness.realization.toQuantitative n).executionCost value trace).work ≤
      witness.realization.totalTime.eval n :=
  witness.executionWork_le_totalTime n value trace

example (realization : Realization coinBoundary) (n : ℕ) (value : BitVec n) :
    Backend.quantitative.cost (realization.toQuantitative n).initCode value =
      (realization.initCode.wit n).time.eval (coinBoundary.input.enc n value).length :=
  realization.toQuantitative_initCost n value

example {A B : Type} {a : A → List Bool} {b : B → List Bool} {f : A → B}
    (r : EncPolyTime a b f) : Backend.description.descSize r = r.size :=
  Backend.descSize_eq r

example : ∃ f : (n : ℕ) → BitVec n → Bool, ¬ ∃ q : Polynomial ℕ,
    ∀ᶠ n in Filter.atTop, (some ∘ f n) ∈
      Backend.description.RealizableLE (BitEncFam.bitVecX.enc n)
        (BitEncFam.bool.option.enc n) (q.eval n) :=
  Backend.exists_not_realizableLE_poly

/-- A P/poly certificate is a generic program witness at every parameter. -/
noncomputable example (witness : Witness coinBoundary constProgram) (n : ℕ) :
    PolynomialProgramWitness Backend.quantitative (coinBoundary.toGeneric n) (totalContract n)
      (constProgram n) :=
  witness.toPolynomialProgramWitness n

/-- Per-step adequacy: some halting run of a certified machine stays within its cost. -/
example {A B : Type} {a : A → List Bool} {b : B → List Bool} {f : A → B}
    (code : EncPolyTime a b f) (x : A) :
    ∃ t ≤ Backend.quantitative.cost code x,
      Relation.RelatesInSteps code.polyTime.tm.TransitionRelation
        (code.polyTime.tm.initCfg (a x)) (code.polyTime.tm.haltCfg (b (f x))) t :=
  Backend.cost_adequate code x

end PolyFunTest.ModuleAPI.ComplexityBackends
