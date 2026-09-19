/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Resource
public import PolyFunTest.Realizability.Quantitative

/-!
# Adversarial canaries for relation-restricted run bounds

Two canaries on the progress conjunct of `RunsWithinUnder`. Disallowing every answer refuses a
run bound even when the queried answer type is nonempty: the conjunct is about the allowed
answers, not about the inhabitants of the response type. Conversely, no backend, boundary, or
contract with an admissible response model has a `PolynomialProgramWitness` for the stuck
program: an untyped answer cannot be allowed. The `stuckRealization` canaries in
`PolyFunTest.Realizability.Quantitative` cover one fixed realization; the emptiness canary here
is generic in the realization.
-/

@[expose] public section

namespace PFunctor.QuantitativeAdversarialTest

open DynSystem.DynComputation QuantitativeTest

/-- An interface exposing one query with a Boolean response. -/
abbrev coinResponse : PFunctor := PFunctor.mk PUnit fun _ ↦ Bool

/-- The one-query program that ignores its answer. -/
def coinProgram : PUnit → FreeM coinResponse PUnit := fun _ ↦
  FreeM.liftBind PUnit.unit fun _ ↦ FreeM.pure PUnit.unit

/-- Quantitative realization of `coinProgram` under the cost-free test backend. -/
def coinRealization : QuantitativeRealization zeroBackend
    (Boundary.unconstrained coinResponse PUnit PUnit) where
  machine := ofFreeM coinProgram
  state := PUnit.unit
  initCode := PUnit.unit
  headCode := PUnit.unit
  updateCode := PUnit.unit

/-- A pending Boolean query does not satisfy a bound under a contract that allows no answer, even
though the response type is inhabited. -/
theorem coinRealization_not_runsWithinUnder_none :
    ¬coinRealization.RunsWithinUnder (fun _ _ ↦ False) (fun _ ↦ oneQueryBound) := by
  intro h
  have hview :
      (ofFreeM coinProgram).view ((ofFreeM coinProgram).init PUnit.unit) =
        Sum.inr ⟨PUnit.unit, fun _ ↦ FreeM.pure PUnit.unit⟩ := by
    rfl
  have hresponse : ∃ response, False :=
    h.response_exists PUnit.unit (.nil _) (by trivial) hview
  obtain ⟨_, hfalse⟩ := hresponse
  exact hfalse

/-- No program witness exists for a program whose first node queries a position with an empty
answer type, under any backend, boundary, and contract admitting a response model: the progress
conjunct demands an allowed answer where none is typed. -/
theorem isEmpty_polynomialProgramWitness_of_liftBind {p : PFunctor} {input output : Type}
    [DecidableEq p.A] {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
    {Q : QuantitativeStepClass C} {label : Type} {bd : Boundary C p input output}
    (contract : ResponseResourceContract Q bd.interface label) (model : contract.Model)
    {program : input → FreeM p output} (x : input) {position : p.A} [IsEmpty (p.B position)]
    {next : p.B position → FreeM p output} (hx : program x = FreeM.liftBind position next) :
    IsEmpty (PolynomialProgramWitness Q bd contract program) := by
  refine ⟨fun witness ↦ ?_⟩
  have hrun := witness.runBound.runsWithin model
  have hdest := congrArg Resumption.dest (witness.implements x)
  rw [dest_denote, hx, FreeM.dest_toResumption_liftBind] at hdest
  cases hview : witness.realization.machine.view (witness.realization.machine.init x) with
  | inl value => simp [hview] at hdest
  | inr query =>
      obtain ⟨direction, -⟩ := hrun.response_exists x (.nil _) (by trivial) hview
      have hpos : query.fst = position := by
        rw [hview] at hdest
        exact congrArg PFunctor.Obj.fst (Sum.inr.inj hdest)
      exact (IsEmpty.false (Eq.mp (congrArg p.B hpos) direction)).elim

/-- The permanently pending one-query program, with a body visible to this module. -/
def pendingProgram : Unit → FreeM emptyResponse Unit := fun _ ↦
  FreeM.liftBind PUnit.unit PEmpty.elim

/-- The stuck program has no program witness under any backend, boundary, and contract that
admits a response model. -/
theorem isEmpty_polynomialProgramWitness_pending {C : StepClass} [C.HasProd] [C.HasSum]
    [C.HasOption] {Q : QuantitativeStepClass C} {label : Type}
    (bd : Boundary C emptyResponse Unit Unit)
    (contract : ResponseResourceContract Q bd.interface label) (model : contract.Model) :
    IsEmpty (PolynomialProgramWitness Q bd contract pendingProgram) :=
  isEmpty_polynomialProgramWitness_of_liftBind contract model PUnit.unit rfl

end PFunctor.QuantitativeAdversarialTest
