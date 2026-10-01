/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Handler

/-!
# Stateful lenses through ordinary imports

Substitution along a stateful lens is `Handler.Stateful.run` of its handler, the product machine
denotes stateful substitution by `simp`, and the bounded transfer applies to any bounded
realization with executable lens code. These are the spellings a consumer in another package uses.
-/

@[expose] public section

universe u v w

namespace PolyFunTest.ModuleAPI.StateLens

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation

variable {p r : PFunctor.{u, u}} {σ α β : Type u}

example (L : StateLens p r σ) (program : FreeM p β) (state : σ) :
    L.mapFreeM program state = L.toStateful.run program state :=
  L.mapFreeM_eq_run program state

example (M : DynComputation.{u} p α β) (L : StateLens p r σ) (input : α × σ) :
    (M.wrapState L).denote input = L.mapResumption (M.denote input.1) input.2 := by
  simp

example {M : DynComputation.{u} p α β} {program : α → FreeM p β} (h : M.Implements program)
    (L : StateLens p r σ) :
    (M.wrapState L).Implements fun input ↦ L.toStateful.run (program input.1) input.2 :=
  h.wrapState_run L

variable {C : StepClass.{u, v}} [P : C.HasProd] [S : C.HasSum] [O : C.HasOption]
  [DecidableEq p.A] [DecidableEq r.A] {Q : QuantitativeStepClass.{u, v, w} C}
  {bd : Boundary C p α β} [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption]
  [Q.IsDistributive]

example {R : QuantitativeRealization Q bd} {stateRep : C.Str σ} {posRep : C.Str r.A}
    {idxRep : C.Str r.Idx} {L : StateLens p r σ}
    {hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep}
    {allowsP : ∀ position, p.B position → Prop} {allowsR : ∀ position, r.B position → Prop}
    {bound : α → ExecutionCost} (h : R.RunsWithinUnder allowsP bound)
    (cert : QuantitativeRealization.WrapStateCostCertificate R hL allowsR)
    (contract : ∀ position state answer, allowsR (L.pos (position, state)) answer →
      allowsP position (L.answer (position, state) answer))
    (progress : ∀ position state, (∃ direction, allowsP position direction) →
      ∃ answer, allowsR (L.pos (position, state)) answer) :
    (R.wrapState stateRep posRep idxRep hL).RunsWithinUnder allowsR fun input ↦
      (bound input.1).handled (bound input.1).queries (cert.carry input) (cert.traffic input) :=
  h.wrapState cert contract progress

end PolyFunTest.ModuleAPI.StateLens
