/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Strength

/-!
# Machine-level strength through ordinary imports

The input-retaining machine's initialization holds by `rfl`, its denotation rewrites with `simp`,
and its partial transition rewrites with `rw [update?_withInput]`. As for the other `update?`
equations, `simp` does not match an opaque `p.Idx` index. The carry leaves queries and traffic
unchanged by `simp`, and the law-based transfer applies to any bounded realization. These are the
spellings a consumer in another package uses.
-/

@[expose] public section

universe u v w

namespace PolyFunTest.ModuleAPI.Strength

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {α β : Type u}

example (M : DynComputation.{u} p α β) (input : α) :
    M.withInput.init input = (M.init input, input) := rfl

example (M : DynComputation.{u} p α β) (input : α) :
    M.withInput.denote input = Resumption.map (fun value ↦ (value, input)) (M.denote input) := by
  simp

example [DecidableEq p.A] (M : DynComputation.{u} p α β) (state : M.State × α)
    (index : p.Idx) :
    M.withInput.update? (state, index) =
      Option.map (fun next ↦ (next, state.2)) (M.update? (state.1, index)) := by
  rw [update?_withInput]

example (cost : ExecutionCost) (steps : ℕ) (c : Carry) :
    (cost.withCarry steps c).queries = cost.queries ∧
      (cost.withCarry steps c).traffic = cost.traffic := by
  simp

variable {C : StepClass.{u, v}} [P : C.HasProd] [S : C.HasSum] [O : C.HasOption]
  [DecidableEq p.A] {Q : QuantitativeStepClass.{u, v, w} C} {bd : Boundary C p α β}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive]
  [Q.HasCompositionCost] [Q.HasProdCost] [Q.HasSumCost] [Q.HasOptionCost] [Q.IsDistributiveCost]

example {R : QuantitativeRealization Q bd} {allows : ∀ position, p.B position → Prop}
    {bound : α → ExecutionCost} (h : R.RunsWithinUnder allows bound) :
    R.withInput.RunsWithinUnder allows fun input ↦ (bound input).withCarry (bound input).queries
      (QuantitativeRealization.lawCarry (Q := Q) (bound input) (Q.size bd.input input)) :=
  h.withInput_of_laws

end PolyFunTest.ModuleAPI.Strength
