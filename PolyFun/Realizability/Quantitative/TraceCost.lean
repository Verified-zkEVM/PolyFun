/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative

/-!
# Local resource costs of machine traces

The initial observation, enabled transition, and terminal observation use the realizers and
representations stored in the quantitative machine. These equations are shared by pathwise
resource potentials and executed finite-prefix accounting.
-/

public section

universe u v w

namespace PFunctor.DynSystem.DynComputation.RankedResource

variable {p : PFunctor.{u, u}} {input output : Type u}
  {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {bd : Boundary C p input output}

/-- Cost of observing a state as the final state of an execution prefix. -/
@[expose]
def terminalCost (R : QuantitativeRealization Q bd) (state : R.machine.State) :
    ExecutionCost :=
  ExecutionCost.ofWork (Q.cost R.headCode state) +
    ExecutionCost.observe (Q.size R.state state) (Q.size bd.head (R.machine.head state))

/-- Cost contributed by one enabled position-response transition. -/
@[expose]
def queryStepCost (R : QuantitativeRealization Q bd) (state : R.machine.State)
    (position : p.A) (direction : p.B position) : ExecutionCost :=
  ExecutionCost.ofWork (Q.cost R.headCode state) +
    ExecutionCost.ofWork (Q.cost R.updateCode (state, ⟨position, direction⟩)) +
    ExecutionCost.observe (Q.size R.state state) (Q.size bd.head (R.machine.head state)) +
    ExecutionCost.query (Q.size bd.pos position) (Q.size bd.idx ⟨position, direction⟩)

/-- Observing a state makes no oracle query. -/
@[simp]
theorem queries_terminalCost (R : QuantitativeRealization Q bd) (state : R.machine.State) :
    (terminalCost R state).queries = 0 := by
  simp [terminalCost]

/-- Each enabled transition records exactly one visible query. -/
@[simp]
theorem queries_queryStepCost (R : QuantitativeRealization Q bd) (state : R.machine.State)
    (position : p.A) (direction : p.B position) :
    (queryStepCost R state position direction).queries = 1 := by
  simp [queryStepCost]

@[simp]
theorem executionTrace_cost_query {R : QuantitativeRealization Q bd}
    {state : R.machine.State} {position : p.A} {next : p.B position → R.machine.State}
    {finish : R.machine.State}
    (view_eq : R.machine.view state = Sum.inr ⟨position, next⟩)
    (direction : p.B position) (tail : R.ExecutionTrace (next direction) finish) :
    (QuantitativeRealization.ExecutionTrace.query (R := R) view_eq direction tail).cost =
      queryStepCost R state position direction + tail.cost :=
  by
    simp [QuantitativeRealization.ExecutionTrace.cost, queryStepCost]

/-- Split prefix cost into initialization, transition cost, and the final observation. -/
theorem executionCost_eq_init_add_trace_add_terminal
    (R : QuantitativeRealization Q bd) (value : input) {finish : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init value) finish) :
    R.executionCost value trace =
      ExecutionCost.ofWork (Q.cost R.initCode value) + (trace.cost + terminalCost R finish) := by
  simp [QuantitativeRealization.executionCost, terminalCost, add_assoc]

end PFunctor.DynSystem.DynComputation.RankedResource
