/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative

/-!
# Carrying a value through a run

A product-state machine that runs a component machine while keeping a second, passive value pays
a per-step overhead on top of the component:
- extra work at initialization, at every readout and at every enabled transition;
- larger encoded states and readouts.

`Carry` records these allowances, and `ExecutionCost.withCarry` charges them along a run with a
given number of visible queries. Queries and traffic are unchanged.

The allowances of an honest backend grow with the sizes of the states and readouts involved, so
discharging them needs those sizes bounded along conforming runs. `RunsWithinUnder.size_state_le`,
`RunsWithinUnder.size_head_le` and `RunsWithinUnder.size_step_le` read such bounds off a run
bound's peak sizes and traffic.
-/

@[expose] public section

universe u v w

namespace PFunctor

/-- Per-step backend overhead of carrying a retained value through a run. -/
structure Carry where
  /-- Extra initialization work. -/
  init : ℕ
  /-- Extra work per readout. -/
  head : ℕ
  /-- Extra work per enabled transition. -/
  update : ℕ
  /-- Extra encoded hidden-state size. -/
  state : ℕ
  /-- Extra encoded readout size. -/
  headSize : ℕ

namespace ExecutionCost

/-- Charge a carry along the transitions of a trace with `steps` queries: `steps` readouts and
`steps` updates, and shifted peak sizes. Initialization and the final readout are not included;
see `withCarry`. -/
def traceCarry (cost : ExecutionCost) (steps : ℕ) (c : Carry) : ExecutionCost :=
  ⟨cost.work + steps * (c.head + c.update), cost.queries, cost.traffic,
    cost.peakStateSize + c.state, cost.peakHeadSize + c.headSize⟩

/-- Charge a carry over a whole run with `steps` visible queries: one initialization, `steps + 1`
readouts and `steps` enabled transitions. Queries and traffic are unchanged, and the peak sizes
are shifted by the size carries. -/
def withCarry (cost : ExecutionCost) (steps : ℕ) (c : Carry) : ExecutionCost :=
  ⟨cost.work + c.init + (steps + 1) * c.head + steps * c.update, cost.queries, cost.traffic,
    cost.peakStateSize + c.state, cost.peakHeadSize + c.headSize⟩

@[simp] theorem queries_withCarry (cost : ExecutionCost) (steps : ℕ) (c : Carry) :
    (cost.withCarry steps c).queries = cost.queries := rfl

@[simp] theorem traffic_withCarry (cost : ExecutionCost) (steps : ℕ) (c : Carry) :
    (cost.withCarry steps c).traffic = cost.traffic := rfl

/-- Carried bounds are monotone in the source resources and in the number of steps. -/
theorem withCarry_mono {cost bound : ExecutionCost} {steps steps' : ℕ} (c : Carry)
    (h : cost ≤ bound) (hsteps : steps ≤ steps') :
    cost.withCarry steps c ≤ bound.withCarry steps' c := by
  obtain ⟨hw, hq, ht, hs, hh⟩ := h
  have h1 : (steps + 1) * c.head ≤ (steps' + 1) * c.head :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : steps * c.update ≤ steps' * c.update := Nat.mul_le_mul_right _ hsteps
  refine ⟨?_, hq, ht, ?_, ?_⟩ <;> simp only [withCarry] <;> omega

/-- The bound of a run against a one-query stateful handler with `steps` queries:
- twice the source work, because the product transition recomputes the source's readout;
- the per-step carry;
- the source's query count;
- `steps` times the per-step inner traffic;
- peak sizes shifted by the size carries. -/
def handled (cost : ExecutionCost) (steps : ℕ) (c : Carry) (traffic : ℕ) : ExecutionCost :=
  ⟨2 * cost.work + c.init + (steps + 1) * c.head + steps * c.update, cost.queries,
    steps * traffic, cost.peakStateSize + c.state, cost.peakHeadSize + c.headSize⟩

@[simp] theorem queries_handled (cost : ExecutionCost) (steps : ℕ) (c : Carry) (traffic : ℕ) :
    (cost.handled steps c traffic).queries = cost.queries := rfl

/-- Handled bounds are monotone in the source resources and in the number of steps. -/
theorem handled_mono {cost bound : ExecutionCost} {steps steps' : ℕ} (c : Carry) (traffic : ℕ)
    (h : cost ≤ bound) (hsteps : steps ≤ steps') :
    cost.handled steps c traffic ≤ bound.handled steps' c traffic := by
  obtain ⟨hw, hq, ht, hs, hh⟩ := h
  have h1 : (steps + 1) * c.head ≤ (steps' + 1) * c.head := Nat.mul_le_mul_right _ (by omega)
  have h2 : steps * c.update ≤ steps' * c.update := Nat.mul_le_mul_right _ hsteps
  have h3 : steps * traffic ≤ steps' * traffic := Nat.mul_le_mul_right _ hsteps
  refine ⟨?_, hq, ?_, ?_, ?_⟩ <;> simp only [handled] <;> omega

end ExecutionCost

namespace DynSystem.DynComputation.QuantitativeRealization

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq p.A] {Q : QuantitativeStepClass.{u, v, w} C} {A B : Type u}
  {bd : Boundary C p A B}

/-! ## Reachable sizes are bounded by a run bound -/

/-- The final state of a conforming prefix is encoded within the bound's peak state size. -/
theorem RunsWithinUnder.size_state_le {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : A → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) (input : A) {state : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init input) state) (htrace : trace.Conforms allows) :
    Q.size R.state state ≤ (bound input).peakStateSize := by
  have := (h.cost_le input trace htrace).2.2.2.1
  simp only [executionCost, ExecutionCost.peakStateSize_add,
    ExecutionCost.peakStateSize_observe, ExecutionCost.ofWork] at this
  omega

/-- The final readout of a conforming prefix is encoded within the bound's peak readout size. -/
theorem RunsWithinUnder.size_head_le {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : A → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) (input : A) {state : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init input) state) (htrace : trace.Conforms allows) :
    Q.size bd.head (R.machine.head state) ≤ (bound input).peakHeadSize := by
  have := (h.cost_le input trace htrace).2.2.2.2
  simp only [executionCost, ExecutionCost.peakHeadSize_add,
    ExecutionCost.peakHeadSize_observe, ExecutionCost.ofWork] at this
  omega

/-- An allowed answer at a conformingly reachable query leads to a state within the peak state
size, and its encoded index is within the traffic bound. -/
theorem RunsWithinUnder.size_step_le {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : A → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) (input : A) {state : R.machine.State}
    (pre : R.ExecutionTrace (R.machine.init input) state) (hpre : pre.Conforms allows)
    {position : p.A} {next : p.B position → R.machine.State}
    (hview : R.machine.view state = Sum.inr ⟨position, next⟩) (direction : p.B position)
    (hallowed : allows position direction) :
    Q.size R.state (next direction) ≤ (bound input).peakStateSize ∧
      Q.size bd.idx ⟨position, direction⟩ ≤ (bound input).traffic := by
  let ext : R.ExecutionTrace (R.machine.init input) (next direction) :=
    pre.append (.query hview direction (.nil (next direction)))
  have hext : ext.Conforms allows :=
    (QuantitativeRealization.ExecutionTrace.conforms_append pre _).mpr ⟨hpre, hallowed, trivial⟩
  refine ⟨h.size_state_le input ext hext, ?_⟩
  have := (h.cost_le input ext hext).2.2.1
  simp only [ext, executionCost, ExecutionCost.traffic_add, ExecutionCost.traffic_observe,
    ExecutionCost.ofWork, QuantitativeRealization.ExecutionTrace.cost_append,
    QuantitativeRealization.ExecutionTrace.cost, ExecutionCost.query] at this
  omega

end DynSystem.DynComputation.QuantitativeRealization

end PFunctor
