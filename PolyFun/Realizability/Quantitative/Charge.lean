/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative
public import PolyFun.PFunctor.Dynamical.DynComputation.Charge
public import ToCslib.Algebra.Order.Hom.Multiples

/-!
# Interface charges on quantitative realizations

A quantitative realization charges the backend work of its machine (`ExecutionCost`), but it
never charges *answering* a query: answers come from the environment. Interface charges price
exactly those calls. This module connects the two accountings.

* `ExecutionTrace.charge c` prices the calls of an execution prefix, generalizing `length` (the
  unit charge, `length_eq_charge_one`) and `queryCount` (the indicator charge of one interface,
  `queryCount_eq_charge`).
* A charge bound on the machine bounds the charge of every execution prefix
  (`ExecutionTrace.charge_le_of_isChargeBound`), and a machine implementing a program family within
  budget is such a machine (`DynComputation.Implements.isChargeBound_init_iff`).
* A run bound bounds the program's charge by the query budget times the largest price
  (`RunsWithin.isChargeBound`).
* **The bridge.** If the machine implements a program family within budget `B`, and answering a
  call at `a` costs at most `π a ≤ φ (c a)` units of work for a monotone additive `φ`, then every
  conforming prefix costs at most the run bound plus `φ B` work, with the calls priced
  (`RunsWithin.executionCost_add_charge_le`).

The answering prices `π` are a bare function here: the theorem says which part of the total is
the machine's own work and which part is paid to the interface, and how the interface part is
bounded through the program's charge bound.
-/

@[expose] public section

universe u v w uω

namespace PFunctor

namespace DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {α β : Type u}
  {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq p.A] {Q : QuantitativeStepClass.{u, v, w} C}
  {bd : Boundary C p α β}

namespace QuantitativeRealization

namespace ExecutionTrace

variable {R : QuantitativeRealization Q bd} {ω : Type uω}

/-- The total charge of the calls of an execution prefix. -/
def charge [Add ω] [Zero ω] (c : p.A → ω) {start finish : R.machine.State} :
    ExecutionTrace R start finish → ω
  | .nil _ => 0
  | .query (position := position) _ _ tail => c position + tail.charge c

/-- The unit charge counts the calls. -/
theorem length_eq_charge_one {start finish : R.machine.State}
    (trace : ExecutionTrace R start finish) : trace.length = trace.charge (fun _ => (1 : ℕ)) := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih =>
    simp only [charge, length, ih]
    omega

/-- Counting the calls to one interface is its indicator charge. -/
theorem queryCount_eq_charge {label : Type*} [DecidableEq label] (labelOf : p.A → label)
    (interface : label) {start finish : R.machine.State} (trace : ExecutionTrace R start finish) :
    trace.queryCount labelOf interface =
      trace.charge (fun a => if labelOf a = interface then (1 : ℕ) else 0) := by
  induction trace with
  | nil => rfl
  | @query state position next finish view_eq direction tail ih =>
    simp only [queryCount, charge, ih]
    split <;> omega

/-- A charge bound on the machine bounds the charge of every execution prefix from that state. -/
theorem charge_le_of_isChargeBound [AddMonoid ω] [Preorder ω] {c : p.A → ω} {B s : ω}
    {start finish : R.machine.State} (trace : ExecutionTrace R start finish)
    (h : R.machine.IsChargeBound c B start s) : s + trace.charge c ≤ B := by
  induction trace generalizing s with
  | nil state =>
    have h0 := h 0
    rw [unroll_zero] at h0
    simp only [charge, add_zero]
    split at h0 <;> exact h0
  | @query state position next finish view_eq direction tail ih =>
    have hnext : R.machine.IsChargeBound c B (next direction) (s + c position) := fun k => by
      have hk := h (k + 1)
      rw [unroll_query_succ _ k state position next view_eq] at hk
      exact hk.2 direction
    have := ih hnext
    rwa [charge, ← add_assoc]

end ExecutionTrace

variable {R : QuantitativeRealization Q bd} {ω : Type uω} [AddMonoid ω] [Preorder ω]
  [AddLeftMono ω] [AddRightMono ω] [CanonicallyOrderedAdd ω]

/-- A run bound bounds the charge of the implemented programs by the query budget times the
largest price. -/
theorem RunsWithin.isChargeBound {bound : α → ExecutionCost} {program : α → FreeM p β}
    (h : R.RunsWithin bound) (implements : R.machine.Implements program) {c : p.A → ω} {K : ω}
    (hc : ∀ a, c a ≤ K) (input : α) :
    (program input).IsChargeBound c ((bound input).queries • K) := by
  have hunit := (FreeM.isChargeBound_one_iff_isTotalRollBound _ _).2
    (h.isTotalRollBound implements input)
  have hK := hunit.map (OrderAddMonoidHom.multiples K zero_le)
  rw [map_zero] at hK
  refine hK.mono_charge fun a => ?_
  change c a ≤ (1 : ℕ) • K
  rw [one_nsmul]
  exact hc a

omit [AddLeftMono ω] [AddRightMono ω] [CanonicallyOrderedAdd ω] in
/-- **The bridge to backend cost.** If the machine of a realization implements a program family
within budget `B` under `c`, and answering a call at `a` costs at most `π a ≤ φ (c a)` units of
work, then every conforming execution prefix, with its calls paid for, costs at most the run bound
plus `φ B` work. -/
theorem RunsWithinUnder.executionCost_add_charge_le {allows : ∀ position, p.B position → Prop}
    {bound : α → ExecutionCost} {program : α → FreeM p β} (h : R.RunsWithinUnder allows bound)
    (implements : R.machine.Implements program) {c : p.A → ω} {B : ω}
    (hprogram : ∀ input, (program input).IsChargeBound c B) (π : p.A → ℕ) (φ : ω →+o ℕ)
    (hπ : ∀ a, π a ≤ φ (c a)) (input : α) {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init input) finish) (conforms : trace.Conforms allows) :
    R.executionCost input trace + ExecutionCost.ofWork (trace.charge π) ≤
      bound input + ExecutionCost.ofWork (φ B) := by
  refine add_le_add (h.1 input trace conforms) ?_
  have hφ := (hprogram input).map φ
  rw [map_zero] at hφ
  have hπ' : (program input).IsChargeBound π (φ B) := hφ.mono_charge hπ
  have hmachine := (implements.isChargeBound_init_iff input).2 hπ'
  have htrace := trace.charge_le_of_isChargeBound hmachine
  rw [zero_add] at htrace
  exact ⟨htrace, le_rfl, le_rfl, le_rfl, le_rfl⟩

end QuantitativeRealization

end DynSystem.DynComputation

end PFunctor
