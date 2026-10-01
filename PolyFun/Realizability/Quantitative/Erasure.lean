/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative

/-!
# Changing local work charges

`recost` retains representations, codes and semantic functions while changing the local work
charge. The same machine implements the same programs and has the same traces, query counts,
traffic and peak sizes. Only work changes. Transporting work bounds requires a comparison of
the old and new charges; arbitrary recosting does not preserve a run bound.
-/

public section

universe u v w

open PFunctor

namespace PFunctor.QuantitativeStepClass

variable {C : StepClass.{u, v}} (Q : QuantitativeStepClass.{u, v, w} C)

/-- Replace the cost function of a backend. Realizers, sizes and admissibility are untouched. -/
@[expose] def recost
    (cost' : ∀ (A B : Type u) (a : C.Str A) (b : C.Str B) (f : A → B), Q.Realizer a b f → A → ℕ) :
    QuantitativeStepClass.{u, v, w} C where
  Realizer := Q.Realizer
  size := Q.size
  cost := @fun A B a b f r x ↦ cost' A B a b f r x
  admissible := Q.admissible

/-- Cost erasure: every realizer costs zero. -/
@[expose] def erase : QuantitativeStepClass.{u, v, w} C := Q.recost fun _ _ _ _ _ _ _ ↦ 0

variable {Q}
  {cost' : ∀ (A B : Type u) (a : C.Str A) (b : C.Str B) (f : A → B), Q.Realizer a b f → A → ℕ}

@[simp] theorem recost_Realizer {A B : Type u} (a : C.Str A) (b : C.Str B) (f : A → B) :
    (Q.recost cost').Realizer a b f = Q.Realizer a b f := rfl

@[simp] theorem recost_size {A : Type u} (a : C.Str A) (x : A) :
    (Q.recost cost').size a x = Q.size a x := rfl

@[simp] theorem recost_cost {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}
    (r : Q.Realizer a b f) (x : A) : (Q.recost cost').cost r x = cost' A B a b f r x := rfl

end PFunctor.QuantitativeStepClass

namespace PFunctor.DynSystem.DynComputation.QuantitativeRealization

open PFunctor.DynSystem.DynComputation

variable {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{u, v, w} C} {p : PFunctor.{u, u}} [DecidableEq p.A]
  {α β : Type u} {bd : Boundary C p α β}
  (cost' : ∀ (A B : Type u) (a : C.Str A) (b : C.Str B) (f : A → B), Q.Realizer a b f → A → ℕ)

/-- The same realization over the recosted backend: same machine, state, and codes. -/
@[expose] def recost (R : QuantitativeRealization Q bd) :
    QuantitativeRealization (Q.recost cost') bd where
  machine := R.machine
  state := R.state
  initCode := R.initCode
  headCode := R.headCode
  updateCode := R.updateCode

variable {cost'}

@[simp] theorem recost_machine (R : QuantitativeRealization Q bd) :
    (R.recost cost').machine = R.machine := rfl

@[simp] theorem recost_state (R : QuantitativeRealization Q bd) :
    (R.recost cost').state = R.state := rfl

@[simp] theorem recost_initCode (R : QuantitativeRealization Q bd) :
    (R.recost cost').initCode = R.initCode := rfl

@[simp] theorem recost_headCode (R : QuantitativeRealization Q bd) :
    (R.recost cost').headCode = R.headCode := rfl

@[simp] theorem recost_updateCode (R : QuantitativeRealization Q bd) :
    (R.recost cost').updateCode = R.updateCode := rfl

/-- Semantic correctness does not see the cost function. -/
theorem recost_implements (R : QuantitativeRealization Q bd) (program : α → FreeM p β) :
    (R.recost cost').machine.Implements program ↔ R.machine.Implements program :=
  Iff.rfl

/-- Transport a trace to the recosted realization; the constructors are definitionally the same
because the machine is. -/
@[expose] def ExecutionTrace.recost {R : QuantitativeRealization Q bd} :
    ∀ {start finish : R.machine.State},
      R.ExecutionTrace start finish → (R.recost cost').ExecutionTrace start finish
  | _, _, .nil state => ExecutionTrace.nil (R := R.recost cost') state
  | _, _, .query view_eq direction tail =>
      ExecutionTrace.query (R := R.recost cost') view_eq direction (ExecutionTrace.recost tail)

@[simp] theorem ExecutionTrace.length_recost {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := cost')).length = trace.length := by
  induction trace with
  | nil => simp [ExecutionTrace.recost, ExecutionTrace.length]
  | query _ _ tail ih => simp [ExecutionTrace.recost, ExecutionTrace.length, ih]

theorem ExecutionTrace.cost_recost_queries {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := cost')).cost.queries = trace.cost.queries := by
  induction trace with
  | nil => rfl
  | query _ _ tail ih =>
      simp only [ExecutionTrace.recost, ExecutionTrace.cost, ExecutionCost.queries_add,
        ExecutionCost.queries_ofWork, ExecutionCost.queries_observe, ExecutionCost.queries_query,
        ih]

theorem ExecutionTrace.cost_recost_traffic {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := cost')).cost.traffic = trace.cost.traffic := by
  induction trace with
  | nil => rfl
  | query _ _ tail ih =>
      simp only [ExecutionTrace.recost, ExecutionTrace.cost, ExecutionCost.traffic_add,
        ExecutionCost.traffic_ofWork, ExecutionCost.traffic_observe, ExecutionCost.traffic_query,
        QuantitativeStepClass.recost_size,
        recost_state, recost_headCode, recost_updateCode, ih]
      all_goals rfl

theorem ExecutionTrace.cost_recost_peakStateSize {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := cost')).cost.peakStateSize = trace.cost.peakStateSize := by
  induction trace with
  | nil => rfl
  | query _ _ tail ih =>
      simp only [ExecutionTrace.recost, ExecutionTrace.cost, ExecutionCost.peakStateSize_add,
        ExecutionCost.peakStateSize_observe, ExecutionCost.ofWork, ExecutionCost.query,
        QuantitativeStepClass.recost_size,
        recost_state, recost_headCode, recost_updateCode, ih]
      all_goals rfl

theorem ExecutionTrace.cost_recost_peakHeadSize {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := cost')).cost.peakHeadSize = trace.cost.peakHeadSize := by
  induction trace with
  | nil => rfl
  | query _ _ tail ih =>
      simp only [ExecutionTrace.recost, ExecutionTrace.cost, ExecutionCost.peakHeadSize_add,
        ExecutionCost.peakHeadSize_observe, ExecutionCost.ofWork, ExecutionCost.query,
        QuantitativeStepClass.recost_size,
        recost_state, recost_headCode, recost_updateCode, ih]
      all_goals rfl

variable (R : QuantitativeRealization Q bd) (input : α) {finish : R.machine.State}
  (trace : R.ExecutionTrace (R.machine.init input) finish)

/-- The transported trace, ascribed to the recosted realization's own initial state so that
component lemmas match syntactically. -/
abbrev recostTrace : (R.recost cost').ExecutionTrace ((R.recost cost').machine.init input) finish :=
  trace.recost (cost' := cost')

/-- Visible queries do not see the cost function. -/
theorem executionCost_recost_queries :
    ((R.recost cost').executionCost input (recostTrace R input trace)).queries =
      (R.executionCost input trace).queries := by
  have h : (recostTrace (cost' := cost') R input trace).cost.queries = trace.cost.queries :=
    ExecutionTrace.cost_recost_queries trace
  simp only [executionCost, ExecutionCost.queries_add, ExecutionCost.queries_ofWork,
    ExecutionCost.queries_observe, h]

/-- Boundary traffic does not see the cost function. -/
theorem executionCost_recost_traffic :
    ((R.recost cost').executionCost input (recostTrace R input trace)).traffic =
      (R.executionCost input trace).traffic := by
  have h : (recostTrace (cost' := cost') R input trace).cost.traffic = trace.cost.traffic :=
    ExecutionTrace.cost_recost_traffic trace
  simp only [executionCost, ExecutionCost.traffic_add, ExecutionCost.traffic_ofWork,
    ExecutionCost.traffic_observe, h]

/-- Peak state size does not see the cost function. -/
theorem executionCost_recost_peakStateSize :
    ((R.recost cost').executionCost input (recostTrace R input trace)).peakStateSize =
      (R.executionCost input trace).peakStateSize := by
  have h : (recostTrace (cost' := cost') R input trace).cost.peakStateSize =
      trace.cost.peakStateSize :=
    ExecutionTrace.cost_recost_peakStateSize trace
  simp only [executionCost, ExecutionCost.peakStateSize_add, ExecutionCost.peakStateSize_observe,
    ExecutionCost.ofWork, h]
  all_goals rfl

/-- Peak head size does not see the cost function. -/
theorem executionCost_recost_peakHeadSize :
    ((R.recost cost').executionCost input (recostTrace R input trace)).peakHeadSize =
      (R.executionCost input trace).peakHeadSize := by
  have h : (recostTrace (cost' := cost') R input trace).cost.peakHeadSize =
      trace.cost.peakHeadSize :=
    ExecutionTrace.cost_recost_peakHeadSize trace
  simp only [executionCost, ExecutionCost.peakHeadSize_add, ExecutionCost.peakHeadSize_observe,
    ExecutionCost.ofWork, h]
  all_goals rfl

/-- Only work moves: under erasure every prefix charges zero work. -/
theorem ExecutionTrace.cost_erase_work {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := fun _ _ _ _ _ _ _ ↦ 0)).cost.work = 0 := by
  induction trace with
  | nil => rfl
  | query _ _ tail ih =>
      simp only [ExecutionTrace.recost, ExecutionTrace.cost, ExecutionCost.work_add,
        ExecutionCost.work_ofWork, ExecutionCost.work_observe, ExecutionCost.work_query,
        recost_headCode, recost_updateCode, ih]
      all_goals rfl

theorem executionCost_erase_work :
    ((R.recost fun _ _ _ _ _ _ _ ↦ 0).executionCost input
      (recostTrace (cost' := fun _ _ _ _ _ _ _ ↦ 0) R input trace)).work = 0 := by
  have h : (recostTrace (cost' := fun _ _ _ _ _ _ _ ↦ 0) R input trace).cost.work = 0 :=
    ExecutionTrace.cost_erase_work trace
  simp only [executionCost, ExecutionCost.work_add, ExecutionCost.work_ofWork,
    ExecutionCost.work_observe, recost_initCode,
    recost_headCode, h]
  all_goals rfl

/-- Restore the original charge annotations on a trace. -/
@[expose] def ExecutionTrace.restore {R : QuantitativeRealization Q bd} :
    ∀ {start finish : R.machine.State},
      (R.recost cost').ExecutionTrace start finish → R.ExecutionTrace start finish
  | _, _, .nil state => ExecutionTrace.nil (R := R) state
  | _, _, .query view_eq direction tail =>
      ExecutionTrace.query (R := R) view_eq direction (ExecutionTrace.restore (R := R) tail)

@[simp] theorem ExecutionTrace.recost_restore {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State}
    (trace : (R.recost cost').ExecutionTrace start finish) :
    (trace.restore (R := R)).recost (cost' := cost') = trace := by
  induction trace using ExecutionTrace.rec (R := R.recost cost') with
  | nil => rfl
  | query _ _ tail ih => simp only [restore, recost, ih]

/-- Recosting preserves the set of allowed response prefixes. -/
@[simp] theorem ExecutionTrace.conforms_recost {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish)
    (allows : ∀ position, p.B position → Prop) :
    (trace.recost (cost' := cost')).Conforms allows ↔ trace.Conforms allows := by
  induction trace with
  | nil => rfl
  | query _ _ tail ih => simp only [recost, Conforms, ih]

/-- Restoring charge annotations preserves allowed response prefixes. -/
@[simp] theorem ExecutionTrace.conforms_restore {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State}
    (trace : (R.recost cost').ExecutionTrace start finish)
    (allows : ∀ position, p.B position → Prop) :
    (trace.restore (R := R)).Conforms allows ↔ trace.Conforms allows := by
  induction trace using ExecutionTrace.rec (R := R.recost cost') with
  | nil => rfl
  | query _ _ tail ih => simp only [restore, Conforms, ih]

/-- Pointwise smaller local charges give smaller prefix work. -/
theorem ExecutionTrace.work_recost_le {R : QuantitativeRealization Q bd}
    (hle : ∀ (A B : Type u) (a : C.Str A) (b : C.Str B) (f : A → B)
      (r : Q.Realizer a b f) (x : A), cost' A B a b f r x ≤ Q.cost r x)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := cost')).cost.work ≤ trace.cost.work := by
  induction trace with
  | nil => exact le_rfl
  | @query state position next finish view_eq direction tail ih =>
      simp only [ExecutionTrace.recost, ExecutionTrace.cost, ExecutionCost.work_add,
        ExecutionCost.work_ofWork, ExecutionCost.work_observe, ExecutionCost.work_query]
      have hh := hle _ _ _ _ _ R.headCode state
      have hu := hle _ _ _ _ _ R.updateCode (state, ⟨position, direction⟩)
      change cost' _ _ _ _ _ R.headCode state +
        cost' _ _ _ _ _ R.updateCode (state, ⟨position, direction⟩) + 0 + 0 +
        (tail.recost (cost' := cost')).cost.work ≤ _
      omega

/-- Pointwise smaller local charges preserve the whole resource inequality. -/
theorem executionCost_recost_le
    (hle : ∀ (A B : Type u) (a : C.Str A) (b : C.Str B) (f : A → B)
      (r : Q.Realizer a b f) (x : A), cost' A B a b f r x ≤ Q.cost r x) :
    (R.recost cost').executionCost input (recostTrace R input trace) ≤
      R.executionCost input trace := by
  refine ⟨?_, (executionCost_recost_queries R input trace).le,
    (executionCost_recost_traffic R input trace).le,
    (executionCost_recost_peakStateSize R input trace).le,
    (executionCost_recost_peakHeadSize R input trace).le⟩
  have ht := trace.work_recost_le hle
  have hi := hle _ _ _ _ _ R.initCode input
  have hh := hle _ _ _ _ _ R.headCode finish
  simp only [executionCost, ExecutionCost.work_add, ExecutionCost.work_ofWork,
    ExecutionCost.work_observe]
  change cost' _ _ _ _ _ R.initCode input + 0 +
    (trace.recost (cost' := cost')).cost.work + cost' _ _ _ _ _ R.headCode finish ≤ _
  omega

/-- A run bound survives a decrease of local work charges, including cost erasure. -/
theorem runsWithinUnder_recost {allows : ∀ position, p.B position → Prop}
    {bound : α → ExecutionCost} (h : R.RunsWithinUnder allows bound)
    (hle : ∀ (A B : Type u) (a : C.Str A) (b : C.Str B) (f : A → B)
      (r : Q.Realizer a b f) (x : A), cost' A B a b f r x ≤ Q.cost r x) :
    (R.recost cost').RunsWithinUnder allows bound := by
  refine ⟨?_, h.2.1, ?_⟩
  · intro value last t ht
    have hs : (t.restore (R := R)).Conforms allows :=
      (ExecutionTrace.conforms_restore (R := R) t allows).mpr ht
    have hb := (executionCost_recost_le R value (t.restore (R := R)) hle).trans
      (h.1 value (t.restore (R := R)) hs)
    have heq := ExecutionTrace.recost_restore (R := R) (cost' := cost') t
    change (R.recost cost').executionCost value
      ((t.restore (R := R)).recost (cost' := cost')) ≤ bound value at hb
    rw [heq] at hb
    exact hb
  · intro value last t ht position next hv
    exact h.2.2 value (t.restore (R := R))
      ((ExecutionTrace.conforms_restore (R := R) t allows).mpr ht) hv

end PFunctor.DynSystem.DynComputation.QuantitativeRealization
