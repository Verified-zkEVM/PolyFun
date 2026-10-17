/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Closure
public import PolyFun.Realizability.Quantitative.Simulation

/-!
# Changing local work charges

`recost` retains representations, codes and semantic functions while changing the local work
charge. The same machine implements the same programs and has the same traces, query counts,
traffic and peak sizes. Only work changes. Transporting work bounds requires a comparison of
the old and new charges; arbitrary recosting does not preserve a run bound.

The recosted backend carries the original structural code (`HasComposition`, `HasProd`,
`HasSum`, `HasOption`, `IsDistributive`), so composite realizations recost part by part
(`QuantitativeRealization.seqComp_recost`). A pointwise decrease of charges is also a
simulation (`SimulatedBy.ofRecostLE`).
-/

public section

universe u v w

open PFunctor

namespace PFunctor.QuantitativeStepClass

variable {C : StepClass.{u, v}} (Q : QuantitativeStepClass.{u, v, w} C)

/-- Replace the cost function of a backend. Realizers, sizes and admissibility are untouched. -/
@[expose] def recost
    (cost' : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}, Q.Realizer a b f → A → ℕ) :
    QuantitativeStepClass.{u, v, w} C where
  Realizer := Q.Realizer
  size := Q.size
  cost := cost'
  admissible := Q.admissible

variable {Q}
  {cost' : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}, Q.Realizer a b f → A → ℕ}

@[simp] theorem recost_Realizer {A B : Type u} (a : C.Str A) (b : C.Str B) (f : A → B) :
    (Q.recost cost').Realizer a b f = Q.Realizer a b f := rfl

@[simp] theorem recost_size {A : Type u} (a : C.Str A) (x : A) :
    (Q.recost cost').size a x = Q.size a x := rfl

@[simp] theorem recost_cost {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}
    (r : Q.Realizer a b f) (x : A) : (Q.recost cost').cost r x = cost' r x := rfl

/-! ## Structure carried by a recosted backend -/

/-- The original identity and composition code, under the new charges. The new charges are
arbitrary, so the only generic connection overhead is the composite's own new charge. -/
instance [Q.HasComposition] : (Q.recost cost').HasComposition where
  identity a := Q.identity a
  compose r s := Q.compose r s
  composeOverhead r s x := cost' (Q.compose r s) x
  cost_compose_le _ _ _ := Nat.le_add_left _ _

/-- The original product code. -/
instance [C.HasProd] [QP : Q.HasProd] : (Q.recost cost').HasProd where
  fst := QP.fst
  snd := QP.snd
  pair := QP.pair

/-- The original sum code. -/
instance [C.HasSum] [QS : Q.HasSum] : (Q.recost cost').HasSum where
  inl := QS.inl
  inr := QS.inr
  elim := QS.elim

/-- The original optional-value code. -/
instance [C.HasProd] [C.HasOption] [QO : Q.HasOption] : (Q.recost cost').HasOption where
  map := QO.map
  none := QO.none
  bindContext := QO.bindContext
  some := QO.some

/-- The original distributivity code. -/
instance [C.HasProd] [C.HasSum] [QD : Q.IsDistributive] : (Q.recost cost').IsDistributive where
  distribute := QD.distribute

/-! ## Recosting as a simulation -/

/-- A pointwise decrease of local charges is a simulation of the original backend by the
recosted one, along the identity on representations. It transports `PolyRealizer`s but no run
bounds; `QuantitativeRealization.runsWithinUnder_recost` transports those. -/
noncomputable def SimulatedBy.ofRecostLE
    (hle : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}
      (r : Q.Realizer a b f) (x : A), cost' r x ≤ Q.cost r x) :
    Q.SimulatedBy (Q.recost cost') (fun a ↦ a) where
  code r := r
  sizeBound := Polynomial.X
  size_le _ _ := by simp
  sizeLower := Polynomial.X
  size_ge _ _ := by simp
  costBound _ := Polynomial.X
  cost_le r x := by
    simp only [Polynomial.eval_X, recost_cost]
    exact (hle r x).trans (Nat.le_add_left _ _)

end PFunctor.QuantitativeStepClass

namespace PFunctor.DynSystem.DynComputation.QuantitativeRealization

open PFunctor.DynSystem.DynComputation

variable {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{u, v, w} C} {p : PFunctor.{u, u}} [DecidableEq p.A]
  {α β : Type u} {bd : Boundary C p α β}
  (cost' : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}, Q.Realizer a b f → A → ℕ)

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

/-- Recosting commutes with sequential composition: neither the machine nor any code changes,
and the recosted backend carries the original structural code. -/
theorem seqComp_recost [Q.HasComposition] [Q.HasProd] [Q.HasSum] [Q.HasOption]
    [Q.IsDistributive] {D : Type u} {outRep : C.Str D} (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) :
    (R₁.seqComp R₂).recost cost' = (R₁.recost cost').seqComp (R₂.recost cost') :=
  rfl

/-- Transport a trace to the recosted realization; the constructors are definitionally the same
because the machine is. -/
@[expose] def ExecutionTrace.recost {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (R.recost cost').ExecutionTrace start finish := trace

@[simp] theorem ExecutionTrace.length_recost {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := cost')).length = trace.length := rfl

theorem ExecutionTrace.cost_recost_queries {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := cost')).cost.queries = trace.cost.queries := by
  induction trace with
  | nil => rfl
  | query _ _ tail ih =>
      simp only [ExecutionTrace.recost] at ih
      simp only [ExecutionTrace.recost, ExecutionTrace.cost, ExecutionCost.queries_add,
        ExecutionCost.queries_ofWork, ExecutionCost.queries_observe, ExecutionCost.queries_query,
        ih]

theorem ExecutionTrace.cost_recost_traffic {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := cost')).cost.traffic = trace.cost.traffic := by
  induction trace with
  | nil => rfl
  | query _ _ tail ih =>
      simp only [ExecutionTrace.recost] at ih
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
      simp only [ExecutionTrace.recost] at ih
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
      simp only [ExecutionTrace.recost] at ih
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

/-- Only work moves: under the zero charge every prefix charges zero work. -/
theorem ExecutionTrace.cost_recost_zero_work {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := fun _ _ ↦ 0)).cost.work = 0 := by
  induction trace with
  | nil => rfl
  | query _ _ tail ih =>
      simp only [ExecutionTrace.recost] at ih
      simp only [ExecutionTrace.recost, ExecutionTrace.cost, ExecutionCost.work_add,
        ExecutionCost.work_ofWork, ExecutionCost.work_observe, ExecutionCost.work_query,
        recost_headCode, recost_updateCode, ih]
      all_goals rfl

theorem executionCost_recost_zero_work :
    ((R.recost fun _ _ ↦ 0).executionCost input
      (recostTrace (cost' := fun _ _ ↦ 0) R input trace)).work = 0 := by
  have h : (recostTrace (cost' := fun _ _ ↦ 0) R input trace).cost.work = 0 :=
    ExecutionTrace.cost_recost_zero_work trace
  simp only [executionCost, ExecutionCost.work_add, ExecutionCost.work_ofWork,
    ExecutionCost.work_observe, recost_initCode,
    recost_headCode, h]
  all_goals rfl

/-- Restore the original charge annotations on a trace. -/
@[expose] def ExecutionTrace.restore {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : (R.recost cost').ExecutionTrace start finish) :
    R.ExecutionTrace start finish := trace

@[simp] theorem ExecutionTrace.recost_restore {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State}
    (trace : (R.recost cost').ExecutionTrace start finish) :
    (trace.restore (R := R)).recost (cost' := cost') = trace := rfl

/-- Recosting preserves the set of allowed response prefixes. -/
@[simp] theorem ExecutionTrace.conforms_recost {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish)
    (allows : ∀ position, p.B position → Prop) :
    (trace.recost (cost' := cost')).Conforms allows ↔ trace.Conforms allows := Iff.rfl

/-- Restoring charge annotations preserves allowed response prefixes. -/
@[simp] theorem ExecutionTrace.conforms_restore {R : QuantitativeRealization Q bd}
    {start finish : R.machine.State}
    (trace : (R.recost cost').ExecutionTrace start finish)
    (allows : ∀ position, p.B position → Prop) :
    (trace.restore (R := R)).Conforms allows ↔ trace.Conforms allows := Iff.rfl

/-- Pointwise smaller local charges give smaller prefix work. -/
theorem ExecutionTrace.work_recost_le {R : QuantitativeRealization Q bd}
    (hle : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}
      (r : Q.Realizer a b f) (x : A), cost' r x ≤ Q.cost r x)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.recost (cost' := cost')).cost.work ≤ trace.cost.work := by
  induction trace with
  | nil => exact le_rfl
  | @query state position next finish view_eq direction tail ih =>
      simp only [ExecutionTrace.recost, ExecutionTrace.cost, ExecutionCost.work_add,
        ExecutionCost.work_ofWork, ExecutionCost.work_observe, ExecutionCost.work_query]
      have hh := hle R.headCode state
      have hu := hle R.updateCode (state, ⟨position, direction⟩)
      change cost' R.headCode state +
        cost' R.updateCode (state, ⟨position, direction⟩) + 0 + 0 +
        (ExecutionTrace.recost (R := R) (cost' := cost') tail).cost.work ≤ _
      omega

/-- Pointwise smaller local charges preserve the whole resource inequality. -/
theorem executionCost_recost_le
    (hle : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}
      (r : Q.Realizer a b f) (x : A), cost' r x ≤ Q.cost r x) :
    (R.recost cost').executionCost input (recostTrace R input trace) ≤
      R.executionCost input trace := by
  refine ⟨?_, (executionCost_recost_queries R input trace).le,
    (executionCost_recost_traffic R input trace).le,
    (executionCost_recost_peakStateSize R input trace).le,
    (executionCost_recost_peakHeadSize R input trace).le⟩
  have ht := trace.work_recost_le hle
  have hi := hle R.initCode input
  have hh := hle R.headCode finish
  simp only [executionCost, ExecutionCost.work_add, ExecutionCost.work_ofWork,
    ExecutionCost.work_observe]
  change cost' R.initCode input + 0 +
    (trace.recost (cost' := cost')).cost.work + cost' R.headCode finish ≤ _
  omega

/-- A run bound survives a decrease of local work charges, including the zero charge. -/
theorem runsWithinUnder_recost {allows : ∀ position, p.B position → Prop}
    {bound : α → ExecutionCost} (h : R.RunsWithinUnder allows bound)
    (hle : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B}
      (r : Q.Realizer a b f) (x : A), cost' r x ≤ Q.cost r x) :
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
