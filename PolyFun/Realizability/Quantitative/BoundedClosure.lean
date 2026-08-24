/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Closure

/-!
# Bounded closure for quantitative realizations

This file supplies resource-aware closure principles for quantitative realizations. The control
flow lemmas are independent of any asymptotic interpretation: traces are transported through
constructors only when their visible query dynamics really agree. Backend work that changes under
a constructor is either derived from a quantitative backend law or exposed as an explicit,
pathwise overhead obligation.

`RankedRunCertificate` is a reusable termination and progress certificate. Its rank decreases on
every allowed answer, and its progress field ensures that a pending query has an allowed answer.
Together these conditions rule out both infinite allowed paths and vacuous resolution at a query
whose allowed response set is empty.

Bounded sequential composition remains a separate construction. An honest theorem needs a
dependent phase decomposition for composite traces: a left prefix may stop before handoff, while
a returned first phase exposes the second phase's initial view immediately and its first query
transitions directly into the right state. Only after that decomposition can a uniform
second-phase bound and the assembled backend-code overhead be combined without choosing a
pointwise second-phase witness.
-/

@[expose] public section

universe u v w

namespace PFunctor

namespace DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}} [C.HasProd]
  [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {A B : Type u}
  {bd : Boundary C p A B}

/-! ## Rank certificates -/

/-- A global, answer-relation-relative certificate for query termination and progress.

The rank is attached to machine states, not semantic oracle executions. Every allowed response
strictly decreases it. `returns_of_rank_zero` prevents a zero-ranked query, while `progress`
prevents a pending query from satisfying the universal decrease condition vacuously because no
answer is allowed. -/
structure RankedRunCertificate (R : QuantitativeRealization Q bd)
    (allows : ∀ position, p.B position → Prop) where
  /-- Natural-valued potential remaining at a hidden machine state. -/
  rank : R.machine.State → ℕ
  /-- A zero-ranked state has already returned. -/
  returns_of_rank_zero : ∀ state, rank state = 0 →
    ∃ value, R.machine.view state = Sum.inl value
  /-- Every admitted response strictly decreases the potential. -/
  decreases : ∀ {state position next},
    R.machine.view state = Sum.inr ⟨position, next⟩ →
      ∀ direction, allows position direction → rank (next direction) < rank state
  /-- Every pending query admits at least one response under the contract. -/
  progress : ∀ {state position next},
    R.machine.view state = Sum.inr ⟨position, next⟩ →
      ∃ direction, allows position direction

namespace RankedRunCertificate

variable {R : QuantitativeRealization Q bd}
  {allows : ∀ position, p.B position → Prop}

/-- A rank certificate proves relation-restricted resolution with the state's rank as fuel. -/
theorem resolvesInUnder (certificate : RankedRunCertificate R allows)
    (state : R.machine.State) :
    R.machine.ResolvesInUnder allows (certificate.rank state) state := by
  generalize hrank : certificate.rank state = rank
  induction rank using Nat.strong_induction_on generalizing state with
  | h rank ih =>
      cases rank with
      | zero =>
          obtain ⟨value, hview⟩ := certificate.returns_of_rank_zero state hrank
          exact R.machine.resolvesInUnder_return allows 0 state value hview
      | succ rank =>
          cases hview : R.machine.view state with
          | inl value =>
              exact R.machine.resolvesInUnder_return allows (rank + 1) state value hview
          | inr query =>
              rcases query with ⟨position, next⟩
              rw [R.machine.resolvesInUnder_query_succ_iff allows rank state position next hview]
              intro direction hAllows
              apply (ih (certificate.rank (next direction)) ?_ (next direction) rfl).mono
              · simpa [hrank] using certificate.decreases hview direction hAllows
              · have := certificate.decreases hview direction hAllows
                omega

/-- A global rank certificate supplies syntactic progress from every input. -/
theorem traceProgressUnder (certificate : RankedRunCertificate R allows) (input : A) :
    R.TraceProgressUnder allows input := by
  intro state trace htrace position next hview
  exact certificate.progress hview

/-- Combine a rank certificate with an honest pathwise cost proof.

The rank bound and cost bound are separate on purpose: a decreasing query potential does not say
anything about backend work, traffic, or representation sizes. -/
theorem runsWithinUnder (certificate : RankedRunCertificate R allows)
    (bound : A → ExecutionCost)
    (cost_le : ∀ input {finish : R.machine.State}
      (trace : R.ExecutionTrace (R.machine.init input) finish),
      trace.Conforms allows → R.executionCost input trace ≤ bound input)
    (rank_init_le : ∀ input, certificate.rank (R.machine.init input) ≤
      (bound input).queries) :
    R.RunsWithinUnder allows bound :=
  ⟨cost_le,
    fun input ↦ (certificate.resolvesInUnder (R.machine.init input)).mono (rank_init_le input),
    certificate.traceProgressUnder⟩

end RankedRunCertificate

/-! ## Initialization replacement -/

omit [DecidableEq p.A] in
/-- Replacing only a computation's initialization leaves relation-restricted resolution from an
already selected state unchanged. -/
theorem resolvesInUnder_setInit_iff (M : DynComputation.{u} p A B)
    (allows : ∀ position, p.B position → Prop) {D : Type u}
    (init : D → M.State) (k : ℕ) (state : M.State) :
    (M.setInit init).ResolvesInUnder allows k state ↔
      M.ResolvesInUnder allows k state := by
  induction k generalizing state with
  | zero =>
      cases hview : M.view state <;>
        simp [ResolvesInUnder, DynComputation.setInit_view, hview]
  | succ k ih =>
      cases hview : M.view state with
      | inl value =>
          simp [ResolvesInUnder, DynComputation.setInit_view, hview]
      | inr query =>
          rcases query with ⟨position, next⟩
          simp only [ResolvesInUnder, DynComputation.setInit_view, hview]
          exact forall_congr' fun direction ↦
            imp_congr_right fun _ ↦ ih (next direction)

/-! ## Input precomposition -/

section Precomp

variable [Q.HasCategory] {D : Type u} {inputRep : C.Str D} {f : D → A}

namespace QuantitativeRealization.ExecutionTrace

/-- Regard a source trace as a trace of an input-precomposed realization.

Precomposition changes only initialization, so hidden states, views, and transitions are shared
definitionally. -/
def toPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) :
    (R.precomp code).ExecutionTrace start finish :=
  match trace with
  | .nil state => .nil (R := R.precomp code) state
  | .query view_eq direction tail =>
      .query (R := R.precomp code) view_eq direction (toPrecomp R code tail)

/-- Forget the changed initialization of an input-precomposed trace. -/
def ofPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : (R.precomp code).ExecutionTrace start finish) :
    R.ExecutionTrace start finish :=
  match trace with
  | .nil state => .nil (R := R) state
  | .query view_eq direction tail =>
      .query (R := R) view_eq direction (ofPrecomp R code tail)

@[simp] theorem ofPrecomp_toPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) :
    (trace.toPrecomp R code).ofPrecomp R code = trace := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih => simp [toPrecomp, ofPrecomp, ih]

@[simp] theorem toPrecomp_ofPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : (R.precomp code).ExecutionTrace start finish) :
    (trace.ofPrecomp R code).toPrecomp R code = trace :=
  match trace with
  | .nil _ => rfl
  | .query _ _ tail => by
      simp only [ofPrecomp, toPrecomp]
      rw [toPrecomp_ofPrecomp R code tail]

@[simp] theorem conforms_toPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f)
    (allows : ∀ position, p.B position → Prop)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.toPrecomp R code).Conforms allows ↔ trace.Conforms allows := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih => simp [toPrecomp, Conforms, ih]

@[simp] theorem conforms_ofPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f)
    (allows : ∀ position, p.B position → Prop)
    {start finish : R.machine.State}
    (trace : (R.precomp code).ExecutionTrace start finish) :
    (trace.ofPrecomp R code).Conforms allows ↔ trace.Conforms allows := by
  rw [← conforms_toPrecomp R code allows (trace.ofPrecomp R code),
    toPrecomp_ofPrecomp]

@[simp] theorem cost_toPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) :
    (trace.toPrecomp R code).cost = trace.cost := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih =>
      rename_i current position next finish
      simp only [toPrecomp, cost]
      rw [R.cost_headCode_precomp code current,
        R.cost_updateCode_precomp code (current, ⟨position, direction⟩),
        R.size_state_precomp code current]
      simp only [Boundary.withInput_head]
      rw [R.size_head_precomp code current, ih]
      rfl

@[simp] theorem cost_ofPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : (R.precomp code).ExecutionTrace start finish) :
    (trace.ofPrecomp R code).cost = trace.cost := by
  rw [← cost_toPrecomp R code (trace.ofPrecomp R code), toPrecomp_ofPrecomp]

@[simp] theorem length_toPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) :
    (trace.toPrecomp R code).length = trace.length := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih => simp [toPrecomp, length, ih]

end QuantitativeRealization.ExecutionTrace

/-- The only additional resource charged by input precomposition is the executable input map and
the backend's certified composition overhead. -/
theorem QuantitativeRealization.executionCost_toPrecomp_le
    (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) (input : D)
    {finish : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init (f input)) finish) :
    (R.precomp code).executionCost input (trace.toPrecomp R code) ≤
      ExecutionCost.ofWork
          (Q.cost code input + Q.composeOverhead code R.initCode input) +
        R.executionCost (f input) trace := by
  have hinit := R.cost_initCode_precomp_le code input
  have hcost := QuantitativeRealization.ExecutionTrace.cost_toPrecomp R code trace
  have hhead := R.cost_headCode_precomp code finish
  have hstate := R.size_state_precomp code finish
  have hheadSize := R.size_head_precomp code finish
  unfold QuantitativeRealization.executionCost
  constructor
  · simp only [ExecutionCost.work_add, ExecutionCost.work_ofWork,
      ExecutionCost.work_observe]
    have hcostWork := congrArg ExecutionCost.work hcost
    omega
  · constructor
    · simp only [ExecutionCost.queries_add, ExecutionCost.queries_ofWork,
        ExecutionCost.queries_observe, Nat.zero_add]
      exact Nat.le_of_eq (congrArg ExecutionCost.queries hcost)
    · constructor
      · simp only [ExecutionCost.traffic_add, ExecutionCost.traffic_ofWork,
          ExecutionCost.traffic_observe, Nat.zero_add]
        exact Nat.le_of_eq (congrArg ExecutionCost.traffic hcost)
      · constructor
        · simp only [ExecutionCost.peakStateSize_add,
            ExecutionCost.peakStateSize_observe]
          rw [congrArg ExecutionCost.peakStateSize hcost, hstate]
          simp [ExecutionCost.ofWork]
        · simp only [ExecutionCost.peakHeadSize_add,
            ExecutionCost.peakHeadSize_observe]
          rw [congrArg ExecutionCost.peakHeadSize hcost]
          simp only [ExecutionCost.ofWork, zero_max]
          simp only [Boundary.withInput_head]
          rw [hheadSize]

/-- Input precomposition preserves restricted pathwise bounds, using the backend's certified
upper bound for initialization overhead on top of the source bound. -/
theorem QuantitativeRealization.RunsWithinUnder.precomp
    {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : A → ExecutionCost}
    (h : R.RunsWithinUnder allows bound)
    (code : Q.Realizer inputRep bd.input f) :
    (R.precomp code).RunsWithinUnder allows fun input ↦
      ExecutionCost.ofWork
          (Q.cost code input + Q.composeOverhead code R.initCode input) +
        bound (f input) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input finish trace htrace
    let sourceTrace := trace.ofPrecomp R code
    have hsource : R.executionCost (f input) sourceTrace ≤ bound (f input) :=
      h.cost_le (f input) sourceTrace (by
        exact (QuantitativeRealization.ExecutionTrace.conforms_ofPrecomp
          R code allows trace).mpr htrace)
    rw [← QuantitativeRealization.ExecutionTrace.toPrecomp_ofPrecomp R code trace]
    exact (R.executionCost_toPrecomp_le code input sourceTrace).trans
      (ExecutionCost.add_le_add le_rfl hsource)
  · intro input
    simp only [ExecutionCost.queries_add, ExecutionCost.queries_ofWork, Nat.zero_add]
    simpa only [QuantitativeRealization.precomp, Function.comp_apply] using
      (resolvesInUnder_setInit_iff R.machine allows (R.machine.init ∘ f)
        (bound (f input)).queries (R.machine.init (f input))).mpr
          (h.resolvesIn (f input))
  · intro input state trace htrace position next hview
    apply h.traceProgress (f input) (trace.ofPrecomp R code)
    · exact (QuantitativeRealization.ExecutionTrace.conforms_ofPrecomp
        R code allows trace).mpr htrace
    · simpa only [QuantitativeRealization.precomp,
        DynComputation.setInit_view] using hview

end Precomp

/-! ## Result postcomposition -/

section MapResult

variable [Q.HasCategory] [Q.HasSum] {D : Type u} {outRep : C.Str D} {f : B → D}

omit [DecidableEq p.A] in
/-- A query exposed after mapping return values was already the same source query. -/
theorem view_eq_query_of_mapResult_view_eq_query (M : DynComputation.{u} p A B)
    {state : M.State} {position : p.A} {next : p.B position → M.State}
    (view_eq : (M.mapResult f).view state = Sum.inr ⟨position, next⟩) :
    M.view state = Sum.inr ⟨position, next⟩ := by
  cases hsource : M.view state with
  | inl value =>
      rw [DynComputation.mapResult_view, hsource] at view_eq
      exact nomatch view_eq
  | inr query =>
      rw [DynComputation.mapResult_view, hsource] at view_eq
      cases view_eq
      rfl

namespace QuantitativeRealization.ExecutionTrace

/-- Transport a trace through result postcomposition. Visible queries, typed answers, and hidden
states are preserved. -/
def toMapResult (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) :
    (R.mapResult code).ExecutionTrace start finish :=
  match trace with
  | .nil state => .nil (R := R.mapResult code) state
  | .query view_eq direction tail =>
      .query (R := R.mapResult code)
        (by
          change (R.machine.mapResult f).view _ = _
          rw [DynComputation.mapResult_view, view_eq]) direction
        (toMapResult R code tail)

/-- Recover the source trace underlying result postcomposition. -/
def ofMapResult (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f) {start finish : R.machine.State}
    (trace : (R.mapResult code).ExecutionTrace start finish) :
    R.ExecutionTrace start finish :=
  match trace with
  | .nil state => .nil (R := R) state
  | .query view_eq direction tail => by
      change (R.machine.mapResult f).view _ = _ at view_eq
      exact .query (R := R)
        (view_eq_query_of_mapResult_view_eq_query R.machine view_eq)
        direction (ofMapResult R code tail)

@[simp] theorem ofMapResult_toMapResult (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) :
    (trace.toMapResult R code).ofMapResult R code = trace := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih => simp [toMapResult, ofMapResult, ih]

@[simp] theorem conforms_toMapResult (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f)
    (allows : ∀ position, p.B position → Prop)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.toMapResult R code).Conforms allows ↔ trace.Conforms allows := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih => simp [toMapResult, Conforms, ih]

@[simp] theorem conforms_ofMapResult (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f)
    (allows : ∀ position, p.B position → Prop)
    {start finish : R.machine.State}
    (trace : (R.mapResult code).ExecutionTrace start finish) :
    (trace.ofMapResult R code).Conforms allows ↔ trace.Conforms allows :=
  match trace with
  | .nil _ => Iff.rfl
  | .query _ _ tail => and_congr Iff.rfl (conforms_ofMapResult R code allows tail)

@[simp] theorem length_toMapResult (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) :
    (trace.toMapResult R code).length = trace.length := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih => simp [toMapResult, length, ih]

end QuantitativeRealization.ExecutionTrace

omit [DecidableEq p.A] in
/-- Mapping returned values preserves relation-restricted resolution exactly. -/
theorem resolvesInUnder_mapResult_iff (M : DynComputation.{u} p A B)
    (allows : ∀ position, p.B position → Prop) (k : ℕ) (state : M.State) :
    (M.mapResult f).ResolvesInUnder allows k state ↔
      M.ResolvesInUnder allows k state := by
  induction k generalizing state with
  | zero =>
      cases hview : M.view state <;>
        simp [ResolvesInUnder, DynComputation.mapResult_view, hview]
  | succ k ih =>
      cases hview : M.view state with
      | inl value =>
          simp [ResolvesInUnder, DynComputation.mapResult_view, hview]
      | inr query =>
          rcases query with ⟨position, next⟩
          simp only [ResolvesInUnder, DynComputation.mapResult_view, hview]
          exact forall_congr' fun direction ↦
            imp_congr_right fun _ ↦ ih (next direction)

/-- An explicit pathwise account of the backend overhead introduced by result postcomposition.

This certificate deliberately compares exact target cost with exact source cost. It does not infer
that sum elimination, composition, or result encoding is free. -/
structure MapResultCostCertificate (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f)
    (allows : ∀ position, p.B position → Prop) where
  /-- Input-indexed resource allowance for the assembled result readout. -/
  overhead : A → ExecutionCost
  /-- Every conforming target prefix costs at most its source prefix plus the allowance. -/
  cost_le : ∀ input {finish : R.machine.State}
    (trace : (R.mapResult code).ExecutionTrace
      ((R.mapResult code).machine.init input) finish),
    trace.Conforms allows →
      (R.mapResult code).executionCost input trace ≤
        R.executionCost input (trace.ofMapResult R code) + overhead input

/-- Result postcomposition preserves restricted bounds under an explicit pathwise backend-cost
certificate. Control-flow termination and progress are transported generically. -/
theorem QuantitativeRealization.RunsWithinUnder.mapResult
    {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : A → ExecutionCost}
    (h : R.RunsWithinUnder allows bound)
    (code : Q.Realizer bd.out outRep f)
    (certificate : MapResultCostCertificate R code allows) :
    (R.mapResult code).RunsWithinUnder allows fun input ↦
      bound input + certificate.overhead input := by
  refine ⟨?_, ?_, ?_⟩
  · intro input finish trace htrace
    have hsource : R.executionCost input (trace.ofMapResult R code) ≤ bound input :=
      h.cost_le input (trace.ofMapResult R code)
        ((QuantitativeRealization.ExecutionTrace.conforms_ofMapResult
          R code allows trace).mpr htrace)
    exact (certificate.cost_le input trace htrace).trans
      (ExecutionCost.add_le_add hsource le_rfl)
  · intro input
    apply (resolvesInUnder_mapResult_iff R.machine allows _ _).mpr
    apply (h.resolvesIn input).mono
    simp
  · intro input state trace htrace position next hview
    apply h.traceProgress input (trace.ofMapResult R code)
    · exact (QuantitativeRealization.ExecutionTrace.conforms_ofMapResult
        R code allows trace).mpr htrace
    · exact view_eq_query_of_mapResult_view_eq_query R.machine hview

end MapResult

end DynSystem.DynComputation

end PFunctor
