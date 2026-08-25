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

Bounded sequential composition uses a dependent phase decomposition for composite traces: a left
prefix may stop before handoff, while a returned first phase exposes the second phase's initial
view immediately and its first query transitions directly into the right state. The decomposition
combines a uniform second-phase bound with explicit assembled-code overhead without choosing a
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
              · have hdecrease := certificate.decreases hview direction hAllows
                omega
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

/-! ## Resolution from bounded prefixes -/

/-- A uniform bound on every conforming prefix, together with syntactic progress, supplies
branchwise resolution.

This lemma closes a useful proof gap between the pathwise and inductive parts of
`RunsWithinUnder`. Progress is essential at budget zero: without it a pending query with no
allowed answers would make `ResolvesInUnder` hold vacuously. -/
theorem resolvesInUnder_of_traceLength_le
    (R : QuantitativeRealization Q bd) (allows : ∀ position, p.B position → Prop)
    (start : R.machine.State) (queries : ℕ)
    (length_le : ∀ {finish : R.machine.State} (trace : R.ExecutionTrace start finish),
      trace.Conforms allows → trace.length ≤ queries)
    (progress : ∀ {state : R.machine.State} (trace : R.ExecutionTrace start state),
      trace.Conforms allows → ∀ {position : p.A} {next : p.B position → R.machine.State},
        R.machine.view state = Sum.inr ⟨position, next⟩ →
          ∃ direction, allows position direction) :
    R.machine.ResolvesInUnder allows queries start := by
  induction queries generalizing start with
  | zero =>
      cases hview : R.machine.view start with
      | inl value => exact R.machine.resolvesInUnder_return allows 0 start value hview
      | inr query =>
          rcases query with ⟨position, next⟩
          obtain ⟨direction, hAllows⟩ := progress (.nil start) trivial hview
          have hlength := length_le (.query hview direction (.nil (next direction)))
            ⟨hAllows, trivial⟩
          simp [QuantitativeRealization.ExecutionTrace.length] at hlength
  | succ queries ih =>
      cases hview : R.machine.view start with
      | inl value =>
          exact R.machine.resolvesInUnder_return allows (queries + 1) start value hview
      | inr query =>
          rcases query with ⟨position, next⟩
          rw [R.machine.resolvesInUnder_query_succ_iff allows queries start position next hview]
          intro direction hAllows
          apply ih (next direction)
          · intro finish trace htrace
            have hlength := length_le (.query hview direction trace) ⟨hAllows, htrace⟩
            simp only [QuantitativeRealization.ExecutionTrace.length] at hlength
            omega
          · intro state trace htrace queryPosition queryNext queryView
            exact progress (.query hview direction trace) ⟨hAllows, htrace⟩ queryView

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
          simp only [ExecutionCost.ofWork]
          simp only [Boundary.withInput_head]
          rw [hheadSize]
          omega

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

/-! ## Sequential composition -/

section SeqComp

variable [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive]
  {D : Type u} {outRep : C.Str D}

namespace QuantitativeRealization.ExecutionTrace

/-- Embed a first-phase trace in the left summand of a sequentially composed realization. -/
def toSeqCompLeft (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep))
    {start finish : R₁.machine.State} (trace : R₁.ExecutionTrace start finish) :
    (R₁.seqComp R₂).ExecutionTrace (Sum.inl start) (Sum.inl finish) :=
  match trace with
  | .nil state => .nil (R := R₁.seqComp R₂) (Sum.inl state)
  | .query (position := position) (next := next) view_eq direction tail =>
      .query (R := R₁.seqComp R₂) (position := position)
        (next := fun answer ↦ Sum.inl (next answer))
        (R₁.machine.seqComp_view_inl_of_query R₂.machine view_eq) direction
        (toSeqCompLeft R₁ R₂ tail)

/-- Embed a second-phase trace in the right summand of a sequentially composed realization. -/
def toSeqCompRight (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep))
    {start finish : R₂.machine.State} (trace : R₂.ExecutionTrace start finish) :
    (R₁.seqComp R₂).ExecutionTrace (Sum.inr start) (Sum.inr finish) :=
  match trace with
  | .nil state => .nil (R := R₁.seqComp R₂) (Sum.inr state)
  | .query (position := position) (next := next) view_eq direction tail =>
      .query (R := R₁.seqComp R₂) (position := position)
        (next := fun answer ↦ Sum.inr (next answer))
        (by
          change (R₁.machine.seqComp R₂.machine).view (Sum.inr start) = _
          rw [R₁.machine.seqComp_view_inr, view_eq]
          rfl) direction
        (toSeqCompRight R₁ R₂ tail)

@[simp] theorem conforms_toSeqCompLeft (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep))
    (allows : ∀ position, p.B position → Prop)
    {start finish : R₁.machine.State} (trace : R₁.ExecutionTrace start finish) :
    (trace.toSeqCompLeft R₁ R₂).Conforms allows ↔ trace.Conforms allows := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih => simp [toSeqCompLeft, Conforms, ih]

@[simp] theorem conforms_toSeqCompRight (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep))
    (allows : ∀ position, p.B position → Prop)
    {start finish : R₂.machine.State} (trace : R₂.ExecutionTrace start finish) :
    (trace.toSeqCompRight R₁ R₂).Conforms allows ↔ trace.Conforms allows := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih => simp [toSeqCompRight, Conforms, ih]

end QuantitativeRealization.ExecutionTrace

/-- Source traces underlying a prefix of a sequentially composed machine.

The three constructors distinguish a prefix still exposing a first-phase query, a completed
first phase before the second phase has made a query, and a prefix that has crossed into the
right state summand. The handoff constructor includes the zero-length second-phase prefix; this
accounts for the second initialization and its first readout even when no second-phase query has
yet occurred. -/
inductive SeqCompTraceSource (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) (start : R₁.machine.State) :
    (R₁.machine.State ⊕ R₂.machine.State) → Type u where
  /-- The prefix remains in phase one at a state that exposes another phase-one query. -/
  | left {finish : R₁.machine.State}
      (trace : R₁.ExecutionTrace start finish)
      {position : p.A} {next : p.B position → R₁.machine.State}
      (view_eq : R₁.machine.view finish = Sum.inr ⟨position, next⟩) :
      SeqCompTraceSource R₁ R₂ start (Sum.inl finish)
  /-- Phase one has returned, but the prefix contains no second-phase query yet. -/
  | handoff {finish : R₁.machine.State} {value : B}
      (trace : R₁.ExecutionTrace start finish)
      (view_eq : R₁.machine.view finish = Sum.inl value) :
      SeqCompTraceSource R₁ R₂ start (Sum.inl finish)
  /-- The prefix contains a handoff and at least one second-phase query. -/
  | right {leftFinish : R₁.machine.State} {value : B}
      {rightFinish : R₂.machine.State}
      (left : R₁.ExecutionTrace start leftFinish)
      (view_eq : R₁.machine.view leftFinish = Sum.inl value)
      (right : R₂.ExecutionTrace (R₂.machine.init value) rightFinish) :
      SeqCompTraceSource R₁ R₂ start (Sum.inr rightFinish)

namespace SeqCompTraceSource

variable {R₁ : QuantitativeRealization Q bd}
  {R₂ : QuantitativeRealization Q (bd.mid outRep)} {start : R₁.machine.State}

/-- Number of visible query-answer transitions represented by the phase-local traces. -/
def length : {finish : R₁.machine.State ⊕ R₂.machine.State} →
    SeqCompTraceSource R₁ R₂ start finish → ℕ
  | _, .left trace _ => trace.length
  | _, .handoff trace _ => trace.length
  | _, .right leftTrace _ rightTrace => leftTrace.length + rightTrace.length

/-- Prepend one first-phase query to a decomposition starting at its selected child. -/
def prependLeft {state : R₁.machine.State} {position : p.A}
    {next : p.B position → R₁.machine.State}
    (view_eq : R₁.machine.view state = Sum.inr ⟨position, next⟩)
    (direction : p.B position)
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompTraceSource R₁ R₂ (next direction) finish) :
    SeqCompTraceSource R₁ R₂ state finish :=
  match source with
  | .left trace finalView => .left (.query view_eq direction trace) finalView
  | .handoff trace finalView => .handoff (.query view_eq direction trace) finalView
  | .right leftTrace returned rightTrace =>
      .right (.query view_eq direction leftTrace) returned rightTrace

omit [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive] in
@[simp] theorem length_prependLeft {state : R₁.machine.State} {position : p.A}
    {next : p.B position → R₁.machine.State}
    (view_eq : R₁.machine.view state = Sum.inr ⟨position, next⟩)
    (direction : p.B position)
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompTraceSource R₁ R₂ (next direction) finish) :
    (source.prependLeft view_eq direction).length = source.length + 1 := by
  cases source with
  | left => rfl
  | handoff => rfl
  | right =>
      simp [prependLeft, length, QuantitativeRealization.ExecutionTrace.length]
      omega

/-- Whether every answer appearing in the projected source traces obeys an answer contract. -/
def Conforms (allows : ∀ position, p.B position → Prop) :
    {finish : R₁.machine.State ⊕ R₂.machine.State} →
      SeqCompTraceSource R₁ R₂ start finish → Prop
  | _, .left trace _ => trace.Conforms allows
  | _, .handoff trace _ => trace.Conforms allows
  | _, .right leftTrace _ rightTrace =>
      leftTrace.Conforms allows ∧ rightTrace.Conforms allows

omit [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive] in
@[simp] theorem conforms_prependLeft (allows : ∀ position, p.B position → Prop)
    {state : R₁.machine.State} {position : p.A}
    {next : p.B position → R₁.machine.State}
    (view_eq : R₁.machine.view state = Sum.inr ⟨position, next⟩)
    (direction : p.B position)
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompTraceSource R₁ R₂ (next direction) finish) :
    (source.prependLeft view_eq direction).Conforms allows ↔
      allows position direction ∧ source.Conforms allows := by
  cases source <;> simp [prependLeft, Conforms,
    QuantitativeRealization.ExecutionTrace.Conforms, and_assoc]

/-- Exact source-machine cost represented by a phase decomposition. -/
def cost (input : A) :
    {finish : R₁.machine.State ⊕ R₂.machine.State} →
      SeqCompTraceSource R₁ R₂ (R₁.machine.init input) finish → ExecutionCost
  | _, .left trace _ => R₁.executionCost input trace
  | _, .handoff (value := value) trace _ =>
      R₁.executionCost input trace +
        R₂.executionCost value (.nil (R₂.machine.init value))
  | _, .right (value := value) leftTrace _ rightTrace =>
      R₁.executionCost input leftTrace + R₂.executionCost value rightTrace

omit [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive] in
/-- The query component of a phase source's cost is its exact syntactic length. -/
@[simp] theorem queries_cost (input : A)
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompTraceSource R₁ R₂ (R₁.machine.init input) finish) :
    (source.cost input).queries = source.length := by
  cases source <;> simp [cost, length, QuantitativeRealization.ExecutionTrace.length]

end SeqCompTraceSource

/-- A second-phase trace projected from a composite prefix already in the right summand. -/
inductive SeqCompRightTraceSource (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) (start : R₂.machine.State) :
    (R₁.machine.State ⊕ R₂.machine.State) → Type u where
  /-- The projected second-phase trace, whose final state is embedded in the right summand. -/
  | mk {finish : R₂.machine.State} (trace : R₂.ExecutionTrace start finish) :
      SeqCompRightTraceSource R₁ R₂ start (Sum.inr finish)

namespace SeqCompRightTraceSource

/-- Number of visible query-answer transitions in a projected second-phase trace. -/
def length {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.mid outRep)} {start : R₂.machine.State}
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompRightTraceSource R₁ R₂ start finish) : ℕ :=
  match source with
  | .mk trace => trace.length

/-- Whether every answer in a projected second-phase trace obeys an answer contract. -/
def Conforms {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.mid outRep)}
    (allows : ∀ position, p.B position → Prop) {start : R₂.machine.State}
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompRightTraceSource R₁ R₂ start finish) : Prop :=
  match source with
  | .mk trace => trace.Conforms allows

end SeqCompRightTraceSource

/-- Phase-source data for a composite prefix with an arbitrary starting summand. -/
inductive SeqCompAnyTraceSource (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) :
    (R₁.machine.State ⊕ R₂.machine.State) →
      (R₁.machine.State ⊕ R₂.machine.State) → Type u where
  /-- A prefix starting in the first phase. -/
  | fromLeft {start : R₁.machine.State}
      {finish : R₁.machine.State ⊕ R₂.machine.State}
      (source : SeqCompTraceSource R₁ R₂ start finish) :
      SeqCompAnyTraceSource R₁ R₂ (Sum.inl start) finish
  /-- A prefix starting in the second phase. -/
  | fromRight {start : R₂.machine.State}
      {finish : R₁.machine.State ⊕ R₂.machine.State}
      (source : SeqCompRightTraceSource R₁ R₂ start finish) :
      SeqCompAnyTraceSource R₁ R₂ (Sum.inr start) finish

namespace SeqCompAnyTraceSource

/-- Number of visible query-answer transitions represented by either phase source. -/
def length {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.mid outRep)}
    {start finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompAnyTraceSource R₁ R₂ start finish) : ℕ :=
  match source with
  | .fromLeft source => source.length
  | .fromRight source => source.length

/-- Whether every answer in either phase-source projection obeys an answer contract. -/
def Conforms {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.mid outRep)}
    (allows : ∀ position, p.B position → Prop)
    {start finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompAnyTraceSource R₁ R₂ start finish) : Prop :=
  match source with
  | .fromLeft source => source.Conforms allows
  | .fromRight source => source.Conforms allows

end SeqCompAnyTraceSource

namespace QuantitativeRealization.ExecutionTrace

/-- A phase decomposition paired with its generic answer-contract transport theorem. -/
structure SeqCompAnyDecomposition (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep))
    {start finish : R₁.machine.State ⊕ R₂.machine.State}
    (trace : (R₁.seqComp R₂).ExecutionTrace start finish) where
  /-- Exact phase-local traces underlying the composite prefix. -/
  source : SeqCompAnyTraceSource R₁ R₂ start finish
  /-- Every answer contract on the composite trace holds on its phase-local projections. -/
  conforms : ∀ allows : ∀ position, p.B position → Prop,
    trace.Conforms allows → source.Conforms allows
  /-- The phase-local traces contain exactly the composite prefix's visible queries. -/
  length_eq : source.length = trace.length

/-- Fuelled decomposition of a composite prefix from either state summand.

The explicit fuel makes recursion insensitive to dependent transports of a trace's starting
state. Clients use `seqCompAnyDecomposition`, which supplies the exact trace length. -/
def seqCompAnyDecompositionAux (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) :
    (fuel : ℕ) → {start finish : R₁.machine.State ⊕ R₂.machine.State} →
      (trace : (R₁.seqComp R₂).ExecutionTrace start finish) →
        trace.length ≤ fuel → SeqCompAnyDecomposition R₁ R₂ trace
  | _, _, _, .nil state, _ => by
      cases state with
      | inl state₁ =>
          cases hsource : R₁.machine.view state₁ with
          | inl value =>
              exact ⟨.fromLeft (.handoff (.nil state₁) hsource), fun _ _ ↦ trivial, rfl⟩
          | inr query =>
              rcases query with ⟨position, next⟩
              exact ⟨.fromLeft (.left (.nil state₁) hsource), fun _ _ ↦ trivial, rfl⟩
      | inr state₂ =>
          exact ⟨.fromRight (.mk (.nil state₂)), fun _ _ ↦ trivial, rfl⟩
  | 0, _, _, .query view_eq direction tail, length_le => by
      simp [length] at length_le
  | fuel + 1, _, _, .query view_eq direction tail, length_le => by
      rename_i state position next finish
      have tailLength_le : tail.length ≤ fuel := by
        simp only [length] at length_le
        omega
      let tailDecomposition := seqCompAnyDecompositionAux R₁ R₂ fuel tail tailLength_le
      cases state with
      | inr state₂ =>
          cases hsource : R₂.machine.view state₂ with
          | inl value =>
              have hreturn : (R₁.seqComp R₂).machine.view (Sum.inr state₂) =
                  Sum.inl value := by
                change (R₁.machine.seqComp R₂.machine).view (Sum.inr state₂) = _
                rw [R₁.machine.seqComp_view_inr, hsource]
                rfl
              rw [hreturn] at view_eq
              exact nomatch view_eq
          | inr query =>
              rcases query with ⟨sourcePosition, sourceNext⟩
              have hquery : (R₁.seqComp R₂).machine.view (Sum.inr state₂) =
                  Sum.inr ⟨sourcePosition, fun answer ↦ Sum.inr (sourceNext answer)⟩ := by
                change (R₁.machine.seqComp R₂.machine).view (Sum.inr state₂) = _
                rw [R₁.machine.seqComp_view_inr, hsource]
                rfl
              rw [hquery] at view_eq
              cases view_eq
              rcases tailDecomposition with ⟨tailSource, tailConforms, tailLength_eq⟩
              cases tailSource with
              | fromRight source =>
                  cases source with
                  | mk rightTrace =>
                      refine ⟨.fromRight (.mk (.query hsource direction rightTrace)), ?_, ?_⟩
                      · intro allows htrace
                        exact ⟨htrace.1, tailConforms allows htrace.2⟩
                      · simpa [SeqCompAnyTraceSource.length,
                          SeqCompRightTraceSource.length,
                          QuantitativeRealization.ExecutionTrace.length] using tailLength_eq
      | inl state₁ =>
          cases hsource : R₁.machine.view state₁ with
          | inl value =>
              cases hright : R₂.machine.view (R₂.machine.init value) with
              | inl result =>
                  have hreturn : (R₁.seqComp R₂).machine.view (Sum.inl state₁) =
                      Sum.inl result := by
                    change (R₁.machine.seqComp R₂.machine).view (Sum.inl state₁) = _
                    rw [R₁.machine.seqComp_view_inl_of_return R₂.machine hsource, hright]
                    rfl
                  rw [hreturn] at view_eq
                  exact nomatch view_eq
              | inr query =>
                  rcases query with ⟨sourcePosition, sourceNext⟩
                  have hquery :
                      (R₁.seqComp R₂).machine.view (Sum.inl state₁) =
                        Sum.inr ⟨sourcePosition,
                          fun answer ↦ Sum.inr (sourceNext answer)⟩ := by
                    change (R₁.machine.seqComp R₂.machine).view (Sum.inl state₁) = _
                    rw [R₁.machine.seqComp_view_inl_of_return R₂.machine hsource, hright]
                    rfl
                  rw [hquery] at view_eq
                  cases view_eq
                  rcases tailDecomposition with ⟨tailSource, tailConforms, tailLength_eq⟩
                  cases tailSource with
                  | fromRight source =>
                      cases source with
                      | mk rightTrace =>
                          refine ⟨.fromLeft
                            (.right (.nil state₁) hsource
                              (.query hright direction rightTrace)), ?_, ?_⟩
                          · intro allows htrace
                            exact ⟨trivial, ⟨htrace.1, tailConforms allows htrace.2⟩⟩
                          · simpa [SeqCompAnyTraceSource.length, SeqCompTraceSource.length,
                              SeqCompRightTraceSource.length,
                              QuantitativeRealization.ExecutionTrace.length] using tailLength_eq
          | inr query =>
              rcases query with ⟨sourcePosition, sourceNext⟩
              have hquery :=
                R₁.machine.seqComp_view_inl_of_query R₂.machine hsource
              change (R₁.machine.seqComp R₂.machine).view (Sum.inl state₁) = _ at view_eq
              rw [hquery] at view_eq
              cases view_eq
              rcases tailDecomposition with ⟨tailSource, tailConforms, tailLength_eq⟩
              cases tailSource with
              | fromLeft source =>
                  refine ⟨.fromLeft (source.prependLeft hsource direction), ?_, ?_⟩
                  · intro allows htrace
                    have htail := tailConforms allows htrace.2
                    cases source with
                    | left sourceTrace finalView =>
                        change allows next direction ∧ sourceTrace.Conforms allows
                        change sourceTrace.Conforms allows at htail
                        exact ⟨htrace.1, htail⟩
                    | handoff sourceTrace returned =>
                        change allows next direction ∧ sourceTrace.Conforms allows
                        change sourceTrace.Conforms allows at htail
                        exact ⟨htrace.1, htail⟩
                    | right leftTrace returned rightTrace =>
                        change (allows next direction ∧ leftTrace.Conforms allows) ∧
                          rightTrace.Conforms allows
                        change leftTrace.Conforms allows ∧ rightTrace.Conforms allows at htail
                        exact ⟨⟨htrace.1, htail.1⟩, htail.2⟩
                  · change (source.prependLeft hsource direction).length = tail.length + 1
                    cases source <;>
                      simp [SeqCompTraceSource.prependLeft, SeqCompTraceSource.length,
                        SeqCompAnyTraceSource.length,
                        QuantitativeRealization.ExecutionTrace.length] at tailLength_eq ⊢ <;>
                      omega

/-- Mechanically decompose a composite prefix into exact phase-local source traces and transport
its answer contract.

The result retains dependent response types rather than flattening the interaction into an
untyped event log. -/
def seqCompAnyDecomposition (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep))
    {start finish : R₁.machine.State ⊕ R₂.machine.State}
    (trace : (R₁.seqComp R₂).ExecutionTrace start finish) :
    SeqCompAnyDecomposition R₁ R₂ trace :=
  seqCompAnyDecompositionAux R₁ R₂ trace.length trace le_rfl

/-- Extract the phase-local source traces from a mechanically checked decomposition. -/
def seqCompAnySource (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep))
    {start finish : R₁.machine.State ⊕ R₂.machine.State}
    (trace : (R₁.seqComp R₂).ExecutionTrace start finish) :
    SeqCompAnyTraceSource R₁ R₂ start finish :=
  (seqCompAnyDecomposition R₁ R₂ trace).source

/-- The arbitrary-state phase source contains exactly the composite prefix's visible queries. -/
theorem length_seqCompAnySource (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep))
    {start finish : R₁.machine.State ⊕ R₂.machine.State}
    (trace : (R₁.seqComp R₂).ExecutionTrace start finish) :
    (trace.seqCompAnySource R₁ R₂).length = trace.length := by
  simpa only [seqCompAnySource] using (seqCompAnyDecomposition R₁ R₂ trace).length_eq

/-- Phase decomposition preserves every answer contract, independently of backend costs. -/
theorem conforms_seqCompAnySource (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep))
    (allows : ∀ position, p.B position → Prop)
    {start finish : R₁.machine.State ⊕ R₂.machine.State}
    (trace : (R₁.seqComp R₂).ExecutionTrace start finish)
    (htrace : trace.Conforms allows) :
    (trace.seqCompAnySource R₁ R₂).Conforms allows :=
  (seqCompAnyDecomposition R₁ R₂ trace).conforms allows htrace

/-- Specialize the arbitrary-state decomposition to a prefix starting in phase one. -/
def seqCompSource (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) {start : R₁.machine.State}
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (trace : (R₁.seqComp R₂).ExecutionTrace (Sum.inl start) finish) :
    SeqCompTraceSource R₁ R₂ start finish :=
  match seqCompAnySource R₁ R₂ trace with
  | .fromLeft source => source

/-- A phase source starting on the left contains exactly the composite prefix's visible
queries. -/
theorem length_seqCompSource (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) {start : R₁.machine.State}
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (trace : (R₁.seqComp R₂).ExecutionTrace (Sum.inl start) finish) :
    (trace.seqCompSource R₁ R₂).length = trace.length := by
  have hlength := trace.length_seqCompAnySource R₁ R₂
  unfold seqCompSource
  generalize source_eq : trace.seqCompAnySource R₁ R₂ = source at hlength ⊢
  cases source with
  | fromLeft source => exact hlength

/-- A composite prefix starting in phase one preserves every answer contract on its exact
phase-local source traces. -/
theorem conforms_seqCompSource (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep))
    (allows : ∀ position, p.B position → Prop) {start : R₁.machine.State}
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (trace : (R₁.seqComp R₂).ExecutionTrace (Sum.inl start) finish)
    (htrace : trace.Conforms allows) :
    (trace.seqCompSource R₁ R₂).Conforms allows :=
  by
    have hsource := trace.conforms_seqCompAnySource R₁ R₂ allows htrace
    unfold seqCompSource
    generalize source_eq : trace.seqCompAnySource R₁ R₂ = source at hsource ⊢
    cases source with
    | fromLeft source => exact hsource

/-- Specialize the arbitrary-state decomposition to a prefix already in phase two. -/
def seqCompRightSource (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) {start : R₂.machine.State}
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (trace : (R₁.seqComp R₂).ExecutionTrace (Sum.inr start) finish) :
    SeqCompRightTraceSource R₁ R₂ start finish :=
  match seqCompAnySource R₁ R₂ trace with
  | .fromRight source => source

end QuantitativeRealization.ExecutionTrace

/-- A uniform envelope for the second-phase bounds of every conformingly reachable handoff.

The quantification over actual first-phase traces is deliberate: clients can derive this field
from the first realization's returned-size theorem and a size-indexed second-phase bound, without
claiming that unreachable values have small encodings. -/
structure SeqCompHandoffBound (R₁ : QuantitativeRealization Q bd)
    (allows : ∀ position, p.B position → Prop) (secondBound : B → ExecutionCost) where
  /-- Input-indexed uniform resource envelope for a reached second phase. -/
  bound : A → ExecutionCost
  /-- Every value returned along a conforming first-phase prefix fits the envelope. -/
  returned_le : ∀ input {finish : R₁.machine.State}
    (trace : R₁.ExecutionTrace (R₁.machine.init input) finish),
    trace.Conforms allows → ∀ {value : B},
      R₁.machine.view finish = Sum.inl value → secondBound value ≤ bound input

/-- Backend-cost comparison between a composite trace and its exact phase decomposition.

The sole proof obligation is genuinely quantitative: it accounts for concrete structural
realizers assembled by `seqComp`. Answer-contract preservation is a generic theorem of the exact
phase decomposition. -/
structure SeqCompCostCertificate (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep))
    (allows : ∀ position, p.B position → Prop) where
  /-- Input-indexed allowance for structural code and phase switching. -/
  overhead : A → ExecutionCost
  /-- Composite cost is bounded by exact source-phase cost plus structural overhead. -/
  cost_le : ∀ input {finish : R₁.machine.State ⊕ R₂.machine.State}
    (trace : (R₁.seqComp R₂).ExecutionTrace
      (Sum.inl (R₁.machine.init input)) finish),
    trace.Conforms allows →
      (R₁.seqComp R₂).executionCost input trace ≤
        (trace.seqCompSource R₁ R₂).cost input + overhead input

/-- Exact phase-local source traces compose syntactic progress across a handoff. -/
theorem SeqCompTraceSource.response_exists
    {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.mid outRep)}
    {allows : ∀ position, p.B position → Prop}
    {firstBound : A → ExecutionCost} {secondBound : B → ExecutionCost}
    (first : R₁.RunsWithinUnder allows firstBound)
    (second : R₂.RunsWithinUnder allows secondBound)
    (input : A) {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompTraceSource R₁ R₂ (R₁.machine.init input) finish)
    (hsource : source.Conforms allows) {position : p.A}
    {next : p.B position → R₁.machine.State ⊕ R₂.machine.State}
    (view_eq : (R₁.seqComp R₂).machine.view finish = Sum.inr ⟨position, next⟩) :
    ∃ direction, allows position direction := by
  cases source with
  | left leftTrace leftView =>
      change leftTrace.Conforms allows at hsource
      have hcomposite :=
        R₁.machine.seqComp_view_inl_of_query R₂.machine leftView
      change (R₁.machine.seqComp R₂.machine).view _ = _ at view_eq
      rw [hcomposite] at view_eq
      cases view_eq
      exact first.traceProgress input leftTrace hsource leftView
  | handoff leftTrace returned =>
      rename_i leftFinish value
      change leftTrace.Conforms allows at hsource
      cases hright : R₂.machine.view (R₂.machine.init value) with
      | inl result =>
          have hreturn : (R₁.machine.seqComp R₂.machine).view (Sum.inl leftFinish) =
              Sum.inl result := by
            rw [R₁.machine.seqComp_view_inl_of_return R₂.machine returned, hright]
            rfl
          change (R₁.machine.seqComp R₂.machine).view _ = _ at view_eq
          rw [hreturn] at view_eq
          exact nomatch view_eq
      | inr query =>
          rcases query with ⟨sourcePosition, sourceNext⟩
          have hquery : (R₁.machine.seqComp R₂.machine).view (Sum.inl leftFinish) =
              Sum.inr ⟨sourcePosition, fun answer ↦ Sum.inr (sourceNext answer)⟩ := by
            rw [R₁.machine.seqComp_view_inl_of_return R₂.machine returned, hright]
            rfl
          change (R₁.machine.seqComp R₂.machine).view _ = _ at view_eq
          rw [hquery] at view_eq
          cases view_eq
          exact second.traceProgress value (.nil (R₂.machine.init value)) trivial hright
  | right leftTrace returned rightTrace =>
      rename_i leftFinish value rightFinish
      change leftTrace.Conforms allows ∧ rightTrace.Conforms allows at hsource
      cases hright : R₂.machine.view rightFinish with
      | inl result =>
          have hreturn : (R₁.machine.seqComp R₂.machine).view (Sum.inr rightFinish) =
              Sum.inl result := by
            rw [R₁.machine.seqComp_view_inr, hright]
            rfl
          change (R₁.machine.seqComp R₂.machine).view _ = _ at view_eq
          rw [hreturn] at view_eq
          exact nomatch view_eq
      | inr query =>
          rcases query with ⟨sourcePosition, sourceNext⟩
          have hquery : (R₁.machine.seqComp R₂.machine).view (Sum.inr rightFinish) =
              Sum.inr ⟨sourcePosition, fun answer ↦ Sum.inr (sourceNext answer)⟩ := by
            rw [R₁.machine.seqComp_view_inr, hright]
            rfl
          change (R₁.machine.seqComp R₂.machine).view _ = _ at view_eq
          rw [hquery] at view_eq
          cases view_eq
          exact second.traceProgress value rightTrace hsource.2 hright

/-- Syntactic progress composes because exact phase decomposition generically preserves answer
contracts. -/
theorem QuantitativeRealization.traceProgressUnder_seqComp
    {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.mid outRep)}
    {allows : ∀ position, p.B position → Prop}
    {firstBound : A → ExecutionCost} {secondBound : B → ExecutionCost}
    (first : R₁.RunsWithinUnder allows firstBound)
    (second : R₂.RunsWithinUnder allows secondBound) (input : A) :
    (R₁.seqComp R₂).TraceProgressUnder allows input := by
  intro state trace htrace position next view_eq
  exact (trace.seqCompSource R₁ R₂).response_exists first second input
    (trace.conforms_seqCompSource R₁ R₂ allows htrace) view_eq

omit [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive] in
/-- The exact phase-local cost of a composite prefix is bounded by the first-phase bound plus
the reachable second-phase envelope. -/
theorem SeqCompTraceSource.cost_le
    {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.mid outRep)}
    {allows : ∀ position, p.B position → Prop}
    {firstBound : A → ExecutionCost} {secondBound : B → ExecutionCost}
    (first : R₁.RunsWithinUnder allows firstBound)
    (second : R₂.RunsWithinUnder allows secondBound)
    (handoff : SeqCompHandoffBound R₁ allows secondBound) (input : A)
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompTraceSource R₁ R₂ (R₁.machine.init input) finish)
    (hsource : source.Conforms allows) :
    source.cost input ≤ firstBound input + handoff.bound input := by
  cases source with
  | left leftTrace leftView =>
      change leftTrace.Conforms allows at hsource
      exact (first.cost_le input leftTrace hsource).trans
        (ExecutionCost.le_add_right (firstBound input) (handoff.bound input))
  | handoff leftTrace returned =>
      rename_i leftFinish value
      change leftTrace.Conforms allows at hsource
      apply ExecutionCost.add_le_add (first.cost_le input leftTrace hsource)
      exact (second.cost_le value (.nil (R₂.machine.init value)) trivial).trans
        (handoff.returned_le input leftTrace hsource returned)
  | right leftTrace returned rightTrace =>
      rename_i leftFinish value rightFinish
      change leftTrace.Conforms allows ∧ rightTrace.Conforms allows at hsource
      apply ExecutionCost.add_le_add (first.cost_le input leftTrace hsource.1)
      exact (second.cost_le value rightTrace hsource.2).trans
        (handoff.returned_le input leftTrace hsource.1 returned)

omit [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive] in
/-- Exact phase-local query accounting is independent of structural backend overhead. -/
theorem SeqCompTraceSource.length_le
    {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.mid outRep)}
    {allows : ∀ position, p.B position → Prop}
    {firstBound : A → ExecutionCost} {secondBound : B → ExecutionCost}
    (first : R₁.RunsWithinUnder allows firstBound)
    (second : R₂.RunsWithinUnder allows secondBound)
    (handoff : SeqCompHandoffBound R₁ allows secondBound) (input : A)
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompTraceSource R₁ R₂ (R₁.machine.init input) finish)
    (hsource : source.Conforms allows) :
    source.length ≤ (firstBound input + handoff.bound input).queries := by
  rw [← source.queries_cost input]
  exact (source.cost_le first second handoff input hsource).2.1

/-- Sequential composition resolves within the sum of its phase query bounds.

Structural backend overhead may charge work, traffic, or representation sizes, but it cannot
create a visible oracle transition: exact phase decomposition accounts for every such transition
before the quantitative cost certificate is consulted. -/
theorem QuantitativeRealization.resolvesInUnder_seqComp
    {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.mid outRep)}
    {allows : ∀ position, p.B position → Prop}
    {firstBound : A → ExecutionCost} {secondBound : B → ExecutionCost}
    (first : R₁.RunsWithinUnder allows firstBound)
    (second : R₂.RunsWithinUnder allows secondBound)
    (handoff : SeqCompHandoffBound R₁ allows secondBound) (input : A) :
    (R₁.seqComp R₂).machine.ResolvesInUnder allows
      (firstBound input + handoff.bound input).queries
      ((R₁.seqComp R₂).machine.init input) := by
  apply resolvesInUnder_of_traceLength_le (R₁.seqComp R₂) allows
    ((R₁.seqComp R₂).machine.init input)
    (firstBound input + handoff.bound input).queries
  · intro finish trace htrace
    change (R₁.seqComp R₂).ExecutionTrace
      (Sum.inl (R₁.machine.init input)) finish at trace
    have hlength := trace.length_seqCompSource R₁ R₂
    calc
      trace.length = (trace.seqCompSource R₁ R₂).length := hlength.symm
      _ ≤ (firstBound input + handoff.bound input).queries :=
        (trace.seqCompSource R₁ R₂).length_le first second handoff input
          (trace.conforms_seqCompSource R₁ R₂ allows htrace)
  · exact QuantitativeRealization.traceProgressUnder_seqComp first second input

/-- Bounded sequential composition for quantitative realizations.

The returned intermediate is charged through `SeqCompHandoffBound`; concrete structural wiring
and phase-switching work is charged through `SeqCompCostCertificate`. Resolution is reconstructed
from the resulting query bound and the independently composed progress theorem. -/
theorem QuantitativeRealization.RunsWithinUnder.seqComp
    {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.mid outRep)}
    {allows : ∀ position, p.B position → Prop}
    {firstBound : A → ExecutionCost} {secondBound : B → ExecutionCost}
    (first : R₁.RunsWithinUnder allows firstBound)
    (second : R₂.RunsWithinUnder allows secondBound)
    (handoff : SeqCompHandoffBound R₁ allows secondBound)
    (certificate : SeqCompCostCertificate R₁ R₂ allows) :
    (R₁.seqComp R₂).RunsWithinUnder allows fun input ↦
      firstBound input + handoff.bound input + certificate.overhead input := by
  have cost_le : ∀ input {finish : R₁.machine.State ⊕ R₂.machine.State}
      (trace : (R₁.seqComp R₂).ExecutionTrace
        (Sum.inl (R₁.machine.init input)) finish),
      trace.Conforms allows →
        (R₁.seqComp R₂).executionCost input trace ≤
          firstBound input + handoff.bound input + certificate.overhead input := by
    intro input finish trace htrace
    have hsource := trace.conforms_seqCompSource R₁ R₂ allows htrace
    exact (certificate.cost_le input trace htrace).trans
      (ExecutionCost.add_le_add
        ((trace.seqCompSource R₁ R₂).cost_le first second handoff input hsource) le_rfl)
  have progress : ∀ input, (R₁.seqComp R₂).TraceProgressUnder allows input :=
    fun input ↦ QuantitativeRealization.traceProgressUnder_seqComp first second input
  refine ⟨cost_le, ?_, progress⟩
  intro input
  apply (QuantitativeRealization.resolvesInUnder_seqComp first second handoff input).mono
  simp

end SeqComp

end DynSystem.DynComputation

end PFunctor
