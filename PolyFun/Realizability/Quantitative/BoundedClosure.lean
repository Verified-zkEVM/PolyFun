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

## Main definitions

* `RankedRunCertificate`: a rank-and-progress certificate for query termination.
* `MapResultCostCertificate`: the pathwise backend overhead charged by result postcomposition.
* `SeqCompTraceSource`, `SeqCompRightTraceSource`, `SeqCompAnyTraceSource`: phase-local source
  traces underlying a prefix of a sequentially composed machine.
* `SeqCompHandoffBound`, `SeqCompCostCertificate`: the reachable second-phase envelope and the
  structural overhead allowance used by bounded sequential composition.

## Main results

* `resolvesInUnder_of_traceLength_le`: a uniform prefix-length bound plus syntactic progress
  gives branchwise resolution.
* `QuantitativeRealization.RunsWithinUnder.precomp`: input precomposition preserves restricted
  pathwise bounds.
* `QuantitativeRealization.RunsWithinUnder.mapResult`: result postcomposition preserves them
  under an explicit cost certificate.
* `QuantitativeRealization.RunsWithinUnder.seqComp`: bounded sequential composition.
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
answer is allowed.

`resolvesInUnder` discharges relation-restricted resolution from a certificate, and
`runsWithinUnder` combines it with a separate pathwise cost proof. -/
structure RankedRunCertificate (R : QuantitativeRealization Q bd)
    (allows : ∀ position, p.B position → Prop) where
  /-- Natural-valued potential remaining at a hidden machine state. -/
  rank : R.machine.State → ℕ
  /-- A zero-ranked state has already returned. -/
  returns_of_rank_zero : ∀ state, rank state = 0 → ∃ value, R.machine.view state = Sum.inl value
  /-- Every admitted response strictly decreases the potential. -/
  decreases : ∀ {state position next}, R.machine.view state = Sum.inr ⟨position, next⟩ →
      ∀ direction, allows position direction → rank (next direction) < rank state
  /-- Every pending query admits at least one response under the contract. -/
  progress : ∀ {state position next}, R.machine.view state = Sum.inr ⟨position, next⟩ →
      ∃ direction, allows position direction

namespace RankedRunCertificate

variable {R : QuantitativeRealization Q bd}
  {allows : ∀ position, p.B position → Prop}

/-- A rank certificate proves relation-restricted resolution with the state's rank as fuel. -/
theorem resolvesInUnder (certificate : RankedRunCertificate R allows) (state : R.machine.State) :
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
      | inl value => exact R.machine.resolvesInUnder_return allows (rank + 1) state value hview
      | inr query =>
        obtain ⟨position, next⟩ := query
        rw [R.machine.resolvesInUnder_query_succ_iff allows rank state position next hview]
        intro direction hAllows
        -- An allowed answer strictly drops the rank, so the successor's own rank is enough fuel.
        have := certificate.decreases hview direction hAllows
        exact (ih _ (by lia) (next direction) rfl).mono (by lia)

/-- A global rank certificate supplies syntactic progress from every input. -/
theorem traceProgressUnder (certificate : RankedRunCertificate R allows) (input : A) :
    R.TraceProgressUnder allows input := fun _ _ ↦ certificate.progress

/-- Combine a rank certificate with an honest pathwise cost proof.

The rank bound and cost bound are separate on purpose: a decreasing query potential does not say
anything about backend work, traffic, or representation sizes. -/
theorem runsWithinUnder (certificate : RankedRunCertificate R allows) (bound : A → ExecutionCost)
    (cost_le : ∀ input {finish : R.machine.State}
      (trace : R.ExecutionTrace (R.machine.init input) finish),
      trace.Conforms allows → R.executionCost input trace ≤ bound input)
    (rank_init_le : ∀ input, certificate.rank (R.machine.init input) ≤ (bound input).queries) :
    R.RunsWithinUnder allows bound :=
  ⟨cost_le, fun input ↦ (certificate.resolvesInUnder _).mono (rank_init_le input),
    certificate.traceProgressUnder⟩

end RankedRunCertificate

/-! ## Resolution from bounded prefixes -/

/-- A uniform bound on every conforming prefix, together with syntactic progress, supplies
branchwise resolution.

This lemma closes a useful proof gap between the pathwise and inductive parts of
`RunsWithinUnder`. Progress is essential at budget zero: without it a pending query with no
allowed answers would make `ResolvesInUnder` hold vacuously. -/
theorem resolvesInUnder_of_traceLength_le (R : QuantitativeRealization Q bd)
    (allows : ∀ position, p.B position → Prop) (start : R.machine.State) (queries : ℕ)
    (length_le : ∀ {finish : R.machine.State} (trace : R.ExecutionTrace start finish),
      trace.Conforms allows → trace.length ≤ queries)
    (progress : ∀ {state : R.machine.State} (trace : R.ExecutionTrace start state),
      trace.Conforms allows → ∀ {position : p.A} {next : p.B position → R.machine.State},
        R.machine.view state = Sum.inr ⟨position, next⟩ → ∃ direction, allows position direction) :
    R.machine.ResolvesInUnder allows queries start := by
  induction queries generalizing start with
  | zero =>
      rcases hview : R.machine.view start with value | ⟨position, next⟩
      · exact R.machine.resolvesInUnder_return allows 0 start value hview
      · obtain ⟨direction, hAllows⟩ := progress (.nil start) trivial hview
        simpa [QuantitativeRealization.ExecutionTrace.length] using
          length_le (.query hview direction (.nil (next direction))) ⟨hAllows, trivial⟩
  | succ queries ih =>
      rcases hview : R.machine.view start with value | ⟨position, next⟩
      · exact R.machine.resolvesInUnder_return allows (queries + 1) start value hview
      · rw [R.machine.resolvesInUnder_query_succ_iff allows queries start position next hview]
        refine fun direction hAllows ↦ ih (next direction) (fun trace htrace ↦ ?_)
          fun trace htrace ↦ progress (.query hview direction trace) ⟨hAllows, htrace⟩
        simpa [QuantitativeRealization.ExecutionTrace.length] using
          length_le (.query hview direction trace) ⟨hAllows, htrace⟩

/-! ## Initialization replacement -/

omit [DecidableEq p.A] in
/-- Replacing only a computation's initialization leaves relation-restricted resolution from an
already selected state unchanged. -/
theorem resolvesInUnder_setInit_iff (M : DynComputation.{u} p A B)
    (allows : ∀ position, p.B position → Prop) {D : Type u} (init : D → M.State) (k : ℕ)
    (state : M.State) :
    (M.setInit init).ResolvesInUnder allows k state ↔ M.ResolvesInUnder allows k state := by
  induction k generalizing state with
  | zero => simp [resolvesInUnder_zero]
  | succ k ih =>
    rcases hview : M.view state with value | ⟨position, next⟩ <;>
      simp [ResolvesInUnder, hview, ih]

/-! ## Input precomposition -/

section Precomp

variable [Q.HasCategory] {D : Type u} {inputRep : C.Str D} {f : D → A}

namespace QuantitativeRealization.ExecutionTrace

/-- Regard a source trace as a trace of an input-precomposed realization.

Precomposition changes only initialization, so hidden states, views, and transitions are shared
definitionally. `ofPrecomp` transports back, and the two are mutually inverse. -/
def toPrecomp (R : QuantitativeRealization Q bd) (code : Q.Realizer inputRep bd.input f)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (R.precomp code).ExecutionTrace start finish :=
  match trace with
  | .nil state => .nil (R := R.precomp code) state
  | .query view_eq direction tail =>
      .query (R := R.precomp code) view_eq direction (toPrecomp R code tail)

/-- Forget the changed initialization of an input-precomposed trace.

This is the two-sided inverse of `toPrecomp` (`ofPrecomp_toPrecomp`, `toPrecomp_ofPrecomp`). It
preserves conformance and cost (`conforms_ofPrecomp`, `cost_ofPrecomp`), so a pathwise bound
established for `R` applies verbatim to traces of `R.precomp code`. -/
def ofPrecomp (R : QuantitativeRealization Q bd) (code : Q.Realizer inputRep bd.input f)
    {start finish : R.machine.State} (trace : (R.precomp code).ExecutionTrace start finish) :
    R.ExecutionTrace start finish :=
  match trace with
  | .nil state => .nil (R := R) state
  | .query view_eq direction tail =>
      .query (R := R) view_eq direction (ofPrecomp R code tail)

/-- Transporting a source trace into an input-precomposed realization and forgetting the changed
initialization recovers it, so `ofPrecomp` is a left inverse of `toPrecomp`; `toPrecomp_ofPrecomp`
is the converse round trip. -/
@[simp] theorem ofPrecomp_toPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) :
    (trace.toPrecomp R code).ofPrecomp R code = trace := by
  induction trace <;> simp [toPrecomp, ofPrecomp, *]

/-- Forgetting an input-precomposed trace's initialization and transporting it back recovers it, so
`toPrecomp` is a left inverse of `ofPrecomp`; `ofPrecomp_toPrecomp` is the converse round trip. -/
@[simp] theorem toPrecomp_ofPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : (R.precomp code).ExecutionTrace start finish) :
    (trace.ofPrecomp R code).toPrecomp R code = trace :=
  match trace with
  | .nil _ => rfl
  | .query _ _ tail => congrArg _ (toPrecomp_ofPrecomp R code tail)

/-- Transporting a source trace into an input-precomposed realization preserves conformance, so a
query contract verified for `R` transfers verbatim to the transported trace; the companion
`conforms_ofPrecomp` states the same for the backward transport. -/
@[simp] theorem conforms_toPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) (allows : ∀ position, p.B position → Prop)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.toPrecomp R code).Conforms allows ↔ trace.Conforms allows := by
  induction trace <;> simp [toPrecomp, Conforms, *]

/-- Forgetting the changed initialization of an input-precomposed trace preserves conformance, so a
query contract verified for `R` transfers verbatim to traces of `R.precomp code`; the companion
`conforms_toPrecomp` states the same for the forward transport. -/
@[simp] theorem conforms_ofPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) (allows : ∀ position, p.B position → Prop)
    {start finish : R.machine.State} (trace : (R.precomp code).ExecutionTrace start finish) :
    (trace.ofPrecomp R code).Conforms allows ↔ trace.Conforms allows := by
  rw [← conforms_toPrecomp R code allows (trace.ofPrecomp R code), toPrecomp_ofPrecomp]

/-- Input precomposition leaves a transported trace's cost unchanged, because it rewires only
initialization while sharing the head, transition, state and interface encodings; the extra
initialization work is charged separately by `executionCost_toPrecomp_le`. -/
@[simp] theorem cost_toPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) : (trace.toPrecomp R code).cost = trace.cost := by
  induction trace with
  | nil => rfl
  | query _ _ _ ih => exact congrArg _ ih

/-- Forgetting an input-precomposed trace's changed initialization leaves its cost unchanged, so a
pathwise cost bound proved for `R` applies verbatim to traces of `R.precomp code`.

This is `cost_toPrecomp` read through the round trip `toPrecomp_ofPrecomp`; use it with
`conforms_ofPrecomp` to pull a conforming precomposed trace back to the source realization. -/
@[simp] theorem cost_ofPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : (R.precomp code).ExecutionTrace start finish) :
    (trace.ofPrecomp R code).cost = trace.cost := by
  rw [← cost_toPrecomp R code (trace.ofPrecomp R code), toPrecomp_ofPrecomp]

/-- Input precomposition leaves trace length unchanged, because `toPrecomp` rewrites only the
initialization and keeps the visible query-answer steps in bijection. -/
@[simp] theorem length_toPrecomp (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) : (trace.toPrecomp R code).length = trace.length := by
  induction trace <;> simp [toPrecomp, length, *]

end QuantitativeRealization.ExecutionTrace

/-- The only additional resource charged by input precomposition is the executable input map and
the backend's certified composition overhead.

Only `work` receives an additional allowance, supplied by `cost_initCode_precomp_le`;
`queries`, `traffic` and the two peak sizes are transported unchanged. Compare
`ExecutionTrace.cost_toPrecomp`, which relates the two trace costs alone and therefore charges
neither initialization nor the final readout. -/
theorem QuantitativeRealization.executionCost_toPrecomp_le (R : QuantitativeRealization Q bd)
    (code : Q.Realizer inputRep bd.input f) (input : D) {finish : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init (f input)) finish) :
    (R.precomp code).executionCost input (trace.toPrecomp R code) ≤
      ExecutionCost.ofWork (Q.cost code input + Q.composeOverhead code R.initCode input) +
        R.executionCost (f input) trace := by
  -- `omega` compares the five components against these facts, so each shared encoding is read at
  -- the precomposed boundary `bd.withInput inputRep`: rewriting it away would desynchronise the
  -- implicit representation arguments and hide the equations from `omega`.
  have hinit := R.cost_initCode_precomp_le code input
  have hcost := QuantitativeRealization.ExecutionTrace.cost_toPrecomp R code trace
  have hhead := R.cost_headCode_precomp code finish
  have hstate := R.size_state_precomp code finish
  have hheadSize : Q.size (bd.withInput inputRep).head ((R.precomp code).machine.head finish) =
      Q.size bd.head (R.machine.head finish) := R.size_head_precomp code finish
  unfold QuantitativeRealization.executionCost
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ExecutionCost.work_add, ExecutionCost.work_observe, ExecutionCost.queries_add,
      ExecutionCost.queries_observe, ExecutionCost.traffic_add, ExecutionCost.traffic_observe,
      ExecutionCost.peakStateSize_add, ExecutionCost.peakStateSize_observe,
      ExecutionCost.peakHeadSize_add, ExecutionCost.peakHeadSize_observe, ExecutionCost.ofWork,
      hcost] <;> omega

/-- Input precomposition preserves restricted pathwise bounds, using the backend's certified
upper bound for initialization overhead on top of the source bound. -/
theorem QuantitativeRealization.RunsWithinUnder.precomp {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : A → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) (code : Q.Realizer inputRep bd.input f) :
    (R.precomp code).RunsWithinUnder allows fun input ↦ ExecutionCost.ofWork
      (Q.cost code input + Q.composeOverhead code R.initCode input) + bound (f input) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input finish trace htrace
    rw [← QuantitativeRealization.ExecutionTrace.toPrecomp_ofPrecomp R code trace]
    exact (R.executionCost_toPrecomp_le code input _).trans <| ExecutionCost.add_le_add le_rfl <|
      h.cost_le (f input) _ ((trace.conforms_ofPrecomp R code allows).mpr htrace)
  · -- Only `work` grows, so the query budget is the source one at the rewired initial state.
    intro input
    simpa [QuantitativeRealization.precomp] using
      (resolvesInUnder_setInit_iff R.machine allows (R.machine.init ∘ f)
        (bound (f input)).queries (R.machine.init (f input))).mpr (h.resolvesIn (f input))
  · intro input state trace htrace position next hview
    exact h.traceProgress (f input) (trace.ofPrecomp R code)
      ((trace.conforms_ofPrecomp R code allows).mpr htrace)
      (by simpa [QuantitativeRealization.precomp] using hview)

end Precomp

/-! ## Result postcomposition -/

section MapResult

variable [Q.HasCategory] [Q.HasSum] {D : Type u} {outRep : C.Str D} {f : B → D}

omit [DecidableEq p.A] in
/-- A query exposed after mapping return values was already the same source query.
`DynComputation.mapResult_view` is the underlying view equation and gives the converse. -/
theorem view_eq_query_of_mapResult_view_eq_query (M : DynComputation.{u} p A B) {state : M.State}
    {position : p.A} {next : p.B position → M.State}
    (view_eq : (M.mapResult f).view state = Sum.inr ⟨position, next⟩) :
    M.view state = Sum.inr ⟨position, next⟩ := by
  aesop

namespace QuantitativeRealization.ExecutionTrace

/-- Transport a trace through result postcomposition. Visible queries, typed answers, and hidden
states are preserved; `ofMapResult` transports back. -/
def toMapResult (R : QuantitativeRealization Q bd) (code : Q.Realizer bd.out outRep f)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (R.mapResult code).ExecutionTrace start finish :=
  match trace with
  | .nil state => .nil (R := R.mapResult code) state
  | .query view_eq direction tail =>
      .query (R := R.mapResult code)
        (by
          change (R.machine.mapResult f).view _ = _
          rw [DynComputation.mapResult_view, view_eq]) direction
        (toMapResult R code tail)

/-- Recover the source trace underlying result postcomposition. This is a left inverse of
`toMapResult` (`ofMapResult_toMapResult`), and the recovered trace conforms to a query contract
exactly when the given one does (`conforms_ofMapResult`). -/
def ofMapResult (R : QuantitativeRealization Q bd) (code : Q.Realizer bd.out outRep f)
    {start finish : R.machine.State} (trace : (R.mapResult code).ExecutionTrace start finish) :
    R.ExecutionTrace start finish :=
  match trace with
  | .nil state => .nil (R := R) state
  | .query view_eq direction tail =>
      .query (R := R) (view_eq_query_of_mapResult_view_eq_query R.machine view_eq) direction
        (ofMapResult R code tail)

/-- Transporting a source trace through result postcomposition and recovering it returns the
original trace, so `ofMapResult` is a left inverse of `toMapResult` and the transport is injective.
The companions `conforms_toMapResult` and `length_toMapResult` carry the query contract and the
step count across the same transport. -/
@[simp] theorem ofMapResult_toMapResult (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) :
    (trace.toMapResult R code).ofMapResult R code = trace := by
  induction trace <;> simp [toMapResult, ofMapResult, *]

/-- Transporting a source trace through result postcomposition preserves conformance, so a query
contract verified for `R` transfers verbatim to the transported trace; the companion
`conforms_ofMapResult` states the same for the backward transport. -/
@[simp] theorem conforms_toMapResult (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f) (allows : ∀ position, p.B position → Prop)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    (trace.toMapResult R code).Conforms allows ↔ trace.Conforms allows := by
  induction trace <;> simp [toMapResult, Conforms, *]

/-- Recovering the source trace underlying result postcomposition preserves conformance, so a
query contract verified for `R.mapResult code` transfers verbatim to the recovered trace; the
companion `conforms_toMapResult` states the same for the forward transport. -/
@[simp] theorem conforms_ofMapResult (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f) (allows : ∀ position, p.B position → Prop)
    {start finish : R.machine.State} (trace : (R.mapResult code).ExecutionTrace start finish) :
    (trace.ofMapResult R code).Conforms allows ↔ trace.Conforms allows := by
  fun_induction ofMapResult R code trace <;> simp [Conforms, *]

/-- Result postcomposition leaves trace length unchanged, because `toMapResult` rewrites only the
returned value and keeps the visible query-answer steps in bijection. -/
@[simp] theorem length_toMapResult (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f) {start finish : R.machine.State}
    (trace : R.ExecutionTrace start finish) : (trace.toMapResult R code).length = trace.length := by
  induction trace <;> simp [toMapResult, length, *]

end QuantitativeRealization.ExecutionTrace

omit [DecidableEq p.A] in
/-- Mapping returned values preserves relation-restricted resolution exactly.

The equivalence holds at each budget `k` separately, so it rewrites in either direction without a
monotonicity step; `resolvesInUnder_setInit_iff` is the analogue for initialization replacement. -/
theorem resolvesInUnder_mapResult_iff (M : DynComputation.{u} p A B)
    (allows : ∀ position, p.B position → Prop) (k : ℕ) (state : M.State) :
    (M.mapResult f).ResolvesInUnder allows k state ↔ M.ResolvesInUnder allows k state := by
  induction k generalizing state <;>
    rcases hview : M.view state with value | ⟨position, next⟩ <;> simp [ResolvesInUnder, *]

/-- An explicit pathwise account of the backend overhead introduced by result postcomposition.

This certificate deliberately compares exact target cost with exact source cost. It does not infer
that sum elimination, composition, or result encoding is free.

`QuantitativeRealization.RunsWithinUnder.mapResult` consumes it, charging `overhead` on top of the
source bound. `SeqCompCostCertificate` is the sequential-composition analogue, whose source cost
comes from an exact phase decomposition rather than from a single reindexed trace. -/
structure MapResultCostCertificate (R : QuantitativeRealization Q bd)
    (code : Q.Realizer bd.out outRep f) (allows : ∀ position, p.B position → Prop) where
  /-- Input-indexed resource allowance for the assembled result readout. -/
  overhead : A → ExecutionCost
  /-- Every conforming target prefix costs at most its source prefix plus the allowance. -/
  cost_le : ∀ input {finish : R.machine.State}
      (trace : (R.mapResult code).ExecutionTrace ((R.mapResult code).machine.init input) finish),
      trace.Conforms allows → (R.mapResult code).executionCost input trace ≤
        R.executionCost input (trace.ofMapResult R code) + overhead input

/-- Result postcomposition preserves restricted bounds under an explicit pathwise backend-cost
certificate. Control-flow termination and progress are transported generically, so `certificate`
carries the whole cost gap. `QuantitativeRealization.RunsWithinUnder.precomp` is the input-side
analogue, where the overhead comes from a backend law instead of a supplied certificate. -/
theorem QuantitativeRealization.RunsWithinUnder.mapResult {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : A → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) (code : Q.Realizer bd.out outRep f)
    (certificate : MapResultCostCertificate R code allows) :
    (R.mapResult code).RunsWithinUnder allows fun input ↦
      bound input + certificate.overhead input := by
  refine ⟨?_, ?_, ?_⟩
  · intro input finish trace htrace
    exact (certificate.cost_le input trace htrace).trans <| ExecutionCost.add_le_add
      (h.cost_le input _ ((trace.conforms_ofMapResult R code allows).mpr htrace)) le_rfl
  · exact fun input ↦ (resolvesInUnder_mapResult_iff R.machine allows _ _).mpr <|
      (h.resolvesIn input).mono (by simp)
  · intro input state trace htrace position next hview
    exact h.traceProgress input (trace.ofMapResult R code)
      ((trace.conforms_ofMapResult R code allows).mpr htrace)
      (view_eq_query_of_mapResult_view_eq_query R.machine hview)

end MapResult

/-! ## Sequential composition -/

section SeqComp

variable [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive]
  {D : Type u} {outRep : C.Str D}

namespace QuantitativeRealization.ExecutionTrace

/-- Embed a first-phase trace in the left summand of a sequentially composed realization.

`toSeqCompRight` is the second-phase counterpart on `Sum.inr`, and `conforms_toSeqCompLeft`
carries a query contract across this embedding. -/
def toSeqCompLeft (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) {start finish : R₁.machine.State}
    (trace : R₁.ExecutionTrace start finish) :
    (R₁.seqComp R₂).ExecutionTrace (Sum.inl start) (Sum.inl finish) :=
  match trace with
  | .nil state => .nil (R := R₁.seqComp R₂) (Sum.inl state)
  | .query view_eq direction tail =>
      .query (R₁.machine.seqComp_view_inl_of_query R₂.machine view_eq) direction
        (toSeqCompLeft R₁ R₂ tail)

/-- Embed a second-phase trace in the right summand of a sequentially composed realization.

`toSeqCompLeft` is the first-phase counterpart on `Sum.inl`, and `conforms_toSeqCompRight`
carries a query contract across this embedding. -/
def toSeqCompRight (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) {start finish : R₂.machine.State}
    (trace : R₂.ExecutionTrace start finish) :
    (R₁.seqComp R₂).ExecutionTrace (Sum.inr start) (Sum.inr finish) :=
  match trace with
  | .nil state => .nil (R := R₁.seqComp R₂) (Sum.inr state)
  | .query (next := next) view_eq direction tail =>
      .query (next := fun answer ↦ Sum.inr (next answer))
        (by
          change (R₁.machine.seqComp R₂.machine).view (Sum.inr start) = _
          rw [R₁.machine.seqComp_view_inr, view_eq]
          rfl) direction
        (toSeqCompRight R₁ R₂ tail)

/-- Embedding a first-phase trace in the left summand preserves conformance, so a query contract
verified for `R₁` transfers verbatim to the embedded trace; the companion `conforms_toSeqCompRight`
states the same for the second-phase embedding. -/
@[simp] theorem conforms_toSeqCompLeft (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) (allows : ∀ position, p.B position → Prop)
    {start finish : R₁.machine.State} (trace : R₁.ExecutionTrace start finish) :
    (trace.toSeqCompLeft R₁ R₂).Conforms allows ↔ trace.Conforms allows := by
  induction trace <;> simp [toSeqCompLeft, Conforms, *]

/-- Embedding a second-phase trace on the `Sum.inr` side of a sequential composition leaves its
query contract unchanged: the composite issues exactly the queries of `trace`, so `allows` neither
gains nor discharges an obligation. `conforms_toSeqCompLeft` is the first-phase analogue. -/
@[simp] theorem conforms_toSeqCompRight (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) (allows : ∀ position, p.B position → Prop)
    {start finish : R₂.machine.State} (trace : R₂.ExecutionTrace start finish) :
    (trace.toSeqCompRight R₁ R₂).Conforms allows ↔ trace.Conforms allows := by
  induction trace <;> simp [toSeqCompRight, Conforms, *]

end QuantitativeRealization.ExecutionTrace

/-- Source traces underlying a prefix of a sequentially composed machine.

The three constructors distinguish a prefix still exposing a first-phase query, a completed
first phase before the second phase has made a query, and a prefix that has crossed into the
right state summand. The handoff constructor includes the zero-length second-phase prefix; this
accounts for the second initialization and its first readout even when no second-phase query has
yet occurred.

Build a value with `QuantitativeRealization.ExecutionTrace.seqCompSource`, which decomposes a
composite prefix that starts in the left summand, or with `prependLeft`, which extends a
decomposition by one first-phase query. `length`, `Conforms` and `cost` read a decomposition
back, and `length_le`, `cost_le` and `response_exists` turn phase-local bounds into bounds on the
composite. `SeqCompAnyTraceSource.fromLeft` embeds this family when the starting summand is not
fixed; `SeqCompRightTraceSource` is the separate family for prefixes that already start on the
right. -/
inductive SeqCompTraceSource (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.mid outRep)) (start : R₁.machine.State) :
    (R₁.machine.State ⊕ R₂.machine.State) → Type u where
  /-- The prefix remains in phase one at a state that exposes another phase-one query. -/
  | left {finish : R₁.machine.State} (trace : R₁.ExecutionTrace start finish) {position : p.A}
      {next : p.B position → R₁.machine.State}
      (view_eq : R₁.machine.view finish = Sum.inr ⟨position, next⟩) :
      SeqCompTraceSource R₁ R₂ start (Sum.inl finish)
  /-- Phase one has returned, but the prefix contains no second-phase query yet. -/
  | handoff {finish : R₁.machine.State} {value : B} (trace : R₁.ExecutionTrace start finish)
      (view_eq : R₁.machine.view finish = Sum.inl value) :
      SeqCompTraceSource R₁ R₂ start (Sum.inl finish)
  /-- A completed first-phase trace followed by a second-phase trace. -/
  | right {leftFinish : R₁.machine.State} {value : B} {rightFinish : R₂.machine.State}
      (left : R₁.ExecutionTrace start leftFinish)
      (view_eq : R₁.machine.view leftFinish = Sum.inl value)
      (right : R₂.ExecutionTrace (R₂.machine.init value) rightFinish) :
      SeqCompTraceSource R₁ R₂ start (Sum.inr rightFinish)

namespace SeqCompTraceSource

variable {R₁ : QuantitativeRealization Q bd}
  {R₂ : QuantitativeRealization Q (bd.mid outRep)} {start : R₁.machine.State}

/-- Number of visible query-answer transitions represented by the phase-local traces.

The `left` and `handoff` prefixes count only the first-phase trace, while `right` adds both
phase counts. `SeqCompRightTraceSource.length` is the counterpart for a prefix confined to the
second phase, and `SeqCompAnyTraceSource.length` dispatches on the starting summand. -/
def length : {finish : R₁.machine.State ⊕ R₂.machine.State} →
    SeqCompTraceSource R₁ R₂ start finish → ℕ
  | _, .left trace _ => trace.length
  | _, .handoff trace _ => trace.length
  | _, .right leftTrace _ rightTrace => leftTrace.length + rightTrace.length

/-- Prepend one first-phase query to a decomposition starting at its selected child.

The constructor shape is preserved: the query is pushed onto the first-phase trace, while a
handoff readout and any second-phase trace are carried through unchanged. `length_prependLeft`
and `conforms_prependLeft` read the resulting length and answer contract off the new query. -/
def prependLeft {state : R₁.machine.State} {position : p.A} {next : p.B position → R₁.machine.State}
    (view_eq : R₁.machine.view state = Sum.inr ⟨position, next⟩) (direction : p.B position)
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompTraceSource R₁ R₂ (next direction) finish) :
    SeqCompTraceSource R₁ R₂ state finish :=
  match source with
  | .left trace finalView => .left (.query view_eq direction trace) finalView
  | .handoff trace finalView => .handoff (.query view_eq direction trace) finalView
  | .right leftTrace returned rightTrace =>
      .right (.query view_eq direction leftTrace) returned rightTrace

omit [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive] in
/-- Prepending a first-phase query lengthens a phase decomposition by exactly one step.

The extra query is absorbed by the first-phase trace in every constructor, so a `right`
decomposition keeps its second-phase count unchanged; `conforms_prependLeft` is the
answer-contract counterpart. -/
@[simp] theorem length_prependLeft {state : R₁.machine.State} {position : p.A}
    {next : p.B position → R₁.machine.State}
    (view_eq : R₁.machine.view state = Sum.inr ⟨position, next⟩) (direction : p.B position)
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompTraceSource R₁ R₂ (next direction) finish) :
    (source.prependLeft view_eq direction).length = source.length + 1 := by
  cases source <;> simp [prependLeft, length,
    QuantitativeRealization.ExecutionTrace.length, Nat.add_right_comm]

/-- Whether every answer appearing in the projected source traces obeys an answer contract.

A `left` or `handoff` prefix constrains only the first-phase trace, while `right` constrains
both phase traces. `SeqCompRightTraceSource.Conforms` is the counterpart for a prefix confined
to the second phase, and `SeqCompAnyTraceSource.Conforms` dispatches on the starting summand. -/
def Conforms (allows : ∀ position, p.B position → Prop) :
    {finish : R₁.machine.State ⊕ R₂.machine.State} → SeqCompTraceSource R₁ R₂ start finish → Prop
  | _, .left trace _ => trace.Conforms allows
  | _, .handoff trace _ => trace.Conforms allows
  | _, .right leftTrace _ rightTrace => leftTrace.Conforms allows ∧ rightTrace.Conforms allows

omit [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive] in
/-- A prepended first-phase query conforms to an answer contract exactly when the new answer is
allowed and the shorter decomposition already conforms.

The conjunction is right-nested, matching `QuantitativeRealization.ExecutionTrace.Conforms` on
`.query`, so repeated rewriting peels one query at a time instead of accumulating bracketing in
the `right` case. `length_prependLeft` is the length counterpart on the same construction. -/
@[simp] theorem conforms_prependLeft (allows : ∀ position, p.B position → Prop)
    {state : R₁.machine.State} {position : p.A} {next : p.B position → R₁.machine.State}
    (view_eq : R₁.machine.view state = Sum.inr ⟨position, next⟩) (direction : p.B position)
    {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompTraceSource R₁ R₂ (next direction) finish) :
    (source.prependLeft view_eq direction).Conforms allows ↔
      allows position direction ∧ source.Conforms allows := by
  cases source <;>
    simp [prependLeft, Conforms, QuantitativeRealization.ExecutionTrace.Conforms, and_assoc]

/-- Exact source-machine cost represented by a phase decomposition.

This is the realized cost of the phase-local traces, not a bound: the handoff case charges the
second machine's initialization and first readout through its empty second-phase prefix.
`queries_cost` reads the `queries` component back as `length`, and `cost_le` bounds the whole
cost by a first-phase bound plus the reachable second-phase envelope. -/
def cost (input : A) : {finish : R₁.machine.State ⊕ R₂.machine.State} →
    SeqCompTraceSource R₁ R₂ (R₁.machine.init input) finish → ExecutionCost
  | _, .left trace _ => R₁.executionCost input trace
  | _, .handoff (value := value) trace _ =>
      R₁.executionCost input trace + R₂.executionCost value (.nil (R₂.machine.init value))
  | _, .right (value := value) leftTrace _ rightTrace =>
      R₁.executionCost input leftTrace + R₂.executionCost value rightTrace

omit [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive] in
/-- The query component of a phase source's cost is its exact syntactic length.

Backend work, encoded sizes and handoff overhead are invisible to `queries`, so the identity
needs no cost certificate; `SeqCompTraceSource.length_le` rewrites backwards along it to turn a
pathwise cost bound into a prefix-length bound. The single-phase counterpart is
`QuantitativeRealization.ExecutionTrace.queries_cost`. -/
@[simp] theorem queries_cost (input : A) {finish : R₁.machine.State ⊕ R₂.machine.State}
    (source : SeqCompTraceSource R₁ R₂ (R₁.machine.init input) finish) :
    (source.cost input).queries = source.length := by
  cases source <;> simp [cost, length, QuantitativeRealization.ExecutionTrace.length]

end SeqCompTraceSource

/-- A second-phase trace projected from a composite prefix already in the right summand.

`R₁` only fixes the left summand of the state index; the projected trace itself lives entirely
in `R₂`. The single constructor pins the `finish` index to `Sum.inr`, so matching on a value
also refines that index.

Values arrive wrapped in `SeqCompAnyTraceSource.fromRight`, which
`QuantitativeRealization.ExecutionTrace.seqCompAnySource` returns for a composite prefix that
already starts in the second phase. `length` and `Conforms` read the projection back.
`SeqCompTraceSource` is the counterpart family for prefixes that start in the left summand. -/
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
