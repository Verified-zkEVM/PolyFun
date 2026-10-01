/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Strength
public import PolyFun.PFunctor.Dynamical.DynComputation.WrapState

/-!
# Quantitative substitution of one-query stateful handlers

`QuantitativeRealization.wrapState` runs an adversary realization `R` over interface `p` against a
stateful lens `L : StateLens p r σ` that carries executable code
(`StateLens.QuantitativelyAdmissible`):
- `onPos` computes the forwarded inner query from the outer query and the handler state;
- `onPull` partially pulls a tagged inner answer back to a tagged outer answer and the next handler
  state.

The product machine is `DynComputation.wrapState`, with state `R.State × σ`.

Every product step is one adversary step, so the trace correspondence is one-to-one
(`exists_source_trace`). Queries are preserved exactly, answer contracts transfer along the lens,
and the work of a product step is bounded by the adversary step plus the handler's per-call work
and structural carry. The flattened `update?` must recompute the adversary's readout to know which
query is pending, so the adversary's readout work is charged twice and the bound doubles the
adversary's work (`ExecutionCost.handled`).

## Main results

* `QuantitativeRealization.wrapState` and `wrapState_implements`: construction and semantics.
* `resolvesInUnder_wrapState`: resolution transfers along the lens contract.
* `WrapStateCostCertificate`: per-step allowances for the handler's work, structural carry, inner
  traffic and handler-state size, over conformingly reachable product states.
* `RunsWithinUnder.wrapState`: work at most `2·work_A + init + (q + 1)·head + q·update`, queries
  equal to the adversary's, traffic at most `q` times the per-step inner traffic, and peak sizes
  shifted by the carries. It needs a contract (allowed inner answers pull back to allowed outer
  answers) and progress (every query the adversary can still answer has an allowed inner answer).
* `WrapStateCostCertificate.ofLaws` and `RunsWithinUnder.wrapState_of_laws`: under the cost laws,
  the certificate holds from handler invariants along conforming product runs, namely a
  handler-state size bound, per-call work bounds for the lens code and a per-step inner-traffic
  bound.
-/

@[expose] public section

universe u v w

namespace PFunctor

namespace DynSystem.DynComputation

section StepMaps

variable {p r : PFunctor.{u, u}} {σ α β : Type u}

attribute [local implicit_reducible] PFunctor.Idx

/-- The product readout returns with the handler state, or exposes the lens image of `M`'s
query. -/
theorem head_wrapState (M : DynComputation.{u} p α β) (L : StateLens p r σ)
    (state : M.State × σ) :
    (M.wrapState L).head state = Sum.elim (fun value ↦ Sum.inl (value, state.2))
      (fun position ↦ Sum.inr (L.pos (position, state.2))) (M.head state.1) := by
  rw [head_eq_sumMap_view, head_eq_sumMap_view]
  rcases hview : M.view state.1 with value | ⟨position, next⟩
  · rw [view_wrapState_of_return M L hview]; rfl
  · rw [view_wrapState_of_query M L hview]; rfl

/-- The product transition pulls an inner answer back through the lens, then steps `M`. -/
theorem update?_wrapState [DecidableEq p.A] [DecidableEq r.A] (M : DynComputation.{u} p α β)
    (L : StateLens p r σ) (state : M.State × σ) (index : r.Idx) :
    (M.wrapState L).update? (state, index) =
      (L.pullHead β ((M.head state.1, state.2), index)).bind fun pulled ↦
        (M.update? (state.1, pulled.1)).map fun next ↦ (next, pulled.2) := by
  obtain ⟨iposition, idirection⟩ := index
  rcases hview : M.view state.1 with value | ⟨position, next⟩
  · rw [update?_of_view_return (M.wrapState L) (view_wrapState_of_return M L hview),
      head_eq_inl_of_view M hview]
    rfl
  · have hcomp := view_wrapState_of_query M L hview
    rw [head_eq_inr_of_view M hview]
    by_cases h : iposition = L.pos (position, state.2)
    · subst h
      rw [update?_of_view_query (M.wrapState L) hcomp idirection]
      change _ = Option.bind (dite _ _ _) _
      rw [dite_eq_left rfl, Option.bind_some, update?_of_view_query M hview]
      rfl
    · rw [update?_of_view_query_of_ne (M.wrapState L) hcomp h]
      change none = Option.bind (dite _ _ _) _
      rw [dite_eq_right h]
      rfl

end StepMaps

variable {p r : PFunctor.{u, u}} {C : StepClass.{u, v}} [P : C.HasProd]
  [S : C.HasSum] [O : C.HasOption] [DecidableEq p.A] [DecidableEq r.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {A B σ : Type u}
  {bd : Boundary C p A B}

namespace Boundary

/-- The boundary of a product machine running against a stateful handler: inputs and results
carry the handler state, and the interface is the handler's inner interface. -/
@[implicit_reducible]
def withHandler (bd : Boundary C p A B) (stateRep : C.Str σ) (posRep : C.Str r.A)
    (idxRep : C.Str r.Idx) : Boundary C r (A × σ) (B × σ) :=
  ⟨P.prod bd.input stateRep, P.prod bd.out stateRep, posRep, idxRep⟩

omit [S : C.HasSum] [O : C.HasOption] [DecidableEq p.A] [DecidableEq r.A] in
@[simp] theorem withHandler_pos (bd : Boundary C p A B) (stateRep : C.Str σ)
    (posRep : C.Str r.A) (idxRep : C.Str r.Idx) :
    (bd.withHandler stateRep posRep idxRep).pos = posRep := rfl

omit [S : C.HasSum] [O : C.HasOption] [DecidableEq p.A] [DecidableEq r.A] in
@[simp] theorem withHandler_idx (bd : Boundary C p A B) (stateRep : C.Str σ)
    (posRep : C.Str r.A) (idxRep : C.Str r.Idx) :
    (bd.withHandler stateRep posRep idxRep).idx = idxRep := rfl

end Boundary

/-- Executable evidence for a stateful lens: the forwarded inner query, and the partial pullback
of a tagged inner answer (absorbing the returned case, as `Lens.pullHeadIdx` does). -/
structure _root_.PFunctor.StateLens.QuantitativelyAdmissible
    (Q : QuantitativeStepClass.{u, v, w} C) (bd : Boundary C p A B) (stateRep : C.Str σ)
    (posRep : C.Str r.A) (idxRep : C.Str r.Idx) (L : StateLens p r σ) where
  /-- Executable forwarding of an outer query at a handler state. -/
  onPos : Q.Realizer (P.prod bd.pos stateRep) posRep L.pos
  /-- Executable partial pullback of a tagged inner answer. -/
  onPull : Q.Realizer (P.prod (P.prod bd.head stateRep) idxRep)
    (O.option (P.prod bd.idx stateRep)) (L.pullHead B)

omit [DecidableEq p.A] [DecidableEq r.A] in
/-- Running against a stateful lens transfers relation-restricted resolution along the lens
contract: every allowed inner answer pulls back to an allowed outer answer. -/
theorem resolvesInUnder_wrapState (M : DynComputation.{u} p A B) (L : StateLens p r σ)
    {allowsP : ∀ position, p.B position → Prop} {allowsR : ∀ position, r.B position → Prop}
    (contract : ∀ position state answer, allowsR (L.pos (position, state)) answer →
      allowsP position (L.answer (position, state) answer))
    (k : ℕ) (state : M.State × σ) (h : M.ResolvesInUnder allowsP k state.1) :
    (M.wrapState L).ResolvesInUnder allowsR k state := by
  induction k generalizing state with
  | zero =>
      obtain ⟨value, hview⟩ := (M.resolvesInUnder_zero allowsP state.1).mp h
      exact (M.wrapState L).resolvesInUnder_return allowsR 0 state _
        (view_wrapState_of_return M L hview)
  | succ k ih =>
      rcases hview : M.view state.1 with value | ⟨position, next⟩
      · exact (M.wrapState L).resolvesInUnder_return allowsR _ state _
          (view_wrapState_of_return M L hview)
      · rw [M.resolvesInUnder_query_succ_iff allowsP k _ position next hview] at h
        rw [(M.wrapState L).resolvesInUnder_query_succ_iff allowsR k state _ _
          (view_wrapState_of_query M L hview)]
        exact fun answer hallowed ↦ ih _ (h _ (contract _ _ _ hallowed))

omit [O : C.HasOption] [DecidableEq p.A] [DecidableEq r.A] in
/-- The product readout is encoded within `R`'s readout, the handler state, the forwarded inner
query (if any) and constant overheads. -/
theorem size_head_wrapState_le [QP : Q.HasProd] [PC : Q.HasProdCost] [QS : Q.HasSum]
    [SC : Q.HasSumCost] {stateRep : C.Str σ} {posRep : C.Str r.A} {L : StateLens p r σ}
    (M : DynComputation.{u} p A B) (s : M.State) (st : σ) :
    Q.size (S.sum (P.prod bd.out stateRep) posRep) ((M.wrapState L).head (s, st)) ≤
      Q.size bd.head (M.head s) + Q.size stateRep st + PC.sizeOverhead + SC.sizeOverhead +
        (M.head s).elim (fun _ ↦ 0) (fun position ↦ Q.size posRep (L.pos (position, st))) := by
  rw [head_wrapState]
  change _ ≤ Q.size (S.sum bd.out bd.pos) (M.head s) + _ + _ + _ + _
  rcases M.head s with value | position
  · have h1 := SC.size_inl_le (P.prod bd.out stateRep) posRep (value, st)
    have h2 := PC.size_prod_le bd.out stateRep value st
    have h3 := SC.le_size_inl bd.out bd.pos value
    simp only [Sum.elim_inl]
    omega
  · have h1 := SC.size_inr_le (P.prod bd.out stateRep) posRep (L.pos (position, st))
    simp only [Sum.elim_inr]
    omega

namespace QuantitativeRealization

section WrapState

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive]

/-- The pullback half of the product transition:
`((s, st), j) ↦ (L.pullHead ((R.head s, st), j), s)` — recompute the adversary's readout, pull the
tagged inner answer back through the lens code, and keep the adversary state. -/
def wrapStatePull (R : QuantitativeRealization Q bd) {stateRep : C.Str σ} {posRep : C.Str r.A}
    {idxRep : C.Str r.Idx} {L : StateLens p r σ}
    (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) :
    Q.Realizer (P.prod (P.prod R.state stateRep) idxRep)
      (P.prod (O.option (P.prod bd.idx stateRep)) R.state)
      fun z ↦ (L.pullHead B ((R.machine.head z.1.1, z.1.2), z.2), z.1.1) :=
  QP.pair
    (Q.compose (QuantitativeStepClass.HasProd.pairRight Q QP (d := idxRep)
      (QuantitativeStepClass.HasProd.pairRight Q QP (d := stateRep) R.headCode)) hL.onPull)
    (Q.compose (QP.fst (P.prod R.state stateRep) idxRep) (QP.fst R.state stateRep))

/-- The stepping half of the product transition:
`((i, st'), s) ↦ (R.update? (s, i)).map (·, st')`. -/
def wrapStateStep (R : QuantitativeRealization Q bd) (stateRep : C.Str σ) :
    Q.Realizer (P.prod (P.prod bd.idx stateRep) R.state) (O.option (P.prod R.state stateRep))
      fun w ↦ (R.machine.update? (w.2, w.1.1)).map fun next ↦ (next, w.1.2) :=
  (Q.compose (QuantitativeStepClass.rotate Q bd.idx stateRep R.state)
    (QuantitativeStepClass.carryUpdate Q stateRep R.updateCode)).castFunction (by
      funext w
      rfl)

/-- Quantitative stateful handler substitution for a one-query handler: the adversary
realization `R` runs against the stateful lens `L` in the product machine
`R.machine.wrapState L`, with code assembled from `R`'s code, the lens code and the structural
mixins. -/
@[implicit_reducible]
def wrapState (R : QuantitativeRealization Q bd) (stateRep : C.Str σ) (posRep : C.Str r.A)
    (idxRep : C.Str r.Idx) {L : StateLens p r σ}
    (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) :
    QuantitativeRealization Q (bd.withHandler stateRep posRep idxRep) where
  machine := R.machine.wrapState L
  state := P.prod R.state stateRep
  initCode := QuantitativeStepClass.HasProd.pairRight Q QP (d := stateRep) R.initCode
  headCode := (QuantitativeStepClass.carryReadoutWith Q R.headCode hL.onPos).castFunction (by
    funext state
    rw [head_wrapState])
  updateCode := (Q.compose (R.wrapStatePull hL)
    (QO.bindContext (R.wrapStateStep stateRep))).castFunction (by
      funext z
      obtain ⟨state, index⟩ := z
      rw [update?_wrapState]
      rfl)

/-- The product realization implements stateful substitution of the adversary's program. -/
theorem wrapState_implements (R : QuantitativeRealization Q bd) (stateRep : C.Str σ)
    (posRep : C.Str r.A) (idxRep : C.Str r.Idx) {L : StateLens p r σ}
    (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) {program : A → FreeM p B}
    (h : R.machine.Implements program) :
    (R.wrapState stateRep posRep idxRep hL).machine.Implements
      fun input ↦ L.mapFreeM (program input.1) input.2 :=
  h.wrapState L

/-! ### Cost certificate -/

variable {stateRep : C.Str σ} {posRep : C.Str r.A} {idxRep : C.Str r.Idx}
  {L : StateLens p r σ}

/-- Per-step allowances for running `R` against an executable stateful lens.

`update_le` charges the product transition by `R`'s transition, a recomputed `R` readout and the
`update` allowance, which covers the handler's own per-call work (`onPull`) and structural
carry. `traffic_le` bounds the inner interface's per-step traffic; `state_le` the handler state's
contribution to the encoded product state. All fields quantify over product states reachable
along conforming product traces, so a growing handler state (a cache, a log) is bounded through
an invariant of the actual runs. -/
structure WrapStateCostCertificate (R : QuantitativeRealization Q bd)
    (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep)
    (allowsR : ∀ position, r.B position → Prop) where
  /-- Input-indexed carry allowances. -/
  carry : A × σ → Carry
  /-- Input-indexed per-step inner traffic allowance. -/
  traffic : A × σ → ℕ
  init_le : ∀ input,
    Q.cost (R.wrapState stateRep posRep idxRep hL).initCode input ≤
      Q.cost R.initCode input.1 + (carry input).init
  head_le : ∀ input {state : R.machine.State × σ}
    (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
      ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
    pre.Conforms allowsR →
      Q.cost (R.wrapState stateRep posRep idxRep hL).headCode state ≤
        Q.cost R.headCode state.1 + (carry input).head
  update_le : ∀ input {state : R.machine.State × σ}
    (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
      ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
    pre.Conforms allowsR →
      ∀ {position : p.A} {next : p.B position → R.machine.State},
        R.machine.view state.1 = Sum.inr ⟨position, next⟩ →
          ∀ answer, allowsR (L.pos (position, state.2)) answer →
            Q.cost (R.wrapState stateRep posRep idxRep hL).updateCode
                (state, ⟨L.pos (position, state.2), answer⟩) ≤
              Q.cost R.updateCode (state.1, ⟨position, L.answer (position, state.2) answer⟩) +
                Q.cost R.headCode state.1 + (carry input).update
  traffic_le : ∀ input {state : R.machine.State × σ}
    (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
      ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
    pre.Conforms allowsR →
      ∀ {position : p.A} {next : p.B position → R.machine.State},
        R.machine.view state.1 = Sum.inr ⟨position, next⟩ →
          ∀ answer, allowsR (L.pos (position, state.2)) answer →
            Q.size posRep (L.pos (position, state.2)) +
              Q.size idxRep ⟨L.pos (position, state.2), answer⟩ ≤ traffic input
  state_le : ∀ input {state : R.machine.State × σ}
    (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
      ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
    pre.Conforms allowsR →
      Q.size (R.wrapState stateRep posRep idxRep hL).state state ≤
        Q.size R.state state.1 + (carry input).state
  headSize_le : ∀ input {state : R.machine.State × σ}
    (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
      ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
    pre.Conforms allowsR →
      Q.size (bd.withHandler stateRep posRep idxRep).head
          ((R.wrapState stateRep posRep idxRep hL).machine.head state) ≤
        Q.size bd.head (R.machine.head state.1) + (carry input).headSize

/-- **Trace correspondence.** Every conforming product trace from a conformingly reachable state
has a source trace of `R` with the same length, conforming to the outer contract, whose cost
bounds the product trace's cost: twice the source work plus the per-step carry, the same
queries, inner traffic within the per-step allowance, and shifted peak sizes. -/
theorem exists_source_trace {R : QuantitativeRealization Q bd}
    {hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep}
    {allowsP : ∀ position, p.B position → Prop} {allowsR : ∀ position, r.B position → Prop}
    (cert : WrapStateCostCertificate R hL allowsR)
    (contract : ∀ position state answer, allowsR (L.pos (position, state)) answer →
      allowsP position (L.answer (position, state) answer))
    (input : A × σ) {start finish : (R.wrapState stateRep posRep idxRep hL).machine.State}
    (trace : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace start finish)
    (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
      ((R.wrapState stateRep posRep idxRep hL).machine.init input) start)
    (hpre : pre.Conforms allowsR) (htrace : trace.Conforms allowsR) :
    ∃ source : R.ExecutionTrace start.1 finish.1, source.Conforms allowsP ∧
      source.length = trace.length ∧
      trace.cost.work ≤ 2 * source.cost.work +
        trace.length * ((cert.carry input).head + (cert.carry input).update) ∧
      trace.cost.queries = source.cost.queries ∧
      trace.cost.traffic ≤ trace.length * cert.traffic input ∧
      trace.cost.peakStateSize ≤ source.cost.peakStateSize + (cert.carry input).state ∧
      trace.cost.peakHeadSize ≤ source.cost.peakHeadSize + (cert.carry input).headSize := by
  induction trace with
  | nil state =>
      refine ⟨.nil state.1, trivial, rfl, ?_, rfl, ?_, ?_, ?_⟩ <;>
        simp [QuantitativeRealization.ExecutionTrace.cost]
  | @query state position next finish view_eq direction tail ih =>
      obtain ⟨source, sourceNext, hR, hsig⟩ :=
        R.machine.exists_view_eq_query_of_wrapState L view_eq
      cases hsig
      have hallowed : allowsR (L.pos (source, state.2)) direction := htrace.1
      let pre' := pre.append (.query view_eq direction (.nil _))
      have hpre' : pre'.Conforms allowsR :=
        (QuantitativeRealization.ExecutionTrace.conforms_append pre _).mpr
          ⟨hpre, hallowed, trivial⟩
      obtain ⟨tailSource, htailConforms, htailLength, hw, hq, ht, hs, hh⟩ :=
        ih pre' hpre' htrace.2
      refine ⟨.query hR (L.answer (source, state.2) direction) tailSource,
        ⟨contract _ _ _ hallowed, htailConforms⟩, ?_, ?_⟩
      · simp only [QuantitativeRealization.ExecutionTrace.length, htailLength]
      have hhead := cert.head_le input pre hpre
      have hupdate := cert.update_le input pre hpre hR direction hallowed
      have htraffic := cert.traffic_le input pre hpre hR direction hallowed
      have hstate := cert.state_le input pre hpre
      have hheadSize := cert.headSize_le input pre hpre
      simp only [QuantitativeRealization.ExecutionTrace.cost,
        QuantitativeRealization.ExecutionTrace.length, ExecutionCost.work_add,
        ExecutionCost.work_observe, ExecutionCost.queries_add, ExecutionCost.queries_observe,
        ExecutionCost.traffic_add, ExecutionCost.traffic_observe,
        ExecutionCost.peakStateSize_add, ExecutionCost.peakStateSize_observe,
        ExecutionCost.peakHeadSize_add, ExecutionCost.peakHeadSize_observe,
        ExecutionCost.ofWork, ExecutionCost.query, Boundary.withHandler_pos,
        Boundary.withHandler_idx, Nat.add_mul, Nat.mul_add, Nat.one_mul] at *
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Pathwise transfer: a conforming product run is bounded by a conforming source run of `R`
under `ExecutionCost.handled`. -/
theorem exists_source_executionCost {R : QuantitativeRealization Q bd}
    {hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep}
    {allowsP : ∀ position, p.B position → Prop} {allowsR : ∀ position, r.B position → Prop}
    (cert : WrapStateCostCertificate R hL allowsR)
    (contract : ∀ position state answer, allowsR (L.pos (position, state)) answer →
      allowsP position (L.answer (position, state) answer))
    (input : A × σ) {finish : R.machine.State × σ}
    (trace : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
      ((R.wrapState stateRep posRep idxRep hL).machine.init input) finish)
    (htrace : trace.Conforms allowsR) :
    ∃ source : R.ExecutionTrace (R.machine.init input.1) finish.1, source.Conforms allowsP ∧
      source.length = trace.length ∧
      (R.wrapState stateRep posRep idxRep hL).executionCost input trace ≤
        (R.executionCost input.1 source).handled trace.length (cert.carry input)
          (cert.traffic input) := by
  obtain ⟨source, hconf, hlength, hw, hq, ht, hs, hh⟩ :=
    exists_source_trace cert contract input trace (.nil _) trivial htrace
  refine ⟨source, hconf, hlength, ?_⟩
  have hinit := cert.init_le input
  have hhead := cert.head_le input trace htrace
  have hstate := cert.state_le input trace htrace
  have hheadSize := cert.headSize_le input trace htrace
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [QuantitativeRealization.executionCost, ExecutionCost.handled,
      ExecutionCost.work_add, ExecutionCost.work_observe, ExecutionCost.queries_add,
      ExecutionCost.queries_observe, ExecutionCost.traffic_add, ExecutionCost.traffic_observe,
      ExecutionCost.peakStateSize_add, ExecutionCost.peakStateSize_observe,
      ExecutionCost.peakHeadSize_add, ExecutionCost.peakHeadSize_observe,
      ExecutionCost.ofWork, Nat.add_mul, Nat.mul_add, Nat.one_mul] at * <;>
    omega

/-- **Bounded one-query stateful handler substitution.** If `R` runs within `bound` under the
outer contract, the lens maps allowed inner answers to allowed outer answers, and every query
`R` can still answer has an allowed inner answer, then the product realization runs within the
`handled` bound: twice `R`'s work plus the per-step carry, `R`'s query budget, per-step inner
traffic, and shifted peak sizes. -/
theorem RunsWithinUnder.wrapState {R : QuantitativeRealization Q bd}
    {hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep}
    {allowsP : ∀ position, p.B position → Prop} {allowsR : ∀ position, r.B position → Prop}
    {bound : A → ExecutionCost} (h : R.RunsWithinUnder allowsP bound)
    (cert : WrapStateCostCertificate R hL allowsR)
    (contract : ∀ position state answer, allowsR (L.pos (position, state)) answer →
      allowsP position (L.answer (position, state) answer))
    (progress : ∀ position state, (∃ direction, allowsP position direction) →
      ∃ answer, allowsR (L.pos (position, state)) answer) :
    (R.wrapState stateRep posRep idxRep hL).RunsWithinUnder allowsR fun input ↦
      (bound input.1).handled (bound input.1).queries (cert.carry input) (cert.traffic input) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input finish trace htrace
    obtain ⟨source, hconf, hlength, hcost⟩ :=
      exists_source_executionCost cert contract input trace htrace
    refine hcost.trans (ExecutionCost.handled_mono _ _ (h.cost_le input.1 source hconf) ?_)
    rw [← hlength]
    exact h.traceLength_le input.1 source hconf
  · intro input
    exact resolvesInUnder_wrapState R.machine L contract _ (R.machine.init input.1, input.2)
      (h.resolvesIn input.1)
  · intro input state trace htrace position next hview
    obtain ⟨source, hconf, -, -⟩ := exists_source_executionCost cert contract input trace htrace
    obtain ⟨sourcePosition, sourceNext, hR, hsig⟩ :=
      R.machine.exists_view_eq_query_of_wrapState L hview
    cases hsig
    exact progress _ _ (h.traceProgress input.1 source hconf hR)

/-! ### Per-step costs under cost laws

The product step is `R`'s step, plus a recomputed `R` readout in the transition, plus the
handler's own code (`onPos` on the readout, `onPull` on the transition), plus a constant number
of structural primitives, each charged the combined envelope at a size bounded by the states,
handler states, readout and indices involved. -/

section Laws

variable [CC : Q.HasCompositionCost] [PC : Q.HasProdCost] [SC : Q.HasSumCost]
  [OC : Q.HasOptionCost] [DC : Q.IsDistributiveCost]

omit [SC : Q.HasSumCost] [OC : Q.HasOptionCost] [DC : Q.IsDistributiveCost] in
/-- Product initialization costs `R`'s plus four structural primitives. -/
theorem cost_initCode_wrapState_le (R : QuantitativeRealization Q bd)
    (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) (input : A) (state : σ) :
    Q.cost (R.wrapState stateRep posRep idxRep hL).initCode (input, state) ≤
      Q.cost R.initCode input + 3 * PC.overhead
          (Q.size (P.prod bd.input stateRep) (input, state)) +
        CC.overhead (Q.size bd.input input) :=
  QuantitativeStepClass.cost_pairRight_le Q R.initCode input state

/-- A product readout costs `R`'s readout, `onPos` when `R` exposes a query, and at most ten
structural primitives. -/
theorem cost_headCode_wrapState_le (R : QuantitativeRealization Q bd)
    (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) (s : R.machine.State)
    (st : σ) :
    Q.cost (R.wrapState stateRep posRep idxRep hL).headCode (s, st) ≤ Q.cost R.headCode s +
      (R.machine.head s).elim (fun _ ↦ 0) (fun position ↦ Q.cost hL.onPos (position, st)) +
      10 * QuantitativeStepClass.structOverhead Q (Q.size R.state s +
        Q.size bd.head (R.machine.head s) + Q.size stateRep st +
        Q.size (bd.withHandler stateRep posRep idxRep).head
          ((R.wrapState stateRep posRep idxRep hL).machine.head (s, st)) +
        PC.sizeOverhead + SC.sizeOverhead) := by
  change Q.cost ((QuantitativeStepClass.carryReadoutWith Q R.headCode hL.onPos).castFunction _)
    (s, st) ≤ _
  rw [QuantitativeStepClass.Realizer.cost_castFunction]
  change _ ≤ _ + _ + 10 * QuantitativeStepClass.structOverhead Q (_ + _ + _ +
    Q.size (S.sum (P.prod bd.out stateRep) posRep) ((R.machine.wrapState L).head (s, st)) + _ + _)
  rw [head_wrapState]
  exact QuantitativeStepClass.cost_carryReadoutWith_le Q R.headCode hL.onPos s st

/-- The pullback half costs `R`'s readout, `onPull`, and thirteen structural primitives. -/
theorem cost_wrapStatePull_le (R : QuantitativeRealization Q bd)
    (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) (s : R.machine.State)
    (st : σ) (j : r.Idx) :
    Q.cost (R.wrapStatePull hL) ((s, st), j) ≤
      Q.cost R.headCode s + Q.cost hL.onPull ((R.machine.head s, st), j) +
        13 * QuantitativeStepClass.structOverhead Q (Q.size R.state s + Q.size stateRep st +
          Q.size bd.head (R.machine.head s) + Q.size idxRep j + 2 * PC.sizeOverhead) := by
  set N := Q.size R.state s + Q.size stateRep st + Q.size bd.head (R.machine.head s) +
    Q.size idxRep j + 2 * PC.sizeOverhead with hN
  unfold wrapStatePull
  have hpair := PC.cost_pair_le
    (Q.compose (QuantitativeStepClass.HasProd.pairRight Q QP (d := idxRep)
      (QuantitativeStepClass.HasProd.pairRight Q QP (d := stateRep) R.headCode)) hL.onPull)
    (Q.compose (QP.fst (P.prod R.state stateRep) idxRep) (QP.fst R.state stateRep)) ((s, st), j)
  have hc1 := Q.cost_comp_le
    (QuantitativeStepClass.HasProd.pairRight Q QP (d := idxRep)
      (QuantitativeStepClass.HasProd.pairRight Q QP (d := stateRep) R.headCode)) hL.onPull
    ((s, st), j)
  have hg1 := CC.composeOverhead_le
    (QuantitativeStepClass.HasProd.pairRight Q QP (d := idxRep)
      (QuantitativeStepClass.HasProd.pairRight Q QP (d := stateRep) R.headCode)) hL.onPull
    ((s, st), j)
  have hPP := QuantitativeStepClass.cost_pairRight_le Q (d := idxRep)
    (QuantitativeStepClass.HasProd.pairRight Q QP (d := stateRep) R.headCode) (s, st) j
  have hP := QuantitativeStepClass.cost_pairRight_le Q (d := stateRep) R.headCode s st
  have hc2 := Q.cost_comp_le (QP.fst (P.prod R.state stateRep) idxRep) (QP.fst R.state stateRep)
    ((s, st), j)
  have hg2 := CC.composeOverhead_le (QP.fst (P.prod R.state stateRep) idxRep)
    (QP.fst R.state stateRep) ((s, st), j)
  have hf1 := PC.cost_fst_le (P.prod R.state stateRep) idxRep ((s, st), j)
  have hf2 := PC.cost_fst_le R.state stateRep (s, st)
  dsimp only at hc1 hg1 hc2 hg2
  have hz := PC.size_prod_le (P.prod R.state stateRep) idxRep (s, st) j
  have hsst := PC.size_prod_le R.state stateRep s st
  have hhst := PC.size_prod_le bd.head stateRep (R.machine.head s) st
  have hhstj := PC.size_prod_le (P.prod bd.head stateRep) idxRep (R.machine.head s, st) j
  have o1 := QuantitativeStepClass.prod_overhead_le Q
    (show Q.size (P.prod (P.prod R.state stateRep) idxRep) ((s, st), j) ≤ N by omega)
  have o2 := QuantitativeStepClass.prod_overhead_le Q
    (show Q.size (P.prod R.state stateRep) (s, st) ≤ N by omega)
  have o3 := QuantitativeStepClass.composition_overhead_le Q
    (show Q.size (P.prod R.state stateRep) (s, st) ≤ N by omega)
  have o4 := QuantitativeStepClass.composition_overhead_le Q (show Q.size R.state s ≤ N by omega)
  have o5 := QuantitativeStepClass.composition_overhead_le Q
    (show Q.size (P.prod (P.prod bd.head stateRep) idxRep) ((R.machine.head s, st), j) ≤ N by
      omega)
  omega

/-- The stepping half costs `R`'s transition and twenty-seven structural primitives. -/
theorem cost_wrapStateStep_le (R : QuantitativeRealization Q bd) (stateRep : C.Str σ)
    (i : p.Idx) (st' : σ) (s : R.machine.State) {s' : R.machine.State}
    (h : R.machine.update? (s, i) = some s') :
    Q.cost (R.wrapStateStep stateRep) ((i, st'), s) ≤ Q.cost R.updateCode (s, i) +
      27 * QuantitativeStepClass.structOverhead Q (Q.size R.state s + Q.size R.state s' +
        Q.size stateRep st' + Q.size bd.idx i + 2 * PC.sizeOverhead + OC.sizeOverhead) := by
  set N := Q.size R.state s + Q.size R.state s' + Q.size stateRep st' + Q.size bd.idx i +
    2 * PC.sizeOverhead + OC.sizeOverhead with hN
  unfold wrapStateStep
  rw [QuantitativeStepClass.Realizer.cost_castFunction]
  have hc := Q.cost_comp_le (QuantitativeStepClass.rotate Q bd.idx stateRep R.state)
    (QuantitativeStepClass.carryUpdate Q stateRep R.updateCode) ((i, st'), s)
  have hg := CC.composeOverhead_le (QuantitativeStepClass.rotate Q bd.idx stateRep R.state)
    (QuantitativeStepClass.carryUpdate Q stateRep R.updateCode) ((i, st'), s)
  dsimp only at hc hg
  have hrot := QuantitativeStepClass.cost_rotate_le Q bd.idx stateRep R.state i st' s
  have hcu : Q.cost (QuantitativeStepClass.carryUpdate Q stateRep R.updateCode) ((s, st'), i) ≤
      Q.cost R.updateCode (s, i) + 17 * QuantitativeStepClass.structOverhead Q N :=
    QuantitativeStepClass.cost_carryUpdate_le Q stateRep R.updateCode s st' i h
  have hw := PC.size_prod_le (P.prod bd.idx stateRep) R.state (i, st') s
  have hist := PC.size_prod_le bd.idx stateRep i st'
  have hsti := PC.size_prod_le (P.prod R.state stateRep) bd.idx (s, st') i
  have hsst := PC.size_prod_le R.state stateRep s st'
  have o1 := QuantitativeStepClass.prod_overhead_le Q
    (show Q.size (P.prod (P.prod bd.idx stateRep) R.state) ((i, st'), s) ≤ N by omega)
  have o2 := QuantitativeStepClass.prod_overhead_le Q
    (show Q.size (P.prod bd.idx stateRep) (i, st') ≤ N by omega)
  have o3 := QuantitativeStepClass.composition_overhead_le Q
    (show Q.size (P.prod bd.idx stateRep) (i, st') ≤ N by omega)
  have o4 := QuantitativeStepClass.composition_overhead_le Q
    (show Q.size (P.prod (P.prod R.state stateRep) bd.idx) ((s, st'), i) ≤ N by omega)
  omega

/-- A product transition costs `R`'s transition, a recomputed `R` readout, `onPull`, and at most
forty-two structural primitives. -/
theorem cost_updateCode_wrapState_le (R : QuantitativeRealization Q bd)
    (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) (s : R.machine.State)
    (st : σ) (j : r.Idx) {i : p.Idx} {st' : σ} {s' : R.machine.State}
    (hpull : L.pullHead B ((R.machine.head s, st), j) = some (i, st'))
    (hupdate : R.machine.update? (s, i) = some s') :
    Q.cost (R.wrapState stateRep posRep idxRep hL).updateCode ((s, st), j) ≤
      Q.cost R.updateCode (s, i) + Q.cost R.headCode s +
        Q.cost hL.onPull ((R.machine.head s, st), j) +
        42 * QuantitativeStepClass.structOverhead Q (Q.size R.state s + Q.size R.state s' +
          Q.size stateRep st + Q.size stateRep st' + Q.size bd.head (R.machine.head s) +
          Q.size bd.idx i + Q.size idxRep j + 2 * PC.sizeOverhead + OC.sizeOverhead) := by
  set N := Q.size R.state s + Q.size R.state s' + Q.size stateRep st + Q.size stateRep st' +
    Q.size bd.head (R.machine.head s) + Q.size bd.idx i + Q.size idxRep j +
    2 * PC.sizeOverhead + OC.sizeOverhead with hN
  change Q.cost ((Q.compose (R.wrapStatePull hL)
    (QO.bindContext (R.wrapStateStep stateRep))).castFunction _) ((s, st), j) ≤ _
  rw [QuantitativeStepClass.Realizer.cost_castFunction]
  have hcomp := Q.cost_comp_le (R.wrapStatePull hL) (QO.bindContext (R.wrapStateStep stateRep))
    ((s, st), j)
  have hglue := CC.composeOverhead_le (R.wrapStatePull hL)
    (QO.bindContext (R.wrapStateStep stateRep)) ((s, st), j)
  dsimp only at hcomp hglue
  rw [hpull] at hcomp hglue
  have hpullCost := cost_wrapStatePull_le R hL s st j
  have hbind := OC.cost_bindContext_le (R.wrapStateStep stateRep) (some (i, st'), s)
  simp only [Option.elim_some] at hbind
  have hstep := cost_wrapStateStep_le R stateRep i st' s hupdate
  have hm1 := QuantitativeStepClass.monotone_structOverhead Q
    (show Q.size R.state s + Q.size stateRep st + Q.size bd.head (R.machine.head s) +
      Q.size idxRep j + 2 * PC.sizeOverhead ≤ N by omega)
  have hm2 := QuantitativeStepClass.monotone_structOverhead Q
    (show Q.size R.state s + Q.size R.state s' + Q.size stateRep st' + Q.size bd.idx i +
      2 * PC.sizeOverhead + OC.sizeOverhead ≤ N by omega)
  have hpo := PC.size_prod_le (O.option (P.prod bd.idx stateRep)) R.state (some (i, st')) s
  have hso := OC.size_some_le (P.prod bd.idx stateRep) (i, st')
  have hist := PC.size_prod_le bd.idx stateRep i st'
  have o1 := QuantitativeStepClass.option_overhead_le Q
    (show Q.size (P.prod (O.option (P.prod bd.idx stateRep)) R.state) (some (i, st'), s) ≤ N by
      omega)
  have o2 := QuantitativeStepClass.composition_overhead_le Q
    (show Q.size (P.prod (O.option (P.prod bd.idx stateRep)) R.state) (some (i, st'), s) ≤ N by
      omega)
  omega

end Laws

/-! ### Conformance transport without a cost certificate -/

/-- Every conforming product trace has a conforming source trace of `R` of the same length. -/
theorem exists_source_conforms {R : QuantitativeRealization Q bd}
    {stateRep : C.Str σ} {posRep : C.Str r.A} {idxRep : C.Str r.Idx} {L : StateLens p r σ}
    {hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep}
    {allowsP : ∀ position, p.B position → Prop} {allowsR : ∀ position, r.B position → Prop}
    (contract : ∀ position state answer, allowsR (L.pos (position, state)) answer →
      allowsP position (L.answer (position, state) answer))
    {start finish : (R.wrapState stateRep posRep idxRep hL).machine.State}
    (trace : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace start finish)
    (htrace : trace.Conforms allowsR) :
    ∃ source : R.ExecutionTrace start.1 finish.1, source.Conforms allowsP ∧
      source.length = trace.length := by
  induction trace with
  | nil state => exact ⟨.nil state.1, trivial, rfl⟩
  | @query state position next finish view_eq direction tail ih =>
      obtain ⟨source, sourceNext, hR, hsig⟩ :=
        R.machine.exists_view_eq_query_of_wrapState L view_eq
      cases hsig
      obtain ⟨tailSource, hconf, hlength⟩ := ih htrace.2
      exact ⟨.query hR (L.answer (source, state.2) direction) tailSource,
        ⟨contract _ _ _ htrace.1, hconf⟩, by
          simp only [QuantitativeRealization.ExecutionTrace.length, hlength]⟩

/-! ### Discharging the certificate from cost laws and handler invariants -/

section Laws

variable [CC : Q.HasCompositionCost] [PC : Q.HasProdCost] [SC : Q.HasSumCost]
  [OC : Q.HasOptionCost] [DC : Q.IsDistributiveCost]

/-- The carry charged by the cost laws for a one-query stateful handler, from the adversary's
bound, the input size, a handler-state size bound, per-call handler work for `onPos` and
`onPull`, and a per-step inner-traffic bound. -/
def handlerLawCarry (bound : ExecutionCost)
    (inputSize stateSize posWork pullWork innerTraffic : ℕ) : Carry where
  init := 4 * QuantitativeStepClass.structOverhead Q (inputSize + stateSize + PC.sizeOverhead)
  head := posWork + 10 * QuantitativeStepClass.structOverhead Q (bound.peakStateSize +
    2 * bound.peakHeadSize + 2 * stateSize + innerTraffic + 2 * PC.sizeOverhead +
      2 * SC.sizeOverhead)
  update := pullWork + 42 * QuantitativeStepClass.structOverhead Q (2 * bound.peakStateSize +
    2 * stateSize + bound.peakHeadSize + bound.traffic + innerTraffic + 2 * PC.sizeOverhead +
      OC.sizeOverhead)
  state := stateSize + PC.sizeOverhead
  headSize := stateSize + innerTraffic + PC.sizeOverhead + SC.sizeOverhead

/-- Under the cost laws, a run bound for the adversary together with handler invariants along
conforming product runs — a handler-state size bound, per-call work bounds for the lens code and
a per-step inner-traffic bound — discharges the handler certificate with `handlerLawCarry`. -/
def WrapStateCostCertificate.ofLaws {R : QuantitativeRealization Q bd}
    {hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep}
    {allowsP : ∀ position, p.B position → Prop} {allowsR : ∀ position, r.B position → Prop}
    {bound : A → ExecutionCost} (h : R.RunsWithinUnder allowsP bound)
    (contract : ∀ position state answer, allowsR (L.pos (position, state)) answer →
      allowsP position (L.answer (position, state) answer))
    (progress : ∀ position state, (∃ direction, allowsP position direction) →
      ∃ answer, allowsR (L.pos (position, state)) answer)
    (stateSize posWork pullWork innerTraffic : A × σ → ℕ)
    (state_le : ∀ input {state : R.machine.State × σ}
      (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
        ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
      pre.Conforms allowsR → Q.size stateRep state.2 ≤ stateSize input)
    (pos_le : ∀ input {state : R.machine.State × σ}
      (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
        ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
      pre.Conforms allowsR → ∀ {position : p.A} {next : p.B position → R.machine.State},
        R.machine.view state.1 = Sum.inr ⟨position, next⟩ →
          Q.cost hL.onPos (position, state.2) ≤ posWork input)
    (pull_le : ∀ input {state : R.machine.State × σ}
      (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
        ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
      pre.Conforms allowsR → ∀ {position : p.A} {next : p.B position → R.machine.State},
        R.machine.view state.1 = Sum.inr ⟨position, next⟩ →
          ∀ answer, allowsR (L.pos (position, state.2)) answer →
            Q.cost hL.onPull ((R.machine.head state.1, state.2),
              ⟨L.pos (position, state.2), answer⟩) ≤ pullWork input)
    (traffic_le : ∀ input {state : R.machine.State × σ}
      (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
        ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
      pre.Conforms allowsR → ∀ {position : p.A} {next : p.B position → R.machine.State},
        R.machine.view state.1 = Sum.inr ⟨position, next⟩ →
          ∀ answer, allowsR (L.pos (position, state.2)) answer →
            Q.size posRep (L.pos (position, state.2)) +
              Q.size idxRep ⟨L.pos (position, state.2), answer⟩ ≤ innerTraffic input) :
    WrapStateCostCertificate R hL allowsR where
  carry input := handlerLawCarry (Q := Q) (bound input.1) (Q.size bd.input input.1)
    (stateSize input) (posWork input) (pullWork input) (innerTraffic input)
  traffic := innerTraffic
  init_le := by
    intro input
    obtain ⟨a, st⟩ := input
    have hcost := cost_initCode_wrapState_le R hL a st
    have hst := state_le (a, st) (.nil _) trivial
    have hsize := PC.size_prod_le bd.input stateRep a st
    change Q.size stateRep st ≤ stateSize (a, st) at hst
    have o1 := QuantitativeStepClass.prod_overhead_le Q
      (show Q.size (P.prod bd.input stateRep) (a, st) ≤
        Q.size bd.input a + stateSize (a, st) + PC.sizeOverhead by omega)
    have o2 := QuantitativeStepClass.composition_overhead_le Q
      (show Q.size bd.input a ≤ Q.size bd.input a + stateSize (a, st) + PC.sizeOverhead by omega)
    simp only [handlerLawCarry]
    omega
  head_le := by
    intro input state pre hpre
    obtain ⟨source, hsource, -⟩ := exists_source_conforms contract pre hpre
    obtain ⟨s, st⟩ := state
    have hs := h.size_state_le input.1 source hsource
    have hh := h.size_head_le input.1 source hsource
    have hst := state_le input pre hpre
    have hcost := cost_headCode_wrapState_le R hL s st
    have hsize := size_head_wrapState_le (Q := Q) (bd := bd) (stateRep := stateRep)
      (posRep := posRep) (L := L) R.machine s st
    dsimp only at hs hh hst
    -- The forwarded query (if any) is within the traffic bound, by progress.
    have hpos : (R.machine.head s).elim (fun _ ↦ 0)
        (fun position ↦ Q.cost hL.onPos (position, st)) ≤ posWork input ∧
        (R.machine.head s).elim (fun _ ↦ 0)
          (fun position ↦ Q.size posRep (L.pos (position, st))) ≤ innerTraffic input := by
      rcases hview : R.machine.view s with value | ⟨position, next⟩
      · rw [R.machine.head_eq_inl_of_view hview]
        exact ⟨Nat.zero_le _, Nat.zero_le _⟩
      · rw [R.machine.head_eq_inr_of_view hview]
        obtain ⟨answer, hanswer⟩ := progress position st
          (h.traceProgress input.1 source hsource hview)
        have := traffic_le input pre hpre hview answer hanswer
        have hposWork := pos_le input pre hpre hview
        dsimp only at this hposWork
        exact ⟨hposWork, by simp only [Sum.elim_inr]; omega⟩
    obtain ⟨hpos₁, hpos₂⟩ := hpos
    change Q.size (bd.withHandler stateRep posRep idxRep).head
      ((R.wrapState stateRep posRep idxRep hL).machine.head (s, st)) ≤ _ at hsize
    have hm := QuantitativeStepClass.monotone_structOverhead Q
      (show Q.size R.state s + Q.size bd.head (R.machine.head s) + Q.size stateRep st +
          Q.size (bd.withHandler stateRep posRep idxRep).head
            ((R.wrapState stateRep posRep idxRep hL).machine.head (s, st)) +
          PC.sizeOverhead + SC.sizeOverhead ≤
        (bound input.1).peakStateSize + 2 * (bound input.1).peakHeadSize +
          2 * stateSize input + innerTraffic input + 2 * PC.sizeOverhead +
            2 * SC.sizeOverhead by omega)
    simp only [handlerLawCarry]
    omega
  update_le := by
    intro input state pre hpre position next hview answer hanswer
    obtain ⟨source, hsource, -⟩ := exists_source_conforms contract pre hpre
    obtain ⟨s, st⟩ := state
    have hs := h.size_state_le input.1 source hsource
    have hh := h.size_head_le input.1 source hsource
    have hst := state_le input pre hpre
    have hallowedP := contract position st answer hanswer
    obtain ⟨hs', hi⟩ := h.size_step_le input.1 source hsource hview _ hallowedP
    -- The next handler state is reachable along the extended product prefix.
    have hview' := view_wrapState_of_query R.machine L (state := (s, st)) hview
    let pre' := pre.append (.query (R := R.wrapState stateRep posRep idxRep hL) hview' answer
      (.nil _))
    have hpre' : pre'.Conforms allowsR :=
      (QuantitativeRealization.ExecutionTrace.conforms_append pre _).mpr ⟨hpre, hanswer, trivial⟩
    have hst' : Q.size stateRep (L.update (position, st) answer) ≤ stateSize input :=
      state_le input pre' hpre'
    have hpull : L.pullHead B ((R.machine.head s, st), ⟨L.pos (position, st), answer⟩) =
        some (⟨position, L.answer (position, st) answer⟩, L.update (position, st) answer) := by
      rw [R.machine.head_eq_inr_of_view hview]
      change dite _ _ _ = _
      rw [dite_eq_left rfl]
    have hcost := cost_updateCode_wrapState_le R hL s st ⟨L.pos (position, st), answer⟩ hpull
      (R.machine.update?_of_view_query hview _)
    have hpullWork := pull_le input pre hpre hview answer hanswer
    have htraffic := traffic_le input pre hpre hview answer hanswer
    dsimp only at hs hh hst hpullWork htraffic
    have hm := QuantitativeStepClass.monotone_structOverhead Q
      (show Q.size R.state s + Q.size R.state (next (L.answer (position, st) answer)) +
          Q.size stateRep st + Q.size stateRep (L.update (position, st) answer) +
          Q.size bd.head (R.machine.head s) +
          Q.size bd.idx ⟨position, L.answer (position, st) answer⟩ +
          Q.size idxRep ⟨L.pos (position, st), answer⟩ + 2 * PC.sizeOverhead +
            OC.sizeOverhead ≤
        2 * (bound input.1).peakStateSize + 2 * stateSize input + (bound input.1).peakHeadSize +
          (bound input.1).traffic + innerTraffic input + 2 * PC.sizeOverhead +
            OC.sizeOverhead by omega)
    simp only [handlerLawCarry]
    omega
  traffic_le := by
    intro input state pre hpre position next hview answer hanswer
    exact traffic_le input pre hpre hview answer hanswer
  state_le := by
    intro input state pre hpre
    have hst := state_le input pre hpre
    obtain ⟨s, st⟩ := state
    have hsize := PC.size_prod_le R.state stateRep s st
    dsimp only at hst
    simp only [handlerLawCarry]
    change Q.size (P.prod R.state stateRep) (s, st) ≤ _
    omega
  headSize_le := by
    intro input state pre hpre
    obtain ⟨source, hsource, -⟩ := exists_source_conforms contract pre hpre
    have hst := state_le input pre hpre
    obtain ⟨s, st⟩ := state
    have hsize := size_head_wrapState_le (Q := Q) (bd := bd) (stateRep := stateRep)
      (posRep := posRep) (L := L) R.machine s st
    dsimp only at hst
    have hpos : (R.machine.head s).elim (fun _ ↦ 0)
        (fun position ↦ Q.size posRep (L.pos (position, st))) ≤ innerTraffic input := by
      rcases hview : R.machine.view s with value | ⟨position, next⟩
      · rw [R.machine.head_eq_inl_of_view hview]
        exact Nat.zero_le _
      · rw [R.machine.head_eq_inr_of_view hview]
        obtain ⟨answer, hanswer⟩ := progress position st
          (h.traceProgress input.1 source hsource hview)
        have := traffic_le input pre hpre hview answer hanswer
        dsimp only at this
        simp only [Sum.elim_inr]
        omega
    simp only [handlerLawCarry]
    change Q.size (S.sum (P.prod bd.out stateRep) posRep)
      ((R.machine.wrapState L).head (s, st)) ≤ _
    omega

/-- **One-query stateful handler substitution under cost laws.** The product machine of an
adversary realization and an executable stateful lens runs within twice the adversary's work
plus, per step, the handler's own work (`onPos`, `onPull`) and a constant number of structural
primitives at sizes bounded by the adversary's peaks and traffic, the handler-state bound and the
inner traffic; queries equal the adversary's, inner traffic is per-step bounded, and peak sizes
shift by the handler state. -/
theorem RunsWithinUnder.wrapState_of_laws {R : QuantitativeRealization Q bd}
    {hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep}
    {allowsP : ∀ position, p.B position → Prop} {allowsR : ∀ position, r.B position → Prop}
    {bound : A → ExecutionCost} (h : R.RunsWithinUnder allowsP bound)
    (contract : ∀ position state answer, allowsR (L.pos (position, state)) answer →
      allowsP position (L.answer (position, state) answer))
    (progress : ∀ position state, (∃ direction, allowsP position direction) →
      ∃ answer, allowsR (L.pos (position, state)) answer)
    (stateSize posWork pullWork innerTraffic : A × σ → ℕ)
    (state_le : ∀ input {state : R.machine.State × σ}
      (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
        ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
      pre.Conforms allowsR → Q.size stateRep state.2 ≤ stateSize input)
    (pos_le : ∀ input {state : R.machine.State × σ}
      (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
        ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
      pre.Conforms allowsR → ∀ {position : p.A} {next : p.B position → R.machine.State},
        R.machine.view state.1 = Sum.inr ⟨position, next⟩ →
          Q.cost hL.onPos (position, state.2) ≤ posWork input)
    (pull_le : ∀ input {state : R.machine.State × σ}
      (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
        ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
      pre.Conforms allowsR → ∀ {position : p.A} {next : p.B position → R.machine.State},
        R.machine.view state.1 = Sum.inr ⟨position, next⟩ →
          ∀ answer, allowsR (L.pos (position, state.2)) answer →
            Q.cost hL.onPull ((R.machine.head state.1, state.2),
              ⟨L.pos (position, state.2), answer⟩) ≤ pullWork input)
    (traffic_le : ∀ input {state : R.machine.State × σ}
      (pre : (R.wrapState stateRep posRep idxRep hL).ExecutionTrace
        ((R.wrapState stateRep posRep idxRep hL).machine.init input) state),
      pre.Conforms allowsR → ∀ {position : p.A} {next : p.B position → R.machine.State},
        R.machine.view state.1 = Sum.inr ⟨position, next⟩ →
          ∀ answer, allowsR (L.pos (position, state.2)) answer →
            Q.size posRep (L.pos (position, state.2)) +
              Q.size idxRep ⟨L.pos (position, state.2), answer⟩ ≤ innerTraffic input) :
    (R.wrapState stateRep posRep idxRep hL).RunsWithinUnder allowsR fun input ↦
      (bound input.1).handled (bound input.1).queries
        (handlerLawCarry (Q := Q) (bound input.1) (Q.size bd.input input.1) (stateSize input)
          (posWork input) (pullWork input) (innerTraffic input))
        (innerTraffic input) :=
  h.wrapState (WrapStateCostCertificate.ofLaws h contract progress stateSize posWork pullWork
    innerTraffic state_le pos_le pull_le traffic_le) contract progress

end Laws

end WrapState

end QuantitativeRealization

end DynSystem.DynComputation

end PFunctor
