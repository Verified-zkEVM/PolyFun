/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.CostLaws
public import PolyFun.Realizability.Quantitative.Carry
public import PolyFun.Realizability.Quantitative.BoundedClosure
public import PolyFun.Realizability.Quantitative.TraceCost

/-!
# Machine-level strength and the strong bind

`QuantitativeRealization.withInput R` realizes `fun a ↦ (·, a) <$> program a` from a realization
`R` of `program`. Its machine is `DynComputation.withInput`:
- the hidden state is `R.State × A`, represented by the pinned product;
- the readout and transition are `R`'s, with the carried input attached;
- the returned value is paired with the input.

The three step maps are assembled from `R`'s code and the structural mixins:
- `initCode` is `HasProd.withInput R.initCode`, that is `pair R.initCode identity`;
- `headCode` is `carryReadout R.headCode`;
- `updateCode` is `carryUpdate R.updateCode`: the exchange `((s, a), i) ↦ ((s, i), a)`, then
  `pairRight R.updateCode`, then the option strength `HasOption.strength`.

The transition never consults `R`'s readout, so no component code is evaluated twice.

`QuantitativeRealization.seqCompWithInput R₁ R₂` runs `R₁.withInput` and hands the intermediate
value *and* the original input to `R₂`. It realizes the strong bind
`fun a ↦ program a >>= fun b ↦ next (b, a)`, whose second phase reads the original input; `seqComp`
alone gives its second phase only `b`.

## Main results

* `withInput_implements` and `seqCompWithInput_implements`: semantics.
* `ExecutionTrace.ofWithInput`: every input-retaining trace is a trace of `R` with the same
  queries, answers and length. The carried input never changes (`snd_finish_eq`).
* `WithInputCostCertificate`: per-step carry allowances, quantified only over states and answers
  reachable along conforming traces of `R`.
* `executionCost_withInput_le` and `RunsWithinUnder.withInput`: the input-retaining run costs
  `R`'s resources plus `init + (q + 1)·head + q·update` of carry for `q` queries. Queries and
  traffic are unchanged and the peak sizes shift by the size carries.
* `WithInputCostCertificate.ofLaws` and `RunsWithinUnder.withInput_of_laws`: under the cost laws
  of `PolyFun.Realizability.Quantitative.CostLaws` the certificate holds with `lawCarry`. That is
  at most `2` structural primitives at initialization, `11` per readout and `17` per transition,
  each charged the combined envelope at a size bounded by `R`'s peak sizes, traffic and the input.
* `RunsWithinUnder.seqCompWithInput` and its `_of_laws` form: the bounded strong bind, from the
  strength carry, the second-phase bound, a handoff envelope and `seqComp`'s structural-overhead
  certificate.
-/

@[expose] public section

universe u v w

namespace PFunctor.DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}} [P : C.HasProd]
  [S : C.HasSum] [O : C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {A B : Type u}
  {bd : Boundary C p A B}

omit [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A] in
/-- Retaining the input preserves relation-restricted resolution exactly. -/
theorem resolvesInUnder_withInput_iff (M : DynComputation.{u} p A B)
    (allows : ∀ position, p.B position → Prop) (k : ℕ) (state : M.State × A) :
    M.withInput.ResolvesInUnder allows k state ↔ M.ResolvesInUnder allows k state.1 := by
  induction k generalizing state with
  | zero =>
      rw [resolvesInUnder_zero, resolvesInUnder_zero]
      rcases hview : M.view state.1 with value | ⟨position, next⟩
      · exact iff_of_true ⟨_, view_withInput_of_return M hview⟩ ⟨_, rfl⟩
      · rw [view_withInput_of_query M hview]
        simp
  | succ k ih =>
      rcases hview : M.view state.1 with value | ⟨position, next⟩
      · exact iff_of_true
          (M.withInput.resolvesInUnder_return allows _ state _ (view_withInput_of_return M hview))
          (M.resolvesInUnder_return allows _ _ _ hview)
      · rw [M.withInput.resolvesInUnder_query_succ_iff allows k state position _
            (view_withInput_of_query M hview),
          M.resolvesInUnder_query_succ_iff allows k _ position next hview]
        exact forall_congr' fun direction ↦ imp_congr_right fun _ ↦ ih _

namespace QuantitativeRealization

section WithInput

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive]

/-- Machine-level strength: a quantitative realization of `fun a ↦ (·, a) <$> program a` whose
hidden state carries the input.

Like `HasProd.withInput`, it pairs a result with the retained input. `Boundary.withInput` is
unrelated: it replaces a boundary's input representation. -/
@[implicit_reducible]
def withInput (R : QuantitativeRealization Q bd) :
    QuantitativeRealization Q (bd.withOut (P.prod bd.out bd.input)) where
  machine := R.machine.withInput
  state := P.prod R.state bd.input
  initCode := QuantitativeStepClass.HasProd.withInput Q QP R.initCode
  headCode := (QuantitativeStepClass.carryReadout Q bd.input R.headCode).castFunction (by
    funext state
    rw [head_withInput])
  updateCode := (QuantitativeStepClass.carryUpdate Q bd.input R.updateCode).castFunction (by
    funext x
    obtain ⟨state, index⟩ := x
    rw [update?_withInput])

/-- The input-retaining machine implements the program that pairs each result with the input. -/
theorem withInput_implements (R : QuantitativeRealization Q bd) {program : A → FreeM p B}
    (h : R.machine.Implements program) :
    R.withInput.machine.Implements
      fun input ↦ FreeM.map (fun value ↦ (value, input)) (program input) :=
  Implements.withInput h

/-! ### Trace transport -/

namespace ExecutionTrace

/-- Forget the carried input of an input-retaining trace: the same queries and answers, read on
`R`. -/
def ofWithInput (R : QuantitativeRealization Q bd) {start finish : R.withInput.machine.State}
    (trace : R.withInput.ExecutionTrace start finish) : R.ExecutionTrace start.1 finish.1 :=
  match trace with
  | .nil state => .nil (R := R) state.1
  | .query view_eq direction tail =>
      .query (R := R) (R.machine.view_eq_query_of_withInput_view_eq_query view_eq).1 direction
        (ofWithInput R tail)

/-- The carried input never changes along an input-retaining trace. -/
theorem snd_finish_eq (R : QuantitativeRealization Q bd)
    {start finish : R.withInput.machine.State} (trace : R.withInput.ExecutionTrace start finish) :
    finish.2 = start.2 := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih =>
      exact ih.trans ((R.machine.view_eq_query_of_withInput_view_eq_query view_eq).2 direction)

@[simp] theorem length_ofWithInput (R : QuantitativeRealization Q bd)
    {start finish : R.withInput.machine.State} (trace : R.withInput.ExecutionTrace start finish) :
    (ofWithInput R trace).length = trace.length := by
  induction trace with
  | nil => rfl
  | query view_eq direction tail ih =>
      simp only [ofWithInput, QuantitativeRealization.ExecutionTrace.length, ih]

@[simp] theorem conforms_ofWithInput (R : QuantitativeRealization Q bd)
    (allows : ∀ position, p.B position → Prop)
    {start finish : R.withInput.machine.State} (trace : R.withInput.ExecutionTrace start finish) :
    (ofWithInput R trace).Conforms allows ↔ trace.Conforms allows := by
  induction trace with
  | nil => exact Iff.rfl
  | query view_eq direction tail ih =>
      simp only [ofWithInput, QuantitativeRealization.ExecutionTrace.Conforms, ih]

end ExecutionTrace

/-! ### Cost certificates and the transfer theorem -/

/-- Per-step carry allowances for retaining the input of `R`.

Every field compares the input-retaining code with `R`'s code at the same step. The work and size
allowances are only required at states (and allowed answers) reachable along conforming traces
of `R` from the same input, so a backend whose structural overhead grows with state sizes can
discharge them from `R`'s own peak-size and traffic bounds (`ofLaws`). -/
structure WithInputCostCertificate (R : QuantitativeRealization Q bd)
    (allows : ∀ position, p.B position → Prop) where
  /-- Input-indexed carry allowances. -/
  carry : A → Carry
  /-- Initialization costs `R`'s plus the initialization carry. -/
  init_le : ∀ input,
    Q.cost R.withInput.initCode input ≤ Q.cost R.initCode input + (carry input).init
  /-- A reachable readout costs `R`'s plus the readout carry. -/
  head_le : ∀ input {state : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init input) state), trace.Conforms allows →
      Q.cost R.withInput.headCode (state, input) ≤
        Q.cost R.headCode state + (carry input).head
  /-- A reachable, allowed transition costs `R`'s plus the transition carry. -/
  update_le : ∀ input {state : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init input) state), trace.Conforms allows →
      ∀ {position : p.A} {next : p.B position → R.machine.State},
        R.machine.view state = Sum.inr ⟨position, next⟩ → ∀ direction, allows position direction →
          Q.cost R.withInput.updateCode ((state, input), ⟨position, direction⟩) ≤
            Q.cost R.updateCode (state, ⟨position, direction⟩) + (carry input).update
  /-- A reachable state is encoded within `R`'s plus the state carry. -/
  state_le : ∀ input {state : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init input) state), trace.Conforms allows →
      Q.size R.withInput.state (state, input) ≤ Q.size R.state state + (carry input).state
  /-- A reachable readout is encoded within `R`'s plus the readout-size carry. -/
  headSize_le : ∀ input {state : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init input) state), trace.Conforms allows →
      Q.size (bd.withOut (P.prod bd.out bd.input)).head (R.withInput.machine.head (state, input)) ≤
        Q.size bd.head (R.machine.head state) + (carry input).headSize

namespace ExecutionTrace

/-- Pathwise transfer for the transition part of an input-retaining trace that starts at a
conformingly reachable state. -/
theorem cost_le_traceCarry {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} (cert : WithInputCostCertificate R allows)
    (input : A) {start finish : R.withInput.machine.State}
    (trace : R.withInput.ExecutionTrace start finish) (hstart : start.2 = input)
    (pre : R.ExecutionTrace (R.machine.init input) start.1) (hpre : pre.Conforms allows)
    (htrace : trace.Conforms allows) :
    trace.cost ≤ (ofWithInput R trace).cost.traceCarry trace.length (cert.carry input) := by
  induction trace with
  | nil state =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [ofWithInput, QuantitativeRealization.ExecutionTrace.cost,
          QuantitativeRealization.ExecutionTrace.length, ExecutionCost.traceCarry]
  | @query state position next finish view_eq direction tail ih =>
      obtain ⟨hR, hsnd⟩ := R.machine.view_eq_query_of_withInput_view_eq_query view_eq
      obtain ⟨s, a⟩ := state
      change a = input at hstart
      subst hstart
      change R.ExecutionTrace (R.machine.init a) s at pre
      have hallowed : allows position direction := htrace.1
      -- Extend the reachable prefix by the current step.
      let pre' : R.ExecutionTrace (R.machine.init a) (next direction).1 :=
        pre.append (.query hR direction (.nil _))
      have hpre' : pre'.Conforms allows :=
        (QuantitativeRealization.ExecutionTrace.conforms_append pre _).mpr
          ⟨hpre, hallowed, trivial⟩
      have htail := ih ((hsnd direction).trans rfl) pre' hpre' htrace.2
      have hhead := cert.head_le a pre hpre
      have hupdate := cert.update_le a pre hpre hR direction hallowed
      have hstate := cert.state_le a pre hpre
      have hheadSize := cert.headSize_le a pre hpre
      obtain ⟨hw, hq, ht, hs, hh⟩ := htail
      simp only [ExecutionCost.traceCarry] at hw hq ht hs hh
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [ofWithInput, QuantitativeRealization.ExecutionTrace.cost,
          QuantitativeRealization.ExecutionTrace.length, ExecutionCost.traceCarry,
          ExecutionCost.work_add, ExecutionCost.work_observe, ExecutionCost.queries_add,
          ExecutionCost.queries_observe, ExecutionCost.traffic_add,
          ExecutionCost.traffic_observe, ExecutionCost.peakStateSize_add,
          ExecutionCost.peakStateSize_observe, ExecutionCost.peakHeadSize_add,
          ExecutionCost.peakHeadSize_observe, ExecutionCost.ofWork, ExecutionCost.query,
          Boundary.withOut_pos, Boundary.withOut_idx, Nat.add_mul, Nat.mul_add,
          Nat.one_mul] at * <;>
        omega

end ExecutionTrace

/-- Pathwise transfer: a conforming input-retaining run costs at most the corresponding run of `R`
with the carry charged once at initialization, at every readout and at every transition. Queries
and traffic are unchanged. -/
theorem executionCost_withInput_le {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} (cert : WithInputCostCertificate R allows)
    (input : A) {finish : R.withInput.machine.State}
    (trace : R.withInput.ExecutionTrace (R.withInput.machine.init input) finish)
    (htrace : trace.Conforms allows) :
    R.withInput.executionCost input trace ≤
      (R.executionCost input (ExecutionTrace.ofWithInput R trace)).withCarry trace.length
        (cert.carry input) := by
  have hR : (ExecutionTrace.ofWithInput R trace).Conforms allows :=
    (ExecutionTrace.conforms_ofWithInput R allows trace).mpr htrace
  have htr := ExecutionTrace.cost_le_traceCarry cert input trace rfl (.nil _) trivial htrace
  have hfinish : finish.2 = input := ExecutionTrace.snd_finish_eq R trace
  obtain ⟨s, a⟩ := finish
  change a = input at hfinish
  subst hfinish
  have hinit := cert.init_le a
  have hhead := cert.head_le a (ExecutionTrace.ofWithInput R trace) hR
  have hstate := cert.state_le a (ExecutionTrace.ofWithInput R trace) hR
  have hheadSize := cert.headSize_le a (ExecutionTrace.ofWithInput R trace) hR
  obtain ⟨hw, hq, ht, hs, hh⟩ := htr
  simp only [ExecutionCost.traceCarry] at hw hq ht hs hh
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [QuantitativeRealization.executionCost, ExecutionCost.withCarry,
      ExecutionCost.work_add, ExecutionCost.work_observe,
      ExecutionCost.queries_add, ExecutionCost.queries_observe,
      ExecutionCost.traffic_add, ExecutionCost.traffic_observe,
      ExecutionCost.peakStateSize_add, ExecutionCost.peakStateSize_observe,
      ExecutionCost.peakHeadSize_add, ExecutionCost.peakHeadSize_observe,
      ExecutionCost.ofWork, Nat.add_mul, Nat.mul_add, Nat.one_mul] at * <;>
    omega

/-- `RunsWithinUnder` transfer for machine-level strength: the input-retaining realization runs
within `R`'s bound with the certificate's carry charged per step. Queries and traffic are
unchanged, and resolution and progress transfer exactly. -/
theorem RunsWithinUnder.withInput {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : A → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) (cert : WithInputCostCertificate R allows) :
    R.withInput.RunsWithinUnder allows fun input ↦
      (bound input).withCarry (bound input).queries (cert.carry input) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input finish trace htrace
    have hR : (ExecutionTrace.ofWithInput R trace).Conforms allows :=
      (ExecutionTrace.conforms_ofWithInput R allows trace).mpr htrace
    refine (executionCost_withInput_le cert input trace htrace).trans
      (ExecutionCost.withCarry_mono _ (h.cost_le input _ hR) ?_)
    rw [← ExecutionTrace.length_ofWithInput R trace]
    exact h.traceLength_le input _ hR
  · intro input
    change R.machine.withInput.ResolvesInUnder allows (bound input).queries
      (R.machine.init input, input)
    exact (resolvesInUnder_withInput_iff R.machine allows _ (R.machine.init input, input)).mpr
      (h.resolvesIn input)
  · intro input state trace htrace position next hview
    exact h.traceProgress input (ExecutionTrace.ofWithInput R trace)
      ((ExecutionTrace.conforms_ofWithInput R allows trace).mpr htrace)
      (R.machine.view_eq_query_of_withInput_view_eq_query hview).1

/-! ### Discharging the certificate from cost laws -/

section Laws

variable [CC : Q.HasCompositionCost] [PC : Q.HasProdCost] [SC : Q.HasSumCost]
  [OC : Q.HasOptionCost] [DC : Q.IsDistributiveCost]

omit [SC : Q.HasSumCost] [OC : Q.HasOptionCost] [DC : Q.IsDistributiveCost] in
/-- Input-retaining initialization costs `R`'s plus identity and pairing at the input's size. -/
theorem cost_initCode_withInput_le (R : QuantitativeRealization Q bd) (input : A) :
    Q.cost R.withInput.initCode input ≤
      Q.cost R.initCode input + CC.overhead (Q.size bd.input input) +
        PC.overhead (Q.size bd.input input) :=
  QuantitativeStepClass.cost_withInput_le Q R.initCode input

/-- An input-retaining readout costs `R`'s plus at most eleven structural primitives. -/
theorem cost_headCode_withInput_le (R : QuantitativeRealization Q bd)
    (state : R.machine.State) (input : A) :
    Q.cost R.withInput.headCode (state, input) ≤ Q.cost R.headCode state +
      11 * QuantitativeStepClass.structOverhead Q (Q.size R.state state +
        Q.size bd.head (R.machine.head state) + Q.size bd.input input + PC.sizeOverhead +
          SC.sizeOverhead) := by
  change Q.cost ((QuantitativeStepClass.carryReadout Q bd.input R.headCode).castFunction _)
    (state, input) ≤ _
  rw [QuantitativeStepClass.Realizer.cost_castFunction]
  exact QuantitativeStepClass.cost_carryReadout_le Q bd.input R.headCode state input

/-- An input-retaining enabled transition costs `R`'s plus at most seventeen structural
primitives. -/
theorem cost_updateCode_withInput_le (R : QuantitativeRealization Q bd)
    (state : R.machine.State) (input : A) (index : p.Idx) {next : R.machine.State}
    (h : R.machine.update? (state, index) = some next) :
    Q.cost R.withInput.updateCode ((state, input), index) ≤ Q.cost R.updateCode (state, index) +
      17 * QuantitativeStepClass.structOverhead Q (Q.size R.state state + Q.size R.state next +
        Q.size bd.input input + Q.size bd.idx index + 2 * PC.sizeOverhead + OC.sizeOverhead) := by
  change Q.cost ((QuantitativeStepClass.carryUpdate Q bd.input R.updateCode).castFunction _)
    ((state, input), index) ≤ _
  rw [QuantitativeStepClass.Realizer.cost_castFunction]
  exact QuantitativeStepClass.cost_carryUpdate_le Q bd.input R.updateCode state input index h

omit [Q.HasCategory] [QS : Q.HasSum] [QO : Q.HasOption] [QD : Q.IsDistributive]
  [CC : Q.HasCompositionCost] [SC : Q.HasSumCost] [OC : Q.HasOptionCost]
  [DC : Q.IsDistributiveCost] in
/-- The input-retaining state is encoded within `R`'s state, the input and the pair overhead. -/
theorem size_state_withInput_le (R : QuantitativeRealization Q bd) (state : R.machine.State)
    (input : A) :
    Q.size (P.prod R.state bd.input) (state, input) ≤
      Q.size R.state state + Q.size bd.input input + PC.sizeOverhead :=
  PC.size_prod_le R.state bd.input state input

omit [Q.HasCategory] [QO : Q.HasOption] [QD : Q.IsDistributive]
  [CC : Q.HasCompositionCost] [OC : Q.HasOptionCost] [DC : Q.IsDistributiveCost] in
/-- The input-retaining readout is encoded within `R`'s readout, the input and the pair and tag
overheads. -/
theorem size_head_withInput_le (R : QuantitativeRealization Q bd) (state : R.machine.State)
    (input : A) :
    Q.size (S.sum (P.prod bd.out bd.input) bd.pos) (R.machine.withInput.head (state, input)) ≤
      Q.size bd.head (R.machine.head state) + Q.size bd.input input + PC.sizeOverhead +
        SC.sizeOverhead := by
  rw [head_withInput]
  change _ ≤ Q.size (S.sum bd.out bd.pos) (R.machine.head state) + _ + _ + _
  rcases R.machine.head state with value | position
  · have h1 := SC.size_inl_le (P.prod bd.out bd.input) bd.pos (value, input)
    have h2 := PC.size_prod_le bd.out bd.input value input
    have h3 := SC.le_size_inl bd.out bd.pos value
    simp only [Sum.map_inl]
    omega
  · have h1 := SC.size_inr_le (P.prod bd.out bd.input) bd.pos position
    have h3 := SC.le_size_inr bd.out bd.pos position
    simp only [Sum.map_inr, id]
    omega

/-- The carry charged by the cost laws, as a function of a source bound and the input size: `2`
primitives at initialization, `11` per readout and `17` per transition, each charged the combined
envelope at a size bounded by the source's peak sizes and traffic and the input. -/
def lawCarry (bound : ExecutionCost) (inputSize : ℕ) : Carry where
  init := CC.overhead inputSize + PC.overhead inputSize
  head := 11 * QuantitativeStepClass.structOverhead Q (bound.peakStateSize +
    bound.peakHeadSize + inputSize + PC.sizeOverhead + SC.sizeOverhead)
  update := 17 * QuantitativeStepClass.structOverhead Q (2 * bound.peakStateSize + inputSize +
    bound.traffic + 2 * PC.sizeOverhead + OC.sizeOverhead)
  state := inputSize + PC.sizeOverhead
  headSize := inputSize + PC.sizeOverhead + SC.sizeOverhead

/-- Under the cost laws, a run bound for `R` discharges the strength certificate with
`lawCarry`. -/
def WithInputCostCertificate.ofLaws {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : A → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) : WithInputCostCertificate R allows where
  carry input := lawCarry (Q := Q) (bound input) (Q.size bd.input input)
  init_le input := by
    have := cost_initCode_withInput_le R input
    simp only [lawCarry]
    omega
  head_le input state pre hpre := by
    refine (cost_headCode_withInput_le R state input).trans ?_
    have hs := h.size_state_le input pre hpre
    have hh := h.size_head_le input pre hpre
    have hm := QuantitativeStepClass.monotone_structOverhead Q
      (show Q.size R.state state + Q.size bd.head (R.machine.head state) + Q.size bd.input input +
          PC.sizeOverhead + SC.sizeOverhead ≤ (bound input).peakStateSize +
            (bound input).peakHeadSize + Q.size bd.input input + PC.sizeOverhead +
              SC.sizeOverhead by omega)
    simp only [lawCarry]
    omega
  update_le input state pre hpre position next hview direction hallowed := by
    refine (cost_updateCode_withInput_le R state input ⟨position, direction⟩
      (R.machine.update?_of_view_query hview direction)).trans ?_
    have hs := h.size_state_le input pre hpre
    obtain ⟨hs', hi⟩ := h.size_step_le input pre hpre hview direction hallowed
    have hm := QuantitativeStepClass.monotone_structOverhead Q
      (show Q.size R.state state + Q.size R.state (next direction) + Q.size bd.input input +
          Q.size bd.idx ⟨position, direction⟩ + 2 * PC.sizeOverhead + OC.sizeOverhead ≤
            2 * (bound input).peakStateSize + Q.size bd.input input + (bound input).traffic +
              2 * PC.sizeOverhead + OC.sizeOverhead by omega)
    simp only [lawCarry]
    omega
  state_le input state _ _ := by
    have := size_state_withInput_le R state input
    simp only [lawCarry]
    change Q.size (P.prod R.state bd.input) (state, input) ≤ _
    omega
  headSize_le input state _ _ := by
    have := size_head_withInput_le R state input
    simp only [lawCarry]
    change Q.size (S.sum (P.prod bd.out bd.input) bd.pos)
      (R.machine.withInput.head (state, input)) ≤ _
    omega

/-- **Strength under cost laws.** If `R` runs within `bound`, its machine-level strength runs
within `bound` plus `lawCarry` per step: queries and traffic unchanged, work increased by
`init + (q + 1)·head + q·update` for the query budget `q`, and peak sizes shifted by the input size
and constant encoding overheads. -/
theorem RunsWithinUnder.withInput_of_laws {R : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {bound : A → ExecutionCost}
    (h : R.RunsWithinUnder allows bound) :
    R.withInput.RunsWithinUnder allows fun input ↦ (bound input).withCarry (bound input).queries
      (lawCarry (Q := Q) (bound input) (Q.size bd.input input)) :=
  h.withInput (WithInputCostCertificate.ofLaws h)

end Laws

end WithInput

/-! ## The strong bind -/

section SeqCompWithInput

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] {D : Type u} {outRep : C.Str D}

/-- Strong sequential composition: the second phase reads the first phase's result together with
the original input. -/
@[implicit_reducible]
def seqCompWithInput (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.strongMid outRep)) :
    QuantitativeRealization Q (bd.withOut outRep) :=
  R₁.withInput.seqComp R₂

omit [DecidableEq p.A] in
private theorem resumption_bind_map {X Y Z : Type u} (f : X → Y) (x : Resumption p X)
    (k : Y → Resumption p Z) :
    Resumption.bind (Resumption.map f x) k = Resumption.bind x (fun value ↦ k (f value)) := by
  rw [Resumption.map, Resumption.bind_assoc]
  simp

/-- The strong bind denotes resumption bind with a continuation that reads the input. -/
theorem denote_seqCompWithInput (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.strongMid outRep)) (input : A) :
    (R₁.seqCompWithInput R₂).machine.denote input =
      Resumption.bind (R₁.machine.denote input)
        (fun value ↦ R₂.machine.denote (value, input)) := by
  change (R₁.machine.withInput.seqComp R₂.machine).denote input = _
  rw [denote_seqComp, denote_withInput, resumption_bind_map]

/-- The strong bind implements the Kleisli strong bind of the implemented programs. -/
theorem seqCompWithInput_implements (R₁ : QuantitativeRealization Q bd)
    (R₂ : QuantitativeRealization Q (bd.strongMid outRep))
    {program : A → FreeM p B} {next : B × A → FreeM p D}
    (h₁ : R₁.machine.Implements program) (h₂ : R₂.machine.Implements next) :
    (R₁.seqCompWithInput R₂).machine.Implements
      fun input ↦ FreeM.bind (program input) fun value ↦ next (value, input) := by
  intro input
  rw [denote_seqCompWithInput, h₁ input, FreeM.toResumption_bind]
  congr 1
  funext value
  exact h₂ (value, input)

/-- A handoff envelope for the input-retaining first phase, from one stated over `R₁`'s own
conforming traces. The second-phase bound may read the original input as well as the returned
value. -/
def SeqCompHandoffBound.withInput {R₁ : QuantitativeRealization Q bd}
    {allows : ∀ position, p.B position → Prop} {secondBound : B × A → ExecutionCost}
    (envelope : A → ExecutionCost)
    (returned_le : ∀ input {finish : R₁.machine.State}
      (trace : R₁.ExecutionTrace (R₁.machine.init input) finish), trace.Conforms allows →
        ∀ {value : B}, R₁.machine.view finish = Sum.inl value →
          secondBound (value, input) ≤ envelope input) :
    SeqCompHandoffBound R₁.withInput allows secondBound where
  bound := envelope
  returned_le input finish trace htrace value hview := by
    obtain ⟨hR, hsnd⟩ := R₁.machine.view_eq_return_of_withInput_view_eq_return hview
    have hfinish : finish.2 = input := ExecutionTrace.snd_finish_eq R₁ trace
    have hvalue : value = (value.1, input) := by
      rw [← hfinish, ← hsnd]
    rw [hvalue]
    exact returned_le input (ExecutionTrace.ofWithInput R₁ trace)
      ((ExecutionTrace.conforms_ofWithInput R₁ allows trace).mpr htrace) hR

/-- **Bounded strong bind.** The first phase is charged its bound plus the strength carry, the
second phase through the handoff envelope, and `seqComp`'s structural wiring through its
certificate. -/
theorem RunsWithinUnder.seqCompWithInput {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.strongMid outRep)}
    {allows : ∀ position, p.B position → Prop}
    {firstBound : A → ExecutionCost} {secondBound : B × A → ExecutionCost}
    (first : R₁.RunsWithinUnder allows firstBound) (carry : WithInputCostCertificate R₁ allows)
    (second : R₂.RunsWithinUnder allows secondBound)
    (handoff : SeqCompHandoffBound R₁.withInput allows secondBound)
    (certificate : SeqCompCostCertificate R₁.withInput R₂ allows) :
    (R₁.seqCompWithInput R₂).RunsWithinUnder allows fun input ↦
      (firstBound input).withCarry (firstBound input).queries (carry.carry input) +
        handoff.bound input + certificate.overhead input :=
  (first.withInput carry).seqComp second handoff certificate

omit [DecidableEq p.A] in
/-- The query budget of the bounded strong bind is exactly the sum of the first phase's budget and
the handoff envelope's: neither the strength carry nor the structural wiring adds queries. -/
theorem queries_seqCompWithInput_bound (first second overhead : ExecutionCost) (c : Carry) :
    (first.withCarry first.queries c + second + overhead).queries =
      first.queries + second.queries + overhead.queries := rfl

section Laws

variable [CC : Q.HasCompositionCost] [PC : Q.HasProdCost] [SC : Q.HasSumCost]
  [OC : Q.HasOptionCost] [DC : Q.IsDistributiveCost]

/-- The bounded strong bind with the strength carry discharged from cost laws. -/
theorem RunsWithinUnder.seqCompWithInput_of_laws {R₁ : QuantitativeRealization Q bd}
    {R₂ : QuantitativeRealization Q (bd.strongMid outRep)}
    {allows : ∀ position, p.B position → Prop}
    {firstBound : A → ExecutionCost} {secondBound : B × A → ExecutionCost}
    (first : R₁.RunsWithinUnder allows firstBound)
    (second : R₂.RunsWithinUnder allows secondBound)
    (handoff : SeqCompHandoffBound R₁.withInput allows secondBound)
    (certificate : SeqCompCostCertificate R₁.withInput R₂ allows) :
    (R₁.seqCompWithInput R₂).RunsWithinUnder allows fun input ↦
      (firstBound input).withCarry (firstBound input).queries
          (lawCarry (Q := Q) (firstBound input) (Q.size bd.input input)) +
        handoff.bound input + certificate.overhead input :=
  first.seqCompWithInput (WithInputCostCertificate.ofLaws first) second handoff certificate

end Laws

end SeqCompWithInput

end QuantitativeRealization

/-! ## Program-level closure -/

section Program

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive]

/-- Bounded quantitative realizability is closed under strength
`program ↦ fun a ↦ (·, a) <$> program a`, with the law-derived carry. -/
theorem IsQuantitativelyRealizableWithinUnder.withInput
    [CC : Q.HasCompositionCost] [PC : Q.HasProdCost] [SC : Q.HasSumCost]
    [OC : Q.HasOptionCost] [DC : Q.IsDistributiveCost]
    {allows : ∀ position, p.B position → Prop} {program : A → FreeM p B}
    {bound : A → ExecutionCost}
    (h : IsQuantitativelyRealizableWithinUnder Q bd allows program bound) :
    IsQuantitativelyRealizableWithinUnder Q (bd.withOut (P.prod bd.out bd.input)) allows
      (fun input ↦ FreeM.map (fun value ↦ (value, input)) (program input))
      fun input ↦ (bound input).withCarry (bound input).queries
        (QuantitativeRealization.lawCarry (Q := Q) (bound input) (Q.size bd.input input)) := by
  obtain ⟨R, hR, hbound⟩ := h
  exact ⟨R.withInput, R.withInput_implements hR, hbound.withInput_of_laws⟩

/-- Quantitative realizability is closed under the Kleisli strong bind. -/
theorem IsQuantitativelyRealizableBy.seqCompWithInput {D : Type u} {outRep : C.Str D}
    {program : A → FreeM p B} {next : B × A → FreeM p D}
    (first : IsQuantitativelyRealizableBy Q bd program)
    (second : IsQuantitativelyRealizableBy Q (bd.strongMid outRep) next) :
    IsQuantitativelyRealizableBy Q (bd.withOut outRep)
      fun input ↦ FreeM.bind (program input) fun value ↦ next (value, input) := by
  obtain ⟨R₁, h₁⟩ := first
  obtain ⟨R₂, h₂⟩ := second
  exact ⟨R₁.seqCompWithInput R₂, R₁.seqCompWithInput_implements R₂ h₁ h₂⟩

end Program

end PFunctor.DynSystem.DynComputation
