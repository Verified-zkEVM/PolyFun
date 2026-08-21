/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Realizability.Basic

/-!
# Closure properties of admissible realizability

Realizability is closed under the operations that leave a machine's dynamics
intact or reindex them by an admissible map, and it transports along refinements
of the ambient step class. Each theorem asks of the class exactly the structure
its construction consumes:

* `isRealizableBy_ofFn` — an immediately returning program, realized by the
  one-step machine whose states are its own results. Needs the returning map to
  be admissible.
* `IsRealizableBy.precomp` / `IsRealizableWithin.precomp` — input
  precomposition, realized by `setInit`. The machine, its state representation,
  and both of its remaining step maps are untouched, so only the initialization
  obligation changes.
* `IsRealizableBy.mapResult` / `IsRealizableWithin.mapResult` — postcomposition
  on results, realized by `mapResult`. The readout gains a `Sum.map` and the
  transition is unchanged.
* `IsRealizableBy.seqComp` / `IsRealizableWithin.seqComp` — **closure under
  `FreeM.bind`**, realized by `seqComp`. The state is the coproduct of the two
  phases' states, and budgets add. Needs `IsDistributive`.
* `IsRealizableBy.wrap` / `IsRealizableWithin.wrap` — interface transport along a
  lens, realized by `wrap`. Needs the lens to be `Lens.IsAdmissible`.
* `IsRealizableBy.mono` / `IsRealizableWithin.mono'` — transport along a
  `StepClass.Refines`.

Budget monotonicity and the bridge from the bounded to the unbounded predicate
live in `PolyFun.Realizability.Basic`.

## Where the structure is spent

Distributivity is consumed in exactly one place, and only twice: the composite
`update?` of a sequential composition splits on the state summand, and then on the
first phase's readout, each time retaining the answer index. The *readout* side of
the same composition needs no products at all — only `comp_mem`, `elim_mem`, and
`inr_mem`.

None of this needs a decidable-equality test on interface positions, and that is a
consequence of `update?` being partial: each phase's own transition already returns
`none` on an answer it is not waiting for, so the composite inherits the tag test
rather than performing it. With the total `updateFlat` no uniform equation holds and
an equality-test axiom would be forced; see `PolyFun.Realizability.Machine`.

Interface transport is the one place a tag test does surface, because pulling an
answer back along a lens must compare it against the position the lens exposes.
That is why `wrap` takes a `Lens.IsAdmissible` hypothesis while `seqComp` takes
none.
-/

@[expose] public section

universe u v v₂

namespace PFunctor

namespace DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {α β : Type u}
  {C : StepClass.{u, v}} [P : C.HasProd] [S : C.HasSum] [O : C.HasOption]
  [DecidableEq p.A] {bd : Boundary C p α β} {program : α → FreeM p β}

/-! ## Immediately returning programs -/

/-- An immediately returning program is realizable exactly when its returning map
is admissible. The realizing machine takes the result type itself as its state:
`head` is the left injection and the flattened transition is the first
projection. -/
theorem isRealizableBy_ofFn {f : α → β} (hf : C.Hom bd.input bd.out f) :
    IsRealizableBy C bd (fun input => FreeM.pure (f input)) := by
  refine ⟨⟨ofFn (p := p) f, bd.out, hf, StepClass.HasSum.inl_mem bd.out bd.pos, ?_⟩,
    ?_⟩
  · refine (StepClass.HasOption.none_mem (bd.stateIdx bd.out) bd.out).congr ?_
    intro step
    exact (update?_of_view_return (ofFn (p := p) f) (view_ofFn f step.1) step.2).symm
  · intro input
    rw [denote_ofFn]
    simp

/-- A constant program is realizable whenever the constant is: the special case
of `isRealizableBy_ofFn` at a constant returning map. -/
theorem isRealizableBy_pure {value : β}
    (hvalue : C.Hom bd.input bd.out fun _ : α => value) :
    IsRealizableBy C bd fun _ : α => (FreeM.pure value : FreeM p β) :=
  isRealizableBy_ofFn hvalue

/-! ## Input precomposition -/

/-- Input precomposition along an admissible map. The realizing machine is the
original one with a new initialization, so its readout and transition maps — and
hence their admissibility proofs — are shared definitionally. -/
theorem IsRealizableBy.precomp {γ : Type u} {inputRep : C.Str γ} {f : γ → α}
    (h : IsRealizableBy C bd program) (hf : C.Hom inputRep bd.input f) :
    IsRealizableBy C (bd.withInput inputRep) fun input => program (f input) := by
  obtain ⟨R, hR⟩ := h
  refine ⟨⟨R.machine.contramapInput f, R.state, ?_, R.head_mem, R.update_mem⟩,
    hR.contramapInput f⟩
  change C.Hom inputRep R.state (R.machine.init ∘ f)
  exact C.comp_mem hf R.init_mem

/-- Input precomposition preserves the query budget: reindexing inputs performs
no queries of its own. -/
theorem IsRealizableWithin.precomp {γ : Type u} {inputRep : C.Str γ} {f : γ → α}
    {k : ℕ} (h : IsRealizableWithin C bd program k)
    (hf : C.Hom inputRep bd.input f) :
    IsRealizableWithin C (bd.withInput inputRep) (fun input => program (f input)) k := by
  obtain ⟨R, hR⟩ := h
  rw [implementsWithin_iff_implements_and_bound] at hR
  refine ⟨⟨R.machine.contramapInput f, R.state, ?_, R.head_mem, R.update_mem⟩, ?_⟩
  · change C.Hom inputRep R.state (R.machine.init ∘ f)
    exact C.comp_mem hf R.init_mem
  · rw [implementsWithin_iff_implements_and_bound]
    exact ⟨hR.1.contramapInput f, fun input => hR.2 (f input)⟩

/-! ## Result postcomposition -/

/-- Postcomposition on results along an admissible map. The realizing machine is
the original one with its readout postcomposed, which acts on the one-step
readout `β ⊕ p.A` by `Sum.map` and leaves the flattened transition alone. -/
theorem IsRealizableBy.mapResult {γ : Type u} {outRep : C.Str γ} {g : β → γ}
    (h : IsRealizableBy C bd program) (hg : C.Hom bd.out outRep g) :
    IsRealizableBy C (bd.withOut outRep)
      fun input => FreeM.map g (program input) := by
  obtain ⟨R, hR⟩ := h
  refine ⟨⟨R.machine.mapResult g, R.state, R.init_mem, ?_, ?_⟩, hR.mapResult g⟩
  · refine (C.comp_mem R.head_mem
      (StepClass.HasSum.map_mem hg (C.id_mem bd.pos))).congr ?_
    intro state
    exact (head_mapResult R.machine g state).symm
  · refine R.update_mem.congr ?_
    intro step
    exact (update?_mapResult R.machine g step).symm

/-- Postcomposition on results preserves the query budget: mapping a returned
value performs no queries of its own. -/
theorem IsRealizableWithin.mapResult {γ : Type u} {outRep : C.Str γ} {g : β → γ}
    {k : ℕ} (h : IsRealizableWithin C bd program k)
    (hg : C.Hom bd.out outRep g) :
    IsRealizableWithin C (bd.withOut outRep)
      (fun input => FreeM.map g (program input)) k := by
  obtain ⟨R, hR⟩ := h
  rw [implementsWithin_iff_implements_and_bound] at hR
  refine ⟨⟨R.machine.mapResult g, R.state, R.init_mem, ?_, ?_⟩, ?_⟩
  · refine (C.comp_mem R.head_mem
      (StepClass.HasSum.map_mem hg (C.id_mem bd.pos))).congr ?_
    intro state
    exact (head_mapResult R.machine g state).symm
  · refine R.update_mem.congr ?_
    intro step
    exact (update?_mapResult R.machine g step).symm
  · rw [implementsWithin_iff_implements_and_bound]
    refine ⟨hR.1.mapResult g, fun input => ?_⟩
    exact (FreeM.isRollBound_map_iff (program input) g k _ _).mpr (hR.2 input)

/-! ## Sequential composition -/

section SeqComp

variable [D : C.IsDistributive] {γ : Type u} {outRep : C.Str γ}
  {program₁ : α → FreeM p β} {program₂ : β → FreeM p γ}

/-- The admissible realization of a sequential composition.

The state is the coproduct of the two phases' states. The readout needs only
`comp_mem`, `elim_mem`, and `inr_mem` — no products at all. The partial transition
is where distributivity enters, twice: once to split on the state summand, once to
split on the first phase's readout while retaining the answer index. -/
private def seqCompRealization (R₁ : Realization C bd)
    (R₂ : Realization C (bd.mid outRep)) :
    Realization C (bd.withOut outRep) where
  machine := R₁.machine.seqComp R₂.machine
  state := S.sum R₁.state R₂.state
  init_mem := by
    refine (C.comp_mem R₁.init_mem (S.inl_mem R₁.state R₂.state)).congr ?_
    intro input
    rfl
  head_mem := by
    refine (S.elim_mem
      (C.comp_mem R₁.head_mem
        (S.elim_mem (C.comp_mem R₂.init_mem R₂.head_mem)
          (S.inr_mem outRep bd.pos)))
      R₂.head_mem).congr ?_
    intro state
    cases state with
    | inl state₁ => exact (head_seqComp_inl R₁.machine R₂.machine state₁).symm
    | inr state₂ => exact (head_seqComp_inr R₁.machine R₂.machine state₂).symm
  update_mem := by
    -- The right summand: advance the second phase and re-tag the result.
    have hRight : C.Hom (P.prod R₂.state bd.idx)
        (StepClass.HasOption.option (S.sum R₁.state R₂.state))
        (fun x => Option.map Sum.inr (R₂.machine.update? x)) :=
      C.comp_mem R₂.update_mem
        (StepClass.HasOption.omap_mem (S.inr_mem R₁.state R₂.state))
    -- The left summand, first phase still exposing a query.
    have hQuery : C.Hom (P.prod bd.pos (P.prod R₁.state bd.idx))
        (StepClass.HasOption.option (S.sum R₁.state R₂.state))
        (fun y => Option.map Sum.inl (R₁.machine.update? y.2)) :=
      C.comp_mem (P.snd_mem bd.pos (P.prod R₁.state bd.idx))
        (C.comp_mem R₁.update_mem
          (StepClass.HasOption.omap_mem (S.inl_mem R₁.state R₂.state)))
    -- The left summand, first phase already returned: hand over to the second.
    have hHandoff : C.Hom (P.prod bd.out (P.prod R₁.state bd.idx))
        (StepClass.HasOption.option (S.sum R₁.state R₂.state))
        (fun y => Option.map Sum.inr
          (R₂.machine.update? (R₂.machine.init y.1, y.2.2))) :=
      C.comp_mem
        (P.pair_mem
          (C.comp_mem (P.fst_mem bd.out (P.prod R₁.state bd.idx)) R₂.init_mem)
          (C.comp_mem (P.snd_mem bd.out (P.prod R₁.state bd.idx))
            (P.snd_mem R₁.state bd.idx)))
        hRight
    -- Splitting on the first phase's readout, retaining the state and the index.
    have hLeft : C.Hom (P.prod R₁.state bd.idx)
        (StepClass.HasOption.option (S.sum R₁.state R₂.state))
        (fun x => Sum.elim
          (fun value => Option.map Sum.inr
            (R₂.machine.update? (R₂.machine.init value, x.2)))
          (fun _ : p.A => Option.map Sum.inl (R₁.machine.update? x))
          (R₁.machine.head x.1)) :=
      C.comp_mem
        (P.withInput_mem (C.comp_mem (P.fst_mem R₁.state bd.idx) R₁.head_mem))
        (StepClass.IsDistributive.elimCtx_mem hHandoff hQuery)
    -- Splitting on the state summand.
    refine (StepClass.IsDistributive.elimCtx_mem hLeft hRight).congr ?_
    intro x
    obtain ⟨state, index⟩ := x
    cases state with
    | inl state₁ =>
        exact (update?_seqComp_inl R₁.machine R₂.machine state₁ index).symm
    | inr state₂ =>
        exact (update?_seqComp_inr R₁.machine R₂.machine state₂ index).symm

/-- **Closure under `bind`.** A realization of the first phase and a realization of
the second compose into a realization of their sequential composition.

The middle boundary is `bd.mid outRep`: the second phase reads the first's results
and shares its interface. Distributivity is what the composite transition needs,
and only there — the readout side needs no products at all. -/
theorem IsRealizableBy.seqComp (h₁ : IsRealizableBy C bd program₁)
    (h₂ : IsRealizableBy C (bd.mid outRep) program₂) :
    IsRealizableBy C (bd.withOut outRep)
      fun input => FreeM.bind (program₁ input) program₂ := by
  obtain ⟨R₁, hR₁⟩ := h₁
  obtain ⟨R₂, hR₂⟩ := h₂
  exact ⟨seqCompRealization R₁ R₂, hR₁.seqComp hR₂⟩

/-- Sequential composition of bounded realizations, with additive budgets. The
query budget is exactly the one the underlying `ImplementsWithin.seqComp`
supplies. -/
theorem IsRealizableWithin.seqComp {k₁ k₂ : ℕ}
    (h₁ : IsRealizableWithin C bd program₁ k₁)
    (h₂ : IsRealizableWithin C (bd.mid outRep) program₂ k₂) :
    IsRealizableWithin C (bd.withOut outRep)
      (fun input => FreeM.bind (program₁ input) program₂) (k₁ + k₂) := by
  obtain ⟨R₁, hR₁⟩ := h₁
  obtain ⟨R₂, hR₂⟩ := h₂
  exact ⟨seqCompRealization R₁ R₂, hR₁.seqComp hR₂⟩

end SeqComp

/-! ## Interface transport -/

section Wrap

variable {q : PFunctor.{u, u}} [DecidableEq q.A]

variable (posRep : C.Str q.A) (idxRep : C.Str q.Idx)

/-- A lens is `C`-admissible, relative to a boundary for its source interface and
representations for its target interface, when its position map and its flattened
index pullback are `C`-morphisms.

Two fields rather than one existential: the pullback is uniquely determined by the
lens, so it is `Lens.pullHeadIdx` and only its admissibility is a hypothesis.

Unlike `Lens.IsCartesian` this has no `.id` and no `.comp`, and that is not an
oversight. `pullHeadIdx` compares the incoming answer's tag against the position
the lens exposes, so even the *identity* lens's pullback performs a decidable
equality test on positions — which is exactly the operation the rest of this layer
is designed not to require of a step class. Admissibility of a lens is therefore a
genuine hypothesis about the class, satisfiable by every realistic one but not
derivable from the mixins. That is also why `seqComp` needs no such hypothesis:
each phase's own `update?` performs its own tag test internally. -/
structure _root_.PFunctor.Lens.IsAdmissible (C : StepClass.{u, v}) [C.HasProd]
    [C.HasSum] [C.HasOption] {p q : PFunctor.{u, u}} [DecidableEq q.A]
    {α β : Type u} (bd : Boundary C p α β) (posRep : C.Str q.A)
    (idxRep : C.Str q.Idx) (lens : Lens p q) : Prop where
  /-- The position map is admissible. -/
  onPos : C.Hom bd.pos posRep lens.toFunA
  /-- The flattened index pullback is admissible. -/
  onPull : C.Hom (StepClass.HasProd.prod bd.head idxRep)
    (StepClass.HasOption.option bd.idx) (lens.pullHeadIdx β)

/-- Interface transport along an admissible lens. The readout is post-composed
with the lens's position map; the transition pulls an answer back along the lens
before feeding it to the underlying computation.

The resolved case needs no constant-map axiom: `pullHeadIdx` returns `none` at a
resolved readout, and the underlying `update?` is `none` there anyway. -/
theorem IsRealizableBy.wrap {lens : Lens p q}
    (hlens : lens.IsAdmissible C bd posRep idxRep)
    (h : IsRealizableBy C bd program) :
    IsRealizableBy C (bd.withInterface posRep idxRep)
      fun input => (program input).mapLens lens := by
  obtain ⟨R, hR⟩ := h
  refine ⟨⟨R.machine.wrap lens, R.state, R.init_mem, ?_, ?_⟩, hR.wrap lens⟩
  · refine (C.comp_mem R.head_mem
      (S.map_mem (C.id_mem bd.out) hlens.onPos)).congr ?_
    intro state
    rfl
  · refine (C.comp_mem
      (P.withInput_mem (C.comp_mem (P.pairRight_mem R.head_mem) hlens.onPull))
      (StepClass.HasOption.obindCtx_mem
        (C.comp_mem
          (P.pair_mem
            (C.comp_mem (P.snd_mem bd.idx (P.prod R.state idxRep))
              (P.fst_mem R.state idxRep))
            (P.fst_mem bd.idx (P.prod R.state idxRep)))
          R.update_mem))).congr ?_
    intro x
    obtain ⟨state, index⟩ := x
    obtain ⟨iposition, idirection⟩ := index
    exact (update?_wrap R.machine lens state iposition idirection).symm

/-- Interface transport preserves the query budget: a lens relabels positions and
reindexes directions, leaving the branching structure alone. -/
theorem IsRealizableWithin.wrap {lens : Lens p q} {k : ℕ}
    (hlens : lens.IsAdmissible C bd posRep idxRep)
    (h : IsRealizableWithin C bd program k) :
    IsRealizableWithin C (bd.withInterface posRep idxRep)
      (fun input => (program input).mapLens lens) k := by
  obtain ⟨R, hR⟩ := h
  rw [implementsWithin_iff_implements_and_bound] at hR
  obtain ⟨R', hR'⟩ :=
    IsRealizableBy.wrap (program := program) posRep idxRep hlens ⟨R, hR.1⟩
  refine ⟨R', ?_⟩
  rw [implementsWithin_iff_implements_and_bound]
  exact ⟨hR', fun input => FreeM.isTotalRollBound_mapLens lens _ (hR.2 input)⟩

end Wrap

/-! ## Enlarging the step class -/

variable {D : StepClass.{u, v₂}} [D.HasProd] [D.HasSum] [D.HasOption]

/-- Realizability transports along a refinement of step classes: a realization by
an admissible machine for a small class is one for every larger class. -/
theorem IsRealizableBy.mono (Ref : C.Refines D) (h : IsRealizableBy C bd program) :
    IsRealizableBy D (bd.mapRefines Ref) program := by
  obtain ⟨R, hR⟩ := h
  refine ⟨⟨R.machine, Ref.str R.state, Ref.hom R.init_mem, ?_, ?_⟩, hR⟩
  · rw [Boundary.head, Boundary.mapRefines, ← Ref.str_sum]
    exact Ref.hom R.head_mem
  · rw [Boundary.stateIdx, Boundary.mapRefines, ← Ref.str_prod, ← Ref.str_option]
    exact Ref.hom R.update_mem

/-- Bounded realizability transports along a refinement of step classes. -/
theorem IsRealizableWithin.mono' {k : ℕ} (Ref : C.Refines D)
    (h : IsRealizableWithin C bd program k) :
    IsRealizableWithin D (bd.mapRefines Ref) program k := by
  obtain ⟨R, hR⟩ := h
  refine ⟨⟨R.machine, Ref.str R.state, Ref.hom R.init_mem, ?_, ?_⟩, hR⟩
  · rw [Boundary.head, Boundary.mapRefines, ← Ref.str_sum]
    exact Ref.hom R.head_mem
  · rw [Boundary.stateIdx, Boundary.mapRefines, ← Ref.str_prod, ← Ref.str_option]
    exact Ref.hom R.update_mem

end DynSystem.DynComputation

end PFunctor
