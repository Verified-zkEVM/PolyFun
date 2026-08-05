/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.DynComputation.Bounded

/-!
# First-order step maps of a returning dynamical computation

A `DynComputation`'s dynamics are carried by `view`, whose codomain
`β ⊕ p.Obj State` stores a *function-valued* continuation and whose second
component is dependent on the exposed position. Neither shape can be constrained
by a predicate on plain functions. This module presents the same dynamics as
first-order maps between plain types:

* `head : State → β ⊕ p.A` — the one-step readout: the value returned at a
  resolved state, or the query position exposed at an unresolved one. This is
  *definitionally* the position map of the computation's underlying lens.
* `update? : State × p.Idx → Option State` — the continuation, flattened onto the
  whole index space `p.Idx = Σ a, p.B a`. `none` means the pair is not a step the
  computation can take: the state has already returned, or the answer is tagged
  with a position the computation is not exposing.

**Partiality is load-bearing.** The total variant `updateFlat`, which collapses
`none` to the unchanged state, does not compose across a state coproduct with a
handoff: at a left state whose intermediate value has been handed to the second
phase, a mismatched tag leaves the composite in the *left* summand while the
second phase alone would stay at its own initial state. Reconciling those junk
values would require the ambient class to contain a decidable-equality test on
interface positions. With `none` they agree, and `update?_seqComp_inl` becomes an
equation unconditional in the answer index.

Nothing constrains where `none` occurs beyond what the semantics forces, and the
run semantics never feeds a direction at a position other than the exposed one, so
the flattening carries no coherence side conditions — the only cost is
`DecidableEq p.A`.

`updateFlat`, `output`, `expose`, and `stepD` are the derived accessors a
machine-facing cost model consumes: a total state-to-state transition, an optional
readout, a total query selector, and the deterministic one-step transition against
a fixed pure handler.

`ofStep_step_eq_of_flat_eq` records that the presentation is faithful: a step
function is determined by the `head` and `update?` it induces, so constraining
those two maps (plus `init`) is a constraint on the machine itself and not on an
arbitrary projection of it.

Every map here is spelled with `Sum` and `Option` combinators rather than with
`match`. An auto-generated matcher abstracts the computation and blocks
unification across distinct input types, whereas combinator applications reduce
by congruence over the shared `view`; that is exactly why the `setInit`
transport lemmas below hold by `rfl`.
-/

@[expose] public section

universe u v w uA uB uA₂ uB₂ uα uβ uγ

namespace PFunctor

namespace DynSystem.DynComputation

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

/-! ## The one-step readout -/

/-- The one-step readout of a returning computation: the value returned at a
resolved state, or the query position exposed at an unresolved one.

This is exactly the position map of the computation's underlying lens, so
computations sharing `toMachine` share it definitionally, and interface or
result transport act on it by plain post-composition. -/
def head (M : DynComputation.{u} p α β) : M.State → β ⊕ p.A :=
  M.toDynSystem.expose

theorem head_def (M : DynComputation.{u} p α β) (state : M.State) :
    M.head state = M.toDynSystem.expose state := rfl

private theorem sumMap_fst_unpack {X : Type w}
    (step : (C.{uβ, uB} β + p).Obj X) :
    Sum.map id Sigma.fst (Resumption.unpack (β := β) step) = step.1 := by
  rcases step with ⟨position, next⟩
  cases position <;> rfl

/-- The readout is the position component of the one-step view: it forgets the
continuation and keeps the returned value or the exposed position. -/
theorem head_eq_sumMap_view (M : DynComputation.{u} p α β) (state : M.State) :
    M.head state = Sum.map id Sigma.fst (M.view state) :=
  (sumMap_fst_unpack (M.toDynSystem.out state)).symm

theorem head_eq_inl_of_view (M : DynComputation.{u} p α β)
    {state : M.State} {value : β} (hview : M.view state = Sum.inl value) :
    M.head state = Sum.inl value := by
  rw [head_eq_sumMap_view, hview]; rfl

theorem head_eq_inr_of_view (M : DynComputation.{u} p α β)
    {state : M.State} {query : p.Obj M.State}
    (hview : M.view state = Sum.inr query) :
    M.head state = Sum.inr query.1 := by
  rw [head_eq_sumMap_view, hview]; rfl

/-! ## The flattened transition -/

/-- The continuation of a returning computation, flattened onto the whole index
space as a *partial* function.

`none` means the pair is not a step the computation can take: the state has
already returned, or the answer is tagged with a position the computation is not
exposing. `some state'` means the answer is one the computation is waiting for and
`state'` is where it goes.

Partiality is what makes the flattening compositional. The total variant
`updateFlat` collapses `none` to the unchanged state, which suits a cost model
that wants a plain state-to-state map, but does not compose across a state
coproduct with a handoff: at a left state whose intermediate value has been handed
over, the composite stays in the left summand on a mismatched tag while the second
phase alone would stay at its own initial state. With `none` both are `none`. -/
def update? [DecidableEq p.A] (M : DynComputation.{u} p α β) :
    M.State × p.Idx → Option M.State := fun step =>
  (M.view step.1).elim (fun _ => none)
    (fun query =>
      if h : step.2.1 = query.1 then some (query.2 (h ▸ step.2.2)) else none)

theorem update?_of_view_return [DecidableEq p.A] (M : DynComputation.{u} p α β)
    {state : M.State} {value : β} (hview : M.view state = Sum.inl value)
    (index : p.Idx) : M.update? (state, index) = none := by
  unfold update?; rw [hview]; rfl

theorem update?_of_view_query [DecidableEq p.A] (M : DynComputation.{u} p α β)
    {state : M.State} {position : p.A} {next : p.B position → M.State}
    (hview : M.view state = Sum.inr ⟨position, next⟩)
    (direction : p.B position) :
    M.update? (state, ⟨position, direction⟩) = some (next direction) := by
  unfold update?; rw [hview]
  simp only [Sum.elim_inr, dif_pos]

theorem update?_of_view_query_of_ne [DecidableEq p.A]
    (M : DynComputation.{u} p α β) {state : M.State} {query : p.Obj M.State}
    (hview : M.view state = Sum.inr query) {index : p.Idx}
    (hne : index.1 ≠ query.1) : M.update? (state, index) = none := by
  unfold update?; rw [hview]
  simp only [Sum.elim_inr, dif_neg hne]

/-- The total variant of the flattened transition: a mismatched tag or an already
returned state leaves the state unchanged.

This is the shape a machine-facing cost model wants, since it is a plain
state-to-state map. It is derived from `update?`, so the two never disagree about
which answers are steps. -/
def updateFlat [DecidableEq p.A] (M : DynComputation.{u} p α β)
    (step : M.State × p.Idx) : M.State :=
  (M.update? step).getD step.1

theorem updateFlat_eq_getD [DecidableEq p.A] (M : DynComputation.{u} p α β)
    (step : M.State × p.Idx) :
    M.updateFlat step = (M.update? step).getD step.1 := rfl

theorem updateFlat_of_view_return [DecidableEq p.A] (M : DynComputation.{u} p α β)
    {state : M.State} {value : β} (hview : M.view state = Sum.inl value)
    (index : p.Idx) : M.updateFlat (state, index) = state := by
  unfold updateFlat; rw [M.update?_of_view_return hview index]; rfl

theorem updateFlat_of_view_query [DecidableEq p.A] (M : DynComputation.{u} p α β)
    {state : M.State} {position : p.A} {next : p.B position → M.State}
    (hview : M.view state = Sum.inr ⟨position, next⟩)
    (direction : p.B position) :
    M.updateFlat (state, ⟨position, direction⟩) = next direction := by
  unfold updateFlat; rw [M.update?_of_view_query hview direction]; rfl

theorem updateFlat_of_view_query_of_ne [DecidableEq p.A]
    (M : DynComputation.{u} p α β) {state : M.State} {query : p.Obj M.State}
    (hview : M.view state = Sum.inr query) {index : p.Idx}
    (hne : index.1 ≠ query.1) : M.updateFlat (state, index) = state := by
  unfold updateFlat; rw [M.update?_of_view_query_of_ne hview hne]; rfl

/-! ## Derived machine-facing accessors -/

/-- The optional readout of a returning computation: the returned value at a
resolved state and `none` at an unresolved one. -/
def output (M : DynComputation.{u} p α β) (state : M.State) : Option β :=
  (M.head state).getLeft?

/-- The query a computation selects at a state. At a resolved state, where no
query is exposed, this is the interface's default position; the run semantics
never consults that value. -/
def expose [Inhabited p.A] (M : DynComputation.{u} p α β) (state : M.State) : p.A :=
  (M.head state).elim (fun _ => default) id

/-- The deterministic one-step transition of a computation against a fixed pure
handler. A resolved state is absorbing. -/
def stepD (M : DynComputation.{u} p α β) (handler : (a : p.A) → p.B a)
    (state : M.State) : M.State :=
  (M.view state).elim (fun _ => state) (fun query => query.2 (handler query.1))

@[simp] theorem output_eq_some_iff (M : DynComputation.{u} p α β)
    (state : M.State) (value : β) :
    M.output state = some value ↔ M.head state = Sum.inl value := by
  unfold output
  cases M.head state <;> simp

@[simp] theorem stepD_of_view_return (M : DynComputation.{u} p α β)
    (handler : (a : p.A) → p.B a) {state : M.State} {value : β}
    (hview : M.view state = Sum.inl value) : M.stepD handler state = state := by
  unfold stepD; rw [hview]; rfl

@[simp] theorem stepD_of_view_query (M : DynComputation.{u} p α β)
    (handler : (a : p.A) → p.B a) {state : M.State} {query : p.Obj M.State}
    (hview : M.view state = Sum.inr query) :
    M.stepD handler state = query.2 (handler query.1) := by
  unfold stepD; rw [hview]; rfl

/-! ## Transport along replacement of the initialization

Every step map is shared definitionally by computations that share `toMachine`.
-/

@[simp] theorem head_setInit {γ : Type uγ} (M : DynComputation.{u} p α β)
    (g : γ → M.State) (state : M.State) :
    (M.setInit g).head state = M.head state := rfl

@[simp] theorem update?_setInit [DecidableEq p.A] {γ : Type uγ}
    (M : DynComputation.{u} p α β) (g : γ → M.State) (step : M.State × p.Idx) :
    (M.setInit g).update? step = M.update? step := rfl

@[simp] theorem updateFlat_setInit [DecidableEq p.A] {γ : Type uγ}
    (M : DynComputation.{u} p α β) (g : γ → M.State) (step : M.State × p.Idx) :
    (M.setInit g).updateFlat step = M.updateFlat step := rfl

@[simp] theorem output_setInit {γ : Type uγ} (M : DynComputation.{u} p α β)
    (g : γ → M.State) (state : M.State) :
    (M.setInit g).output state = M.output state := rfl

@[simp] theorem expose_setInit [Inhabited p.A] {γ : Type uγ}
    (M : DynComputation.{u} p α β) (g : γ → M.State) (state : M.State) :
    (M.setInit g).expose state = M.expose state := rfl

@[simp] theorem stepD_setInit {γ : Type uγ} (M : DynComputation.{u} p α β)
    (g : γ → M.State) (handler : (a : p.A) → p.B a) (state : M.State) :
    (M.setInit g).stepD handler state = M.stepD handler state := rfl

/-! ## Transport along result mapping -/

@[simp] theorem head_mapResult {γ : Type uγ} (M : DynComputation.{u} p α β)
    (f : β → γ) (state : M.State) :
    (M.mapResult f).head state = Sum.map f id (M.head state) := rfl

@[simp] theorem update?_mapResult [DecidableEq p.A] {γ : Type uγ}
    (M : DynComputation.{u} p α β) (f : β → γ) (step : M.State × p.Idx) :
    (M.mapResult f).update? step = M.update? step := by
  unfold update?
  rw [mapResult_view]
  cases hview : M.view step.1 with
  | inl value => rfl
  | inr query => rfl

@[simp] theorem updateFlat_mapResult [DecidableEq p.A] {γ : Type uγ}
    (M : DynComputation.{u} p α β) (f : β → γ) (step : M.State × p.Idx) :
    (M.mapResult f).updateFlat step = M.updateFlat step := by
  unfold updateFlat
  rw [M.update?_mapResult f step]
  rfl

/-! ## Transport along interface transport -/

@[simp] theorem head_wrap {q : PFunctor.{uA₂, uB₂}} (M : DynComputation.{u} p α β)
    (lens : Lens p q) (state : M.State) :
    (M.wrap lens).head state = Sum.map id lens.toFunA (M.head state) := rfl

/-- The flattened index pullback of a lens, absorbing the resolved case: an answer
at the position the lens exposes for `a` is pulled back to an answer at `a`, while
a resolved readout or a mismatched tag has no preimage.

The domain carries the machine's whole readout `β ⊕ p.A` rather than just a
position. Absorbing the resolved case here is what lets interface transport avoid
`expose` and hence avoid needing an admissible constant `default`. -/
def _root_.PFunctor.Lens.pullHeadIdx {q : PFunctor.{uA₂, uB₂}} [DecidableEq q.A]
    (lens : Lens p q) (β : Type uβ) : (β ⊕ p.A) × q.Idx → Option p.Idx := fun x =>
  x.1.elim (fun _ => none)
    (fun a =>
      if h : x.2.1 = lens.toFunA a then
        some ⟨a, lens.toFunB a (h ▸ x.2.2)⟩
      else none)

/-- Interface transport pulls an answer back along the lens before feeding it to
the underlying computation. The resolved case needs no special handling: the
underlying `update?` is already `none` there. -/
theorem update?_wrap {q : PFunctor.{uA₂, uB₂}} [DecidableEq p.A] [DecidableEq q.A]
    (M : DynComputation.{u} p α β) (lens : Lens p q) (state : M.State)
    (iposition : q.A) (idirection : q.B iposition) :
    (M.wrap lens).update? (state, ⟨iposition, idirection⟩) =
      (lens.pullHeadIdx β (M.head state, ⟨iposition, idirection⟩)).bind
        fun index => M.update? (state, index) := by
  cases hview : M.view state with
  | inl value =>
      rw [update?_of_view_return (M.wrap lens)
          (show (M.wrap lens).view state = Sum.inl value by rw [wrap_view, hview])
          ⟨iposition, idirection⟩,
        head_eq_inl_of_view M hview]
      rfl
  | inr query =>
      rcases query with ⟨position, next⟩
      have hcomp : (M.wrap lens).view state =
          Sum.inr ⟨lens.toFunA position,
            fun direction => next (lens.toFunB position direction)⟩ := by
        rw [wrap_view, hview]
      rw [head_eq_inr_of_view M hview]
      by_cases h : iposition = lens.toFunA position
      · subst h
        rw [update?_of_view_query (M.wrap lens) hcomp idirection]
        change _ = Option.bind (dite _ _ _) _
        rw [dif_pos rfl, Option.bind_some, update?_of_view_query M hview]
        rfl
      · rw [update?_of_view_query_of_ne (M.wrap lens) hcomp h]
        change none = Option.bind (dite _ _ _) _
        rw [dif_neg h]
        rfl

/-! ## The step maps of a sequential composition -/

section SeqComp

variable {γ : Type uγ}

theorem seqComp_view_inl_of_return (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) {state₁ : M₁.State} {value : β}
    (hview : M₁.view state₁ = Sum.inl value) :
    (M₁.seqComp M₂).view (Sum.inl state₁) =
      Sum.map (fun result : γ => result)
        (p.map (Sum.inr : M₂.State → M₁.State ⊕ M₂.State))
        (M₂.view (M₂.init value)) := by
  rw [seqComp_view_inl, hview]
  rfl

theorem seqComp_view_inl_of_query (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) {state₁ : M₁.State}
    {position : p.A} {next : p.B position → M₁.State}
    (hview : M₁.view state₁ = Sum.inr ⟨position, next⟩) :
    (M₁.seqComp M₂).view (Sum.inl state₁) =
      Sum.inr ⟨position, fun direction => Sum.inl (next direction)⟩ := by
  rw [seqComp_view_inl, hview]
  rfl

@[simp] theorem head_seqComp_inr (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) (state₂ : M₂.State) :
    (M₁.seqComp M₂).head (Sum.inr state₂) = M₂.head state₂ := by
  rw [head_eq_sumMap_view (M₁.seqComp M₂) (Sum.inr state₂), seqComp_view_inr,
    head_eq_sumMap_view M₂ state₂]
  cases M₂.view state₂ <;> rfl

/-- At a left state the composite reads off `M₁`; a returned intermediate value
is handed over to `M₂`'s initial readout in the same observation. -/
@[simp] theorem head_seqComp_inl (M₁ : DynComputation.{u} p α β)
    (M₂ : DynComputation.{v} p β γ) (state₁ : M₁.State) :
    (M₁.seqComp M₂).head (Sum.inl state₁) =
      Sum.elim (fun value => M₂.head (M₂.init value)) Sum.inr (M₁.head state₁) := by
  rw [head_eq_sumMap_view (M₁.seqComp M₂) (Sum.inl state₁)]
  cases hview : M₁.view state₁ with
  | inl value =>
      rw [seqComp_view_inl_of_return M₁ M₂ hview, head_eq_inl_of_view M₁ hview,
        Sum.elim_inl, head_eq_sumMap_view M₂ (M₂.init value)]
      cases M₂.view (M₂.init value) <;> rfl
  | inr query =>
      rcases query with ⟨position, next⟩
      rw [seqComp_view_inl_of_query M₁ M₂ hview, head_eq_inr_of_view M₁ hview]
      rfl

@[simp] theorem update?_seqComp_inr [DecidableEq p.A]
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (state₂ : M₂.State) (index : p.Idx) :
    (M₁.seqComp M₂).update? (Sum.inr state₂, index) =
      Option.map Sum.inr (M₂.update? (state₂, index)) := by
  obtain ⟨position, direction⟩ := index
  cases hview : M₂.view state₂ with
  | inl value =>
      rw [update?_of_view_return (M₁.seqComp M₂)
          (show (M₁.seqComp M₂).view (Sum.inr state₂) = Sum.inl value by
            rw [seqComp_view_inr, hview]; rfl),
        update?_of_view_return M₂ hview]
      rfl
  | inr query =>
      rcases query with ⟨position₂, next₂⟩
      have hcomp : (M₁.seqComp M₂).view (Sum.inr state₂) =
          Sum.inr ⟨position₂, fun direction => Sum.inr (next₂ direction)⟩ := by
        rw [seqComp_view_inr, hview]; rfl
      by_cases h : position = position₂
      · subst h
        rw [update?_of_view_query (M₁.seqComp M₂) hcomp direction,
          update?_of_view_query M₂ hview direction]
        rfl
      · rw [update?_of_view_query_of_ne (M₁.seqComp M₂) hcomp h,
          update?_of_view_query_of_ne M₂ hview h]
        rfl

/-- At a left state the composite advances `M₁`, unless `M₁` has already returned
an intermediate value, in which case control has been handed to `M₂` initialized
at that value.

This equation is **unconditional in the answer index**, which is exactly what
partiality buys. With the total `updateFlat` no such equation holds: on a
mismatched tag the composite stays at `Sum.inl state₁` while `M₂` alone would stay
at `M₂.init value`. With `none` both agree, and the case where `M₂` also returns
immediately is subsumed for the same reason.

So this single lemma covers what the total variant needed three conditional ones
for — a matching-tag case, a mismatched-tag case, and a both-phases-returned case.
Only the two uniform total-variant lemmas are kept below;
`updateFlat_eq_getD` recovers the rest. -/
@[simp] theorem update?_seqComp_inl [DecidableEq p.A]
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (state₁ : M₁.State) (index : p.Idx) :
    (M₁.seqComp M₂).update? (Sum.inl state₁, index) =
      Sum.elim (fun value => Option.map Sum.inr (M₂.update? (M₂.init value, index)))
        (fun _ : p.A => Option.map Sum.inl (M₁.update? (state₁, index)))
        (M₁.head state₁) := by
  obtain ⟨position, direction⟩ := index
  cases hview : M₁.view state₁ with
  | inr query =>
      rcases query with ⟨position₁, next₁⟩
      rw [head_eq_inr_of_view M₁ hview, Sum.elim_inr]
      have hcomp := seqComp_view_inl_of_query M₁ M₂ hview
      by_cases h : position = position₁
      · subst h
        rw [update?_of_view_query (M₁.seqComp M₂) hcomp direction,
          update?_of_view_query M₁ hview direction]
        rfl
      · rw [update?_of_view_query_of_ne (M₁.seqComp M₂) hcomp h,
          update?_of_view_query_of_ne M₁ hview h]
        rfl
  | inl value =>
      rw [head_eq_inl_of_view M₁ hview, Sum.elim_inl]
      cases hview₂ : M₂.view (M₂.init value) with
      | inl result =>
          rw [update?_of_view_return (M₁.seqComp M₂) (value := result)
              (by rw [seqComp_view_inl_of_return M₁ M₂ hview, hview₂]; rfl),
            update?_of_view_return M₂ hview₂]
          rfl
      | inr query₂ =>
          rcases query₂ with ⟨position₂, next₂⟩
          have hcomp : (M₁.seqComp M₂).view (Sum.inl state₁) =
              Sum.inr ⟨position₂, fun d => Sum.inr (next₂ d)⟩ := by
            rw [seqComp_view_inl_of_return M₁ M₂ hview, hview₂]; rfl
          by_cases h : position = position₂
          · subst h
            rw [update?_of_view_query (M₁.seqComp M₂) hcomp direction,
              update?_of_view_query M₂ hview₂ direction]
            rfl
          · rw [update?_of_view_query_of_ne (M₁.seqComp M₂) hcomp h,
              update?_of_view_query_of_ne M₂ hview₂ h]
            rfl

@[simp] theorem updateFlat_seqComp_inr [DecidableEq p.A]
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (state₂ : M₂.State) (index : p.Idx) :
    (M₁.seqComp M₂).updateFlat (Sum.inr state₂, index) =
      Sum.inr (M₂.updateFlat (state₂, index)) := by
  unfold updateFlat
  rw [update?_seqComp_inr]
  cases M₂.update? (state₂, index) <;> rfl

/-- At a left state exposing a query, the composite advances `M₁` inside the left
summand. -/
theorem updateFlat_seqComp_inl_of_query [DecidableEq p.A]
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    {state₁ : M₁.State} {position₁ : p.A} {next₁ : p.B position₁ → M₁.State}
    (hview : M₁.view state₁ = Sum.inr ⟨position₁, next₁⟩) (index : p.Idx) :
    (M₁.seqComp M₂).updateFlat (Sum.inl state₁, index) =
      Sum.inl (M₁.updateFlat (state₁, index)) := by
  unfold updateFlat
  rw [update?_seqComp_inl, head_eq_inr_of_view M₁ hview, Sum.elim_inr]
  cases M₁.update? (state₁, index) <;> rfl

end SeqComp

/-! ## Faithfulness of the flat presentation

The flat step maps lose nothing: a step function is determined by the readout and
the partial transition it induces. So presenting a computation by
`(State, init, head, update?)` is a genuine presentation rather than a lossy
projection — which is why constraining those three maps is the right notion of an
admissible machine.
-/

/-- A step function is determined by the readout and the partial transition it
induces. -/
theorem ofStep_step_eq_of_flat_eq [DecidableEq p.A] {S : Type u}
    (step₁ step₂ : S → β ⊕ p.Obj S) (init : α → S)
    (hhead : ∀ state, (ofStep (p := p) step₁ init).head state =
      (ofStep (p := p) step₂ init).head state)
    (hupdate : ∀ pair, (ofStep (p := p) step₁ init).update? pair =
      (ofStep (p := p) step₂ init).update? pair) :
    step₁ = step₂ := by
  funext state
  have hview₁ : (ofStep (p := p) step₁ init).view state = step₁ state :=
    view_ofStep step₁ init state
  have hview₂ : (ofStep (p := p) step₂ init).view state = step₂ state :=
    view_ofStep step₂ init state
  have hpos := hhead state
  rw [head_eq_sumMap_view, head_eq_sumMap_view, hview₁, hview₂] at hpos
  cases h₁ : step₁ state with
  | inl value₁ =>
      cases h₂ : step₂ state with
      | inl value₂ =>
          rw [h₁, h₂] at hpos
          change Sum.inl value₁ = Sum.inl value₂ at hpos
          rw [Sum.inl.inj hpos]
      | inr query₂ =>
          rw [h₁, h₂] at hpos
          change Sum.inl value₁ = Sum.inr query₂.1 at hpos
          exact absurd hpos (by simp)
  | inr query₁ =>
      cases h₂ : step₂ state with
      | inl value₂ =>
          rw [h₁, h₂] at hpos
          change Sum.inr query₁.1 = Sum.inl value₂ at hpos
          exact absurd hpos (by simp)
      | inr query₂ =>
          rcases query₁ with ⟨position₁, next₁⟩
          rcases query₂ with ⟨position₂, next₂⟩
          have hposEq : position₁ = position₂ := by
            rw [h₁, h₂] at hpos
            change Sum.inr position₁ = Sum.inr position₂ at hpos
            exact Sum.inr.inj hpos
          subst hposEq
          refine congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (funext fun d => ?_)))
          have := hupdate (state, ⟨position₁, d⟩)
          rw [update?_of_view_query _ (hview₁.trans h₁) d,
            update?_of_view_query _ (hview₂.trans h₂) d] at this
          exact Option.some.inj this

end DynSystem.DynComputation

end PFunctor
