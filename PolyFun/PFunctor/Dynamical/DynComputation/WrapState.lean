/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation
public import PolyFun.PFunctor.Handler.StateLens

/-!
# Running a computation against a stateful lens

`DynComputation.wrapState M L` runs `M` against a stateful lens `L : StateLens p r σ` as one
product machine:
- the hidden state is `M.State × σ`;
- every outer query of `M` becomes exactly one inner query, so the visible query count is `M`'s;
- the final handler state is returned alongside the result.

It extends `DynComputation.wrap`, a stateless lens, to persistent handler state. Its denotation is
stateful substitution of `M`'s denotation (`denote_wrapState`), and it implements
`Handler.Stateful.run` of the lens's handler (`Implements.wrapState_run`).
-/

@[expose] public section

universe u

namespace PFunctor.DynSystem.DynComputation

variable {p r : PFunctor.{u, u}} {σ α β : Type u}

/-- Run a returning computation against a stateful lens: the hidden state pairs the computation's
state with the handler state, each outer query becomes one inner query, and the final handler
state is returned alongside the result. -/
abbrev wrapState (M : DynComputation.{u} p α β) (L : StateLens p r σ) :
    DynComputation.{u} r (α × σ) (β × σ) :=
  ofStep (S := M.State × σ)
    (fun state ↦ Sum.elim (fun value ↦ Sum.inl (value, state.2))
      (fun query ↦ Sum.inr ⟨L.pos (query.1, state.2), fun answer ↦
        (query.2 (L.answer (query.1, state.2) answer), L.update (query.1, state.2) answer)⟩)
      (M.view state.1))
    (fun input ↦ (M.init input.1, input.2))

theorem view_wrapState_of_return (M : DynComputation.{u} p α β) (L : StateLens p r σ)
    {state : M.State × σ} {value : β} (h : M.view state.1 = Sum.inl value) :
    (M.wrapState L).view state = Sum.inl (value, state.2) := by
  rw [view_ofStep, h]; rfl

theorem view_wrapState_of_query (M : DynComputation.{u} p α β) (L : StateLens p r σ)
    {state : M.State × σ} {position : p.A} {next : p.B position → M.State}
    (h : M.view state.1 = Sum.inr ⟨position, next⟩) :
    (M.wrapState L).view state = Sum.inr ⟨L.pos (position, state.2), fun answer ↦
      (next (L.answer (position, state.2) answer), L.update (position, state.2) answer)⟩ := by
  rw [view_ofStep, h]; rfl

/-- A query exposed by the product machine is the lens image of a query of `M`. -/
theorem exists_view_eq_query_of_wrapState (M : DynComputation.{u} p α β)
    (L : StateLens p r σ) {state : M.State × σ} {position : r.A}
    {next : r.B position → M.State × σ}
    (h : (M.wrapState L).view state = Sum.inr ⟨position, next⟩) :
    ∃ (source : p.A) (sourceNext : p.B source → M.State),
      M.view state.1 = Sum.inr ⟨source, sourceNext⟩ ∧
        (⟨position, next⟩ : r.Obj (M.State × σ)) =
          ⟨L.pos (source, state.2), fun answer ↦ (sourceNext (L.answer (source, state.2) answer),
            L.update (source, state.2) answer)⟩ := by
  rcases hview : M.view state.1 with value | ⟨source, sourceNext⟩
  · rw [view_wrapState_of_return M L hview] at h
    exact nomatch h
  · rw [view_wrapState_of_query M L hview] at h
    exact ⟨source, sourceNext, rfl, (Sum.inr.inj h).symm⟩

/-- The product machine returns exactly when `M` does, with the current handler state. -/
theorem view_eq_return_of_wrapState (M : DynComputation.{u} p α β) (L : StateLens p r σ)
    {state : M.State × σ} {result : β × σ}
    (h : (M.wrapState L).view state = Sum.inl result) :
    M.view state.1 = Sum.inl result.1 ∧ result.2 = state.2 := by
  rcases hview : M.view state.1 with value | ⟨source, sourceNext⟩
  · rw [view_wrapState_of_return M L hview] at h
    cases Sum.inl.inj h
    exact ⟨rfl, rfl⟩
  · rw [view_wrapState_of_query M L hview] at h
    exact nomatch h

/-- State-level semantics: the product machine performs stateful substitution of `M`'s
behavior. -/
theorem behavior_wrapState (M : DynComputation.{u} p α β) (L : StateLens p r σ)
    (state : M.State × σ) :
    (M.wrapState L).toDynSystem.behavior state =
      L.mapResumption (M.toDynSystem.behavior state.1) state.2 := by
  have h₁ : (M.wrapState L).toDynSystem.behavior = Resumption.corec (M.wrapState L).view :=
    Resumption.corec_unique _ _ (dest_behavior_view (M.wrapState L))
  have h₂ : (fun state : M.State × σ ↦
      L.mapResumption (M.toDynSystem.behavior state.1) state.2) =
        Resumption.corec (M.wrapState L).view := by
    apply Resumption.corec_unique
    intro state
    rw [StateLens.mapResumption, Resumption.dest_corec]
    simp only [StateLens.mapStep, dest_behavior_view]
    rcases hview : M.view state.1 with value | ⟨position, next⟩
    · rw [view_wrapState_of_return M L hview]; rfl
    · rw [view_wrapState_of_query M L hview]; rfl
  exact congrFun (h₁.trans h₂.symm) state

/-- The product machine denotes stateful substitution of `M`'s denotation. -/
@[simp] theorem denote_wrapState (M : DynComputation.{u} p α β) (L : StateLens p r σ)
    (input : α × σ) :
    (M.wrapState L).denote input = L.mapResumption (M.denote input.1) input.2 :=
  behavior_wrapState M L (M.init input.1, input.2)

/-- Running against a stateful lens transports implementation to stateful substitution. -/
theorem Implements.wrapState {M : DynComputation.{u} p α β} {program : α → FreeM p β}
    (h : M.Implements program) (L : StateLens p r σ) :
    (M.wrapState L).Implements fun input ↦ L.mapFreeM (program input.1) input.2 := by
  intro input
  rw [denote_wrapState, h input.1, StateLens.toResumption_mapFreeM]

/-- The product machine implements `Handler.Stateful.run` of the lens's stateful handler. -/
theorem Implements.wrapState_run {M : DynComputation.{u} p α β} {program : α → FreeM p β}
    (h : M.Implements program) (L : StateLens p r σ) :
    (M.wrapState L).Implements fun input ↦ L.toStateful.run (program input.1) input.2 := by
  intro input
  change (M.wrapState L).denote input =
    FreeM.toResumption (L.toStateful.run (program input.1) input.2)
  rw [← StateLens.mapFreeM_eq_run]
  exact h.wrapState L input

end PFunctor.DynSystem.DynComputation
