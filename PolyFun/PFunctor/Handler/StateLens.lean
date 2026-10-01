/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Stateful
public import PolyFun.PFunctor.Free.Resumption

/-!
# Stateful lenses: one-query stateful handlers

A `StateLens p r σ` is a stateful handler that answers every outer `p`-query with exactly one inner
`r`-query. At handler state `s`, the outer query `x` is forwarded as `pos (x, s)`, and the inner
answer `e` determines the outer answer `answer (x, s) e` and the next handler state
`update (x, s) e`. Its data is exactly that of a lens from the tensor of `p` with the state monomial
`σy^σ` to `r`. (`Lens.State`, a get/put lens on states, is unrelated.)

Forwarding, logging, counting and relabelling handlers have this shape. A handler that may answer
without an inner query, such as a cache hit, or with several does not.

## Main definitions and results

* `StateLens.mapFreeM` and `StateLens.mapResumption`: stateful substitution on programs and
  resumptions, related by `toResumption_mapFreeM`.
* `StateLens.toStateful` and `mapFreeM_eq_run`: substitution along a stateful lens is
  `Handler.Stateful.run` of its handler.
* `StateLens.pullHead`: the partial pullback of a tagged inner answer, which machines running
  against the lens use to resume.
-/

@[expose] public section

universe u

namespace PFunctor

/-- A stateful lens: a handler for the outer interface `p` that forwards every query as one query
of the inner interface `r`, threading a handler state `σ`. -/
structure StateLens (p r : PFunctor.{u, u}) (σ : Type u) where
  /-- The inner query issued for an outer query at a handler state. -/
  pos : p.A × σ → r.A
  /-- The outer answer determined by an inner answer. -/
  answer : (query : p.A × σ) → r.B (pos query) → p.B query.1
  /-- The handler state after an inner answer. -/
  update : (query : p.A × σ) → r.B (pos query) → σ

namespace StateLens

variable {p r : PFunctor.{u, u}} {σ : Type u}

/-- Stateful substitution of a free program along a stateful lens. -/
def mapFreeM (L : StateLens p r σ) {β : Type u} : FreeM p β → σ → FreeM r (β × σ)
  | .pure value, state => .pure (value, state)
  | .liftBind position next, state =>
      .liftBind (L.pos (position, state)) fun answer ↦
        L.mapFreeM (next (L.answer (position, state) answer)) (L.update (position, state) answer)

/-- The one-step coalgebra of stateful substitution on resumptions. -/
def mapStep (L : StateLens p r σ) {β : Type u} (x : Resumption p β × σ) :
    (β × σ) ⊕ r.Obj (Resumption p β × σ) :=
  Sum.elim (fun value ↦ Sum.inl (value, x.2))
    (fun query ↦ Sum.inr ⟨L.pos (query.1, x.2), fun answer ↦
      (query.2 (L.answer (query.1, x.2) answer), L.update (query.1, x.2) answer)⟩)
    (Resumption.dest x.1)

/-- Stateful substitution of a resumption along a stateful lens. -/
def mapResumption (L : StateLens p r σ) {β : Type u} (computation : Resumption p β)
    (state : σ) : Resumption r (β × σ) :=
  Resumption.corec L.mapStep (computation, state)

/-- Stateful substitution commutes with the embedding of free programs into resumptions. -/
theorem toResumption_mapFreeM (L : StateLens p r σ) {β : Type u} (program : FreeM p β)
    (state : σ) :
    FreeM.toResumption (L.mapFreeM program state) =
      L.mapResumption (FreeM.toResumption program) state := by
  induction program generalizing state with
  | pure value =>
      apply Resumption.eq_of_dest_eq
      rw [mapResumption, Resumption.dest_corec]
      rfl
  | lift_bind position next ih =>
      change FreeM.toResumption (L.mapFreeM (FreeM.liftBind position next) state) =
        L.mapResumption (FreeM.toResumption (FreeM.liftBind position next)) state
      apply Resumption.eq_of_dest_eq
      rw [mapResumption, Resumption.dest_corec, mapFreeM, FreeM.dest_toResumption_liftBind]
      simp only [mapStep, FreeM.dest_toResumption_liftBind, Sum.elim_inr, Sum.map_inr]
      congr 1
      refine Sigma.ext rfl (heq_of_eq (funext fun answer ↦ ?_))
      exact ih _ _

/-- A stateful lens as a stateful handler into free programs: one inner query per outer query. -/
def toStateful (L : StateLens p r σ) : Handler.Stateful (FreeM r) σ p := fun position state ↦
  FreeM.liftBind (L.pos (position, state)) fun answer ↦
    FreeM.pure (L.answer (position, state) answer, L.update (position, state) answer)

/-- Stateful substitution along a stateful lens is `Handler.Stateful.run` of its handler. -/
theorem mapFreeM_eq_run (L : StateLens p r σ) {β : Type u} (program : FreeM p β) (state : σ) :
    L.mapFreeM program state = L.toStateful.run program state := by
  induction program generalizing state with
  | pure value => rfl
  | lift_bind position next ih =>
      change L.mapFreeM (FreeM.liftBind position next) state =
        L.toStateful.run (FreeM.liftBind position next) state
      rw [Handler.Stateful.run_liftBind]
      change _ = FreeM.bind (FreeM.liftBind _ _) _
      simp only [mapFreeM, FreeM.bind]
      congr 1
      funext answer
      exact ih _ _

/-- The partial pullback of an inner answer, absorbing the returned case. Given the outer
machine's readout, the handler state and a tagged inner answer, it recovers the tagged outer
answer and the next handler state, or `none` if the answer is not one the handler is waiting
for. -/
def pullHead [DecidableEq r.A] (L : StateLens p r σ) (β : Type u) :
    ((β ⊕ p.A) × σ) × r.Idx → Option (p.Idx × σ) := fun x ↦
  x.1.1.elim (fun _ ↦ none) fun position ↦
    if h : x.2.1 = L.pos (position, x.1.2) then
      some (⟨position, L.answer (position, x.1.2) (h ▸ x.2.2)⟩,
        L.update (position, x.1.2) (h ▸ x.2.2))
    else none

end StateLens

end PFunctor
