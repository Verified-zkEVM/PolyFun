/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Handler.StateLens

/-!
# Stateful lens compatibility

Ordinary-import canaries for old receiver types, constructor binders, patterns and unfolding.
-/

@[expose] public section

set_option linter.deprecated false

universe u

namespace PFunctor.StateLens.Compatibility

variable {p r : PFunctor.{u, u}} {σ β : Type u} (L : StateLens p r σ)

-- Old receiver types support all three projections in record construction.
example : StateLens p r σ where
  pos := L.pos
  answer := L.answer
  update := L.update

-- Constructor field names and their order remain available through the old namespace.
example : StateLens p r σ :=
  StateLens.mk (pos := L.pos) (answer := L.answer) (update := L.update)

example :
    (match (StateLens.mk L.pos L.answer L.update : StateLens p r σ) with
    | StateLens.mk pos _ _ => pos) = L.pos := rfl

example :
    (match L with
    | ⟨pos, _, _⟩ => pos) = L.pos := rfl

-- Old method receivers retain their named arguments and explicit unfolding surface.
example (program : FreeM p β) (state : σ) :
    L.mapFreeM program state = StatefulLens.mapFreeM L program state := by
  unfold StateLens.mapFreeM
  rfl

example (computation : Resumption p β) (state : σ) :
    Resumption r (β × σ) :=
  L.mapResumption (computation := computation) (state := state)

example (x : Resumption p β × σ) : (β × σ) ⊕ r.Obj (Resumption p β × σ) :=
  L.mapStep (x := x)

example : Handler.Stateful (FreeM r) σ p := L.toStateful

example [DecidableEq r.A] : ((β ⊕ p.A) × σ) × r.Idx → Option (p.Idx × σ) :=
  L.pullHead (β := β)

-- The theorem receiver must also use the old type for generalized field notation.
example (program : FreeM p β) (state : σ) :
    FreeM.toResumption (L.mapFreeM program state) =
      L.mapResumption (FreeM.toResumption program) state :=
  L.toResumption_mapFreeM (program := program) (state := state)

example (program : FreeM p β) (state : σ) :
    L.mapFreeM program state = L.toStateful.run program state :=
  L.mapFreeM_eq_run (program := program) (state := state)

end PFunctor.StateLens.Compatibility
