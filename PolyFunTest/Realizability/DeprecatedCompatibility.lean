/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Realizability.Quantitative.Handler

/-!
# Quantitative stateful lens compatibility

Ordinary-import canaries for the old certificate receiver, constructor binders and patterns.
The backend, code and size universes remain independent.
-/

@[expose] public section

set_option linter.deprecated false

universe u v w

namespace PFunctor.StateLens.Compatibility

open DynSystem.DynComputation

variable {p r : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [P : C.HasProd] [S : C.HasSum] [O : C.HasOption] [DecidableEq r.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {A B σ : Type u}
  {bd : Boundary C p A B} {stateRep : C.Str σ} {posRep : C.Str r.A}
  {idxRep : C.Str r.Idx} {L : StateLens p r σ}

-- Explicit universe arguments retain the old arity and order.
example (hL : StateLens.QuantitativelyAdmissible.{u, v, w} Q bd stateRep posRep idxRep L) :
    StatefulLens.QuantitativelyAdmissible.{u, v, w} Q bd stateRep posRep idxRep L := hL

-- Both the lens and its quantitative evidence support old-typed field notation.
example (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) :
    Q.Realizer (P.prod bd.pos stateRep) posRep L.pos := hL.onPos

example (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) :
    Q.Realizer (P.prod (P.prod bd.head stateRep) idxRep)
      (O.option (P.prod bd.idx stateRep)) (L.pullHead B) := hL.onPull

-- Named constructor arguments and record fields keep their original spellings.
example (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) :
    L.QuantitativelyAdmissible Q bd stateRep posRep idxRep :=
  StateLens.QuantitativelyAdmissible.mk (onPos := hL.onPos) (onPull := hL.onPull)

example (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) :
    L.QuantitativelyAdmissible Q bd stateRep posRep idxRep where
  onPos := hL.onPos
  onPull := hL.onPull

example (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) :
    (match (StateLens.QuantitativelyAdmissible.mk hL.onPos hL.onPull :
        L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) with
    | StateLens.QuantitativelyAdmissible.mk onPos _ => onPos) = hL.onPos := rfl

example (hL : L.QuantitativelyAdmissible Q bd stateRep posRep idxRep) :
    (match hL with
    | ⟨onPos, _⟩ => onPos) = hL.onPos := rfl

-- The cost theorem remains callable through the old lens receiver and binder names.
example (c : r.A → ℕ∞) {β : Type u} (x : FreeM p β) (state : σ) :
    FreeM.wpFold (OpSpec.charge c) (L.mapFreeM x state) (fun _ => 0) ≤
      FreeM.wpFold (OpSpec.charge fun a => ⨆ st, c (L.pos (a, st))) x (fun _ => 0) :=
  L.wpFold_charge_mapFreeM_le (c := c) (x := x) (state := state)

end PFunctor.StateLens.Compatibility
