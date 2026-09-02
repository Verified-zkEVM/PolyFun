/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import PolyFun.PFunctor.Free.Fold

/-!
# Direct canaries for finite free-monad folds

The examples pin the traversal order and nested-query shape of `FreeM.foldl`
and `FreeM.foldr`, together with fusion of result mapping into the readout.
-/

@[expose] public section

namespace PFunctor.FreeM

/-- A Boolean-position, Boolean-answer test interface. -/
abbrev boolInterface : PFunctor := PFunctor.mk Bool fun _ ↦ Bool

example : FreeM.foldl (P := boolInterface) false
    (fun current round _answer ↦ current * 10 + round) id 3 0 =
    (FreeM.lift false).bind fun _first ↦
      (FreeM.lift false).bind fun _second ↦
        (FreeM.lift false).bind fun _third ↦ pure 12 := by
  simp

example : FreeM.foldr (P := boolInterface) false
    (fun current round _answer ↦ current * 10 + round) id 3 0 =
    (FreeM.lift false).bind fun _first ↦
      (FreeM.lift false).bind fun _second ↦
        (FreeM.lift false).bind fun _third ↦ pure 210 := by
  simp

example : FreeM.foldr (P := boolInterface) false
    (fun visited round _answer ↦ visited ++ [round]) id 2 [] =
    (FreeM.lift false).bind fun _first ↦
      (FreeM.lift false).bind fun _second ↦
        pure [1, 0] := by
  simp

example :
    FreeM.map some
      (FreeM.foldr (P := boolInterface) false
        (fun accumulator _round answer ↦ accumulator != answer) id 2 false) =
    FreeM.foldr false
      (fun accumulator _round answer ↦ accumulator != answer) some 2 false := by
  rw [FreeM.map_foldr]
  rfl

end PFunctor.FreeM
