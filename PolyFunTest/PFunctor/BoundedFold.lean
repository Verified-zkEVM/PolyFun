/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.BoundedFold

/-!
# Direct canaries for bounded realizations of free-monad folds

The examples distinguish the generated two-query syntax and verify that the
countdown-state machine realizes the corresponding `FreeM.foldr` program.
-/

@[expose] public section

namespace PFunctor.DynSystem.DynComputation

/-- A Boolean-position, Boolean-answer test interface. -/
abbrev boolInterface : PFunctor := PFunctor.mk Bool fun _ ↦ Bool

example : FreeM.foldr (P := boolInterface) false
    (fun accumulator _round answer ↦ accumulator != answer) id 2 false =
    (FreeM.lift false).bind fun first =>
      (FreeM.lift false).bind fun second =>
        pure ((false != first) != second) := by
  simp

example : FreeM.foldr (P := boolInterface) false
    (fun visited round _answer ↦ visited ++ [round]) id 2 [] =
    (FreeM.lift false).bind fun _first ↦
      (FreeM.lift false).bind fun _second ↦
        pure [1, 0] := by
  simp

example :
    (boundedFold (p := boolInterface) false
      (fun accumulator _ answer ↦ accumulator != answer) id 2).ImplementsWithin
      (fun initial =>
        FreeM.foldr false
          (fun accumulator _round answer ↦ accumulator != answer)
          id 2 initial) 2 :=
  implementsWithin_boundedFold (p := boolInterface) false
    (fun accumulator _ answer ↦ accumulator != answer) id 2

example :
    (boundedFold (p := boolInterface) false
      (fun visited round _answer ↦ visited ++ [round]) id 2).view
        (⟨0, by omega⟩, []) = Sum.inl [] :=
  view_boundedFold_zero (p := boolInterface) false
    (fun visited round _answer ↦ visited ++ [round]) id 2 rfl

example :
    (boundedFold (p := boolInterface) false
      (fun visited round _answer ↦ visited ++ [round]) id 2).view
        (⟨2, by omega⟩, []) =
      Sum.inr ⟨false, fun _answer ↦ (⟨1, by omega⟩, [1])⟩ :=
  view_boundedFold_succ (p := boolInterface) false
    (fun visited round _answer ↦ visited ++ [round]) id 2 (by decide)

/-! The upper bound is deliberately not advertised as minimal: an empty answer
type makes later rounds unreachable. -/

abbrev emptyInterface : PFunctor := PFunctor.mk PUnit fun _ ↦ PEmpty

example :
    (FreeM.foldr (P := emptyInterface) PUnit.unit
      (fun _accumulator _round answer ↦ answer.elim) id 2 false).IsTotalRollBound 1 := by
  rw [FreeM.foldr_succ]
  exact ⟨Nat.succ_pos 0, fun answer ↦ nomatch answer⟩

/-! Universe separation canary: positions/results remain small while answers
and accumulator states live one universe higher. -/

abbrev largeAnswerInterface : PFunctor.{0, 1} :=
  PFunctor.mk Bool fun _ ↦ ULift Bool

def largeStep (state : ULift.{1, 0} Bool) (_round : ℕ)
    (answer : ULift.{1, 0} Bool) : ULift.{1, 0} Bool :=
  ULift.up (state.down != answer.down)

def largeReadout (state : ULift.{1, 0} Bool) : Bool := state.down

example :
    (boundedFold (p := largeAnswerInterface) false
      largeStep largeReadout 1).ImplementsWithin
      (fun initial ↦
        FreeM.foldr false largeStep largeReadout 1 initial) 1 :=
  implementsWithin_boundedFold (p := largeAnswerInterface) false
    largeStep largeReadout 1

end PFunctor.DynSystem.DynComputation
