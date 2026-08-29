/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.BoundedFold

/-!
# Direct canaries for bounded interaction folds

The examples distinguish the generated two-query syntax and verify that the
generic countdown-state machine supplies its public bounded-implementation proof.
-/

@[expose] public section

namespace PFunctor.DynSystem.DynComputation

/-- A Boolean-position, Boolean-answer test interface. -/
abbrev boolInterface : PFunctor := PFunctor.mk Bool fun _ ↦ Bool

example : boundedFoldProgram (p := boolInterface) false
    (fun accumulator _ answer ↦ accumulator != answer) id 2 false =
    FreeM.liftBind false fun first =>
      FreeM.liftBind false fun second =>
        FreeM.pure ((false != first) != second) := rfl

example : boundedFoldProgram (p := boolInterface) false
    (fun visited round _answer ↦ visited ++ [round]) id 2 [] =
    FreeM.liftBind false fun _first ↦
      FreeM.liftBind false fun _second ↦
        FreeM.pure [1, 0] := rfl

example :
    (boundedFold (p := boolInterface) false
      (fun accumulator _ answer ↦ accumulator != answer) id 2).ImplementsWithin
      (fun initial => boundedFoldProgram false
        (fun accumulator _ answer ↦ accumulator != answer) id 2 initial) 2 :=
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
    (boundedFoldProgram (p := emptyInterface) PUnit.unit
      (fun _accumulator _ answer ↦ answer.elim) id 2 false).IsTotalRollBound 1 := by
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
      (fun initial ↦ boundedFoldProgram false
        largeStep largeReadout 1 initial) 1 :=
  implementsWithin_boundedFold (p := largeAnswerInterface) false
    largeStep largeReadout 1

end PFunctor.DynSystem.DynComputation
