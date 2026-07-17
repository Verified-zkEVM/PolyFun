/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Free.Cursor
public import PolyFun.PFunctor.Trace

/-! # Producer tests for dependent trace and free-tree root predicates -/

@[expose] public section

universe uA uB v

namespace PFunctor.PredicateExamples

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- The trace predicate accepts genuinely dependent direction fibers without
requiring decidable equality on positions. -/
example (allowed : (a : P.A) → Set (P.B a)) (a : P.A) (b : P.B a)
    (tail : TraceList P) :
    TraceList.DirectionsWithin allowed (⟨a, b⟩ :: tail) ↔
      b ∈ allowed a ∧ TraceList.DirectionsWithin allowed tail := by
  simp

/-- Root satisfaction distinguishes leaves from exposed positions. -/
example (positionPred : P.A → Prop) (leafPred : α → Prop) (result : α) :
    FreeM.RootSatisfies positionPred leafPred (pure result : FreeM P α) =
      leafPred result := rfl

example (positionPred : P.A → Prop) (leafPred : α → Prop)
    (position : P.A) (next : P.B position → FreeM P α) :
    FreeM.RootSatisfies positionPred leafPred
        ((FreeM.lift (P := P) position).bind next) =
      positionPred position := rfl

/-- A cursor descent changes the selected residual but introduces no separate
cursor-level satisfaction semantics. -/
example (positionPred : P.A → Prop) (leafPred : α → Prop)
    {position : P.A} {next : P.B position → FreeM P α}
    (direction : P.B position) (tail : FreeM.Cursor (next direction)) :
    FreeM.RootSatisfies positionPred leafPred
        (FreeM.Cursor.down direction tail).residual ↔
      FreeM.RootSatisfies positionPred leafPred tail.residual := by
  simp

end PFunctor.PredicateExamples
