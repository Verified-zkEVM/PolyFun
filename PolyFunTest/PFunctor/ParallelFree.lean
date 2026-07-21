/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Parallel.Free
public import PolyFun.PFunctor.Display.Parallel.Lens

/-!
# Regression tests for parallel lenses, free programs, and handlers

The canaries observe all three branches of componentwise lens maps, the
residual one-sided phases of free parallel execution, displayed free-program
composition, and the identity/coherence interfaces used downstream.
-/

@[expose] public section

namespace PFunctor.ParallelFreeCanary

abbrev P : PFunctor.{0, 0} := ⟨Bool, fun _ => Bool⟩

abbrev Q : PFunctor.{0, 0} := ⟨PUnit, fun _ => Nat⟩

abbrev flipLens : Lens P P where
  toFunA operation := !operation
  toFunB _ answer := !answer

abbrev succLens : Lens Q Q where
  toFunA _ := PUnit.unit
  toFunB _ answer := answer + 1

example : (Lens.parallelSumMap flipLens succLens).toFunA (.left true) =
    .left false :=
  rfl

example : (Lens.parallelSumMap flipLens succLens).toFunA (.right PUnit.unit) =
    .right PUnit.unit :=
  rfl

example : (Lens.parallelSumMap flipLens succLens).toFunB
    (.left true) false = true :=
  rfl

def mappedRightAnswer :
    (P ∥ Q).B ((Lens.parallelSumMap flipLens succLens).toFunA
      (.right PUnit.unit)) := by
  change Nat
  exact 4

def sourceRightAnswer : (P ∥ Q).B (.right PUnit.unit) := by
  change Nat
  exact 5

example : (Lens.parallelSumMap flipLens succLens).toFunB
    (.right PUnit.unit) mappedRightAnswer = sourceRightAnswer :=
  rfl

example : (Lens.parallelSumMap flipLens succLens).toFunB
    (.both true PUnit.unit) (false, 4) = (true, 5) :=
  rfl

def leftProgram : FreeM P Bool :=
  FreeM.liftBind true FreeM.pure

def rightProgram : FreeM Q Nat :=
  FreeM.liftBind PUnit.unit FreeM.pure

example : FreeM.parallel (FreeM.pure true : FreeM P Bool)
    (FreeM.pure 3 : FreeM Q Nat) = FreeM.pure (true, 3) :=
  rfl

example : FreeM.parallel leftProgram (FreeM.pure 3) =
    (FreeM.liftBind (ParallelChoice.left (B := Q.A) true)
      (fun answer => FreeM.pure (answer, 3)) :
        FreeM (P ∥ Q) (Bool × Nat)) :=
  rfl

example : FreeM.parallel (FreeM.pure true) rightProgram =
    (FreeM.liftBind (ParallelChoice.right (A := P.A) PUnit.unit)
      (fun answer => FreeM.pure (true, answer)) :
        FreeM (P ∥ Q) (Bool × Nat)) :=
  rfl

example : FreeM.parallel leftProgram rightProgram =
    (FreeM.liftBind (ParallelChoice.both true PUnit.unit)
      (fun answer => FreeM.pure answer) :
        FreeM (P ∥ Q) (Bool × Nat)) :=
  rfl

def twoStepLeft : FreeM P Bool :=
  FreeM.liftBind true fun _ => FreeM.liftBind false FreeM.pure

/-- After the initial joint operation, the remaining left operation becomes a
left-only step because the right program has already returned. -/
example : FreeM.parallel twoStepLeft rightProgram =
    (FreeM.liftBind (ParallelChoice.both true PUnit.unit) fun answer =>
      FreeM.liftBind (ParallelChoice.left (B := Q.A) false) fun nextAnswer =>
        FreeM.pure (nextAnswer, answer.2) :
      FreeM (P ∥ Q) (Bool × Nat)) :=
  rfl

abbrev pDisplay : Display P where
  position _ := PUnit
  direction _ _ _ := PUnit

abbrev qDisplay : Display Q where
  position _ := PUnit
  direction _ _ _ := PUnit

abbrev flippedDisplayLens : Display.Lens pDisplay pDisplay flipLens where
  toPosition _ _ := PUnit.unit
  toDirection _ _ _ _ := PUnit.unit

abbrev successorDisplayLens : Display.Lens qDisplay qDisplay succLens where
  toPosition _ _ := PUnit.unit
  toDirection _ _ _ _ := PUnit.unit

example :
    (Display.Lens.parallelSumMap flippedDisplayLens successorDisplayLens).toPosition
        (.both true PUnit.unit) (PUnit.unit, PUnit.unit) =
        (PUnit.unit, PUnit.unit) :=
  rfl

abbrev observedPDisplay : Display P where
  position _ := Bool
  direction _ _ _ := Bool

abbrev observedQDisplay : Display Q where
  position _ := String
  direction _ _ _ := Nat

abbrev observedFlip :
    Display.Lens observedPDisplay observedPDisplay flipLens where
  toPosition _ contract := !contract
  toDirection _ _ _ direction := !direction

abbrev observedSucc :
    Display.Lens observedQDisplay observedQDisplay succLens where
  toPosition _ contract := contract ++ "!"
  toDirection _ _ _ direction := direction + 1

def observedMap := Display.Lens.parallelSumMap observedFlip observedSucc

example : observedMap.toPosition (.left true) (ULift.up false) =
    ULift.up true :=
  rfl

example : observedMap.toPosition (.right PUnit.unit) (ULift.up "q") =
    ULift.up "q!" :=
  rfl

example : observedMap.toPosition (.both true PUnit.unit) (false, "q") =
    (true, "q!") :=
  rfl

example : observedMap.toDirection (.left true) (ULift.up false)
    false (ULift.up true) = ULift.up false :=
  rfl

example : observedMap.toDirection (.right PUnit.unit) (ULift.up "q")
    mappedRightAnswer (ULift.up 2) = ULift.up 3 :=
  rfl

example : observedMap.toDirection (.both true PUnit.unit) (false, "q")
    (false, 4) (true, 2) = (false, 3) :=
  rfl

def observedLeftProgram :
    FreeM.Displayed
      (observedPDisplay.toDisplayedAlgebra (fun _ => Bool)) leftProgram :=
  ⟨false, fun answer evidence =>
    observedPDisplay.leaf _ answer (!evidence)⟩

def observedRightProgram :
    FreeM.Displayed
      (observedQDisplay.toDisplayedAlgebra (fun _ => Nat)) rightProgram :=
  ⟨"q", fun answer evidence =>
    observedQDisplay.leaf _ answer (answer + evidence)⟩

def observedParallelProgram :
    FreeM.Displayed
      ((Display.parallelSum observedPDisplay observedQDisplay).toDisplayedAlgebra
        (fun _ => Bool × Nat))
      (FreeM.parallel leftProgram rightProgram) :=
  FreeM.Displayed.parallel leftProgram rightProgram
    observedLeftProgram observedRightProgram

example : observedParallelProgram.1 = (false, "q") :=
  rfl

example : (observedParallelProgram.2 (true, 4) (false, 2)).down.1 = true :=
  rfl

example : (observedParallelProgram.2 (true, 4) (false, 2)).down.2 = 6 :=
  rfl

def displayedLeftProgram :
    FreeM.Displayed
      (pDisplay.toDisplayedAlgebra (fun _ => PUnit)) leftProgram :=
  ⟨PUnit.unit, fun answer _ => pDisplay.leaf _ answer PUnit.unit⟩

def displayedRightProgram :
    FreeM.Displayed
      (qDisplay.toDisplayedAlgebra (fun _ => PUnit)) rightProgram :=
  ⟨PUnit.unit, fun answer _ => qDisplay.leaf _ answer PUnit.unit⟩

def displayedParallelProgram :
    FreeM.Displayed
      ((Display.parallelSum pDisplay qDisplay).toDisplayedAlgebra
        (fun _ => PUnit × PUnit))
      (FreeM.parallel leftProgram rightProgram) :=
  FreeM.Displayed.parallel leftProgram rightProgram
    displayedLeftProgram displayedRightProgram

example : Handler.parallel (Handler.id P) (Handler.id Q) =
    Handler.id (P ∥ Q) :=
  Handler.parallel_id P Q

example :
    Display.Handler.transport (Handler.parallel_id P Q)
        (Display.Handler.parallel (Display.Handler.id pDisplay)
          (Display.Handler.id qDisplay)) =
      Display.Handler.id (Display.parallelSum pDisplay qDisplay) :=
  Display.Handler.parallel_id pDisplay qDisplay

universe uA₁ uA₂ uA₃ uA₄ uA₅ uA₆ uB
  uC₁ uD₁ uC₂ uD₂ uE uF uI uJ

def heterogeneousDisplayedParallel
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {E : Type uE} {F : Type uF} {I : E → Type uI} {J : F → Type uJ}
    (left : FreeM P E) (right : FreeM Q F)
    (displayedLeft : FreeM.Displayed (S.toDisplayedAlgebra I) left)
    (displayedRight : FreeM.Displayed (T.toDisplayedAlgebra J) right) :=
  FreeM.Displayed.parallel left right displayedLeft displayedRight

theorem lensMapComp
    {P₁ : PFunctor.{uA₁, uB}} {Q₁ : PFunctor.{uA₂, uB}}
    {P₂ : PFunctor.{uA₃, uB}} {Q₂ : PFunctor.{uA₄, uB}}
    {P₃ : PFunctor.{uA₅, uB}} {Q₃ : PFunctor.{uA₆, uB}}
    (firstLeft : Lens P₁ P₂) (firstRight : Lens Q₁ Q₂)
    (secondLeft : Lens P₂ P₃) (secondRight : Lens Q₂ Q₃) :
    Lens.parallelSumMap secondLeft secondRight ∘ₗ
        Lens.parallelSumMap firstLeft firstRight =
      Lens.parallelSumMap (secondLeft ∘ₗ firstLeft)
        (secondRight ∘ₗ firstRight) :=
  Lens.parallelSumMap_comp secondLeft secondRight firstLeft firstRight

abbrev Step : PFunctor.{0, 0} := ⟨Bool, fun _ => PUnit⟩

def firstLeft : Handler (FreeM Step) Step := fun _ =>
  FreeM.liftBind false fun _ => FreeM.liftBind true FreeM.pure

def firstRight : Handler (FreeM Step) Step := fun _ => FreeM.lift false

def secondLeft : Handler (FreeM Step) Step
  | false => FreeM.pure PUnit.unit
  | true => FreeM.lift true

def secondRight : Handler (FreeM Step) Step := fun _ => FreeM.lift false

def rootOperation {E : Type} : FreeM (Step ∥ Step) E →
    Option (ParallelChoice Bool Bool)
  | .pure _ => none
  | .liftBind operation _ => some operation

example :
    rootOperation
      ((Handler.parallel secondLeft secondRight).comp
        (Handler.parallel firstLeft firstRight) (.both false false)) =
      some (.right false) :=
  rfl

example :
    rootOperation
      (Handler.parallel (secondLeft.comp firstLeft)
        (secondRight.comp firstRight) (.both false false)) =
      some (.both true false) :=
  rfl

theorem handler_parallel_comp_fails :
    (Handler.parallel secondLeft secondRight).comp
        (Handler.parallel firstLeft firstRight) ≠
      Handler.parallel (secondLeft.comp firstLeft)
        (secondRight.comp firstRight) := by
  intro equality
  have rootEquality := congrArg rootOperation
    (congrFun equality (ParallelChoice.both false false))
  cases rootEquality

end PFunctor.ParallelFreeCanary
