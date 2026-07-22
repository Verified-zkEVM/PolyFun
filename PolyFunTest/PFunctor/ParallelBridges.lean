/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.PatternRunsOnMatter.Parallel
public import PolyFun.PFunctor.Wiring.Parallel

/-!
# Regression tests for parallel wiring and reconstruction bridges

The concrete wiring examples observe that the two external sigma resources
remain distinct in all three one-or-both branches.  The generic theorem pins
the Pattern-Runs-on-Matter comparison at independent component universes.
-/

@[expose] public section

namespace PFunctor.ParallelBridgesCanary

abbrev Step : PFunctor.{0, 0} := ⟨Bool, fun _ => PUnit⟩

def Boxes := PEmpty

def Arity (box : Boxes) : Type := nomatch box

def Dom (box : Boxes) : Arity box → PFunctor := nomatch box

def Cod (box : Boxes) : PFunctor := nomatch box

def Inputs := PUnit

def inputInterface (_ : Inputs) : PFunctor := Step

def implementation (box : Boxes) :
    (operation : (Cod box).A) →
      FreeM (PFunctor.sigma (Dom box)) ((Cod box).B operation) :=
  nomatch box

def inputWiring :
    Wiring Boxes Arity Dom Cod Inputs inputInterface Step :=
  .input PUnit.unit

def rootOperation {E : Type} :
    FreeM (PFunctor.sigma inputInterface ∥
      PFunctor.sigma inputInterface) E →
      Option (ParallelChoice (PFunctor.sigma inputInterface).A
        (PFunctor.sigma inputInterface).A)
  | .pure _ => none
  | .liftBind operation _ => some operation

example : rootOperation
    (Wiring.evalParallel implementation inputWiring inputWiring (.left false)) =
      some (.left ⟨PUnit.unit, false⟩) :=
  rfl

example : rootOperation
    (Wiring.evalParallel implementation inputWiring inputWiring (.right true)) =
      some (.right ⟨PUnit.unit, true⟩) :=
  rfl

example : rootOperation
    (Wiring.evalParallel implementation inputWiring inputWiring
      (.both false true)) =
      some (.both ⟨PUnit.unit, false⟩ ⟨PUnit.unit, true⟩) :=
  rfl

abbrev unaryDisplay : Display Step where
  position _ := PUnit
  direction _ _ _ := PUnit

def domDisplay (box : Boxes) :
    (port : Arity box) → Display (Dom box port) :=
  nomatch box

def codDisplay (box : Boxes) : Display (Cod box) :=
  nomatch box

def inputDisplay (_ : Inputs) : Display Step := unaryDisplay

def displayedImplementation (box : Boxes) :
    Display.Handler (codDisplay box) (Display.sigma (domDisplay box))
      (implementation box) :=
  nomatch box

def displayedInputWiring :
    Wiring.Displayed domDisplay codDisplay inputDisplay
      inputWiring unaryDisplay :=
  .input PUnit.unit

example :
    (Wiring.evalDisplayedParallel domDisplay codDisplay inputDisplay
      implementation displayedImplementation displayedInputWiring
      displayedInputWiring (.both false true)
      (PUnit.unit, PUnit.unit)).1 = (PUnit.unit, PUnit.unit) :=
  rfl

universe uA₁ uA₂ uB uS₁ uS₂

theorem reindexViaRunAgainstParallel
    {P R : PFunctor.{uA₁, uB}} {Q V : PFunctor.{uA₂, uB}}
    {LeftState : Type uS₁} {RightState : Type uS₂}
    (leftHandler : Handler (FreeM P) R)
    (rightHandler : Handler (FreeM Q) V)
    (left : Responder LeftState P) (right : Responder RightState Q) :
    Responder.reindexViaRunAgainst
        (Handler.parallel leftHandler rightHandler)
        (Responder.parallel left right) =
      Responder.parallel
        (Responder.reindexViaRunAgainst leftHandler left)
        (Responder.reindexViaRunAgainst rightHandler right) :=
  Responder.reindexViaRunAgainst_parallel
    leftHandler rightHandler left right

end PFunctor.ParallelBridgesCanary
