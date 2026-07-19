/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Parallel.Free
public import PolyFun.PFunctor.Wiring

/-!
# Parallel evaluation of independent recursive wirings

Two recursive wirings can be evaluated independently and then combined by
`Handler.parallel`.  The target is deliberately
`sigma inputInterface ∥ sigma inputInterface`: the two copies make the
resource separation explicit.  Collapsing them back to one shared input would
require the affine/ownership discipline that is outside this layer.
-/

@[expose] public section

universe uBoxes uArity uInputs uA uB uC uD

namespace PFunctor
namespace Wiring

variable {Boxes : Type uBoxes} {Arity : Boxes → Type uArity}
variable {Dom : (box : Boxes) → Arity box → PFunctor.{uA, uB}}
variable {Cod : Boxes → PFunctor.{uA, uB}}
variable {Inputs : Type uInputs}
variable {inputInterface : Inputs → PFunctor.{uA, uB}}

/-- Evaluate two independent wirings and combine their handlers in parallel.
The duplicated external-input interface prevents implicit contraction. -/
def evalParallel
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    {leftOutput rightOutput : PFunctor.{uA, uB}}
    (left : Wiring Boxes Arity Dom Cod Inputs inputInterface leftOutput)
    (right : Wiring Boxes Arity Dom Cod Inputs inputInterface rightOutput) :
    Handler (FreeM
      (PFunctor.sigma inputInterface ∥ PFunctor.sigma inputInterface))
      (leftOutput ∥ rightOutput) :=
  Handler.parallel (eval implementation left) (eval implementation right)

@[simp] theorem evalParallel_left
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    {leftOutput rightOutput : PFunctor.{uA, uB}}
    (left : Wiring Boxes Arity Dom Cod Inputs inputInterface leftOutput)
    (right : Wiring Boxes Arity Dom Cod Inputs inputInterface rightOutput)
    (operation : leftOutput.A) :
    evalParallel implementation left right (.left operation) =
      FreeM.left (Q := PFunctor.sigma inputInterface)
        (eval implementation left operation) := rfl

@[simp] theorem evalParallel_right
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    {leftOutput rightOutput : PFunctor.{uA, uB}}
    (left : Wiring Boxes Arity Dom Cod Inputs inputInterface leftOutput)
    (right : Wiring Boxes Arity Dom Cod Inputs inputInterface rightOutput)
    (operation : rightOutput.A) :
    evalParallel implementation left right (.right operation) =
      FreeM.right (P := PFunctor.sigma inputInterface)
        (eval implementation right operation) := rfl

@[simp] theorem evalParallel_both
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    {leftOutput rightOutput : PFunctor.{uA, uB}}
    (left : Wiring Boxes Arity Dom Cod Inputs inputInterface leftOutput)
    (right : Wiring Boxes Arity Dom Cod Inputs inputInterface rightOutput)
    (leftOperation : leftOutput.A) (rightOperation : rightOutput.A) :
    evalParallel implementation left right (.both leftOperation rightOperation) =
      FreeM.parallel (eval implementation left leftOperation)
        (eval implementation right rightOperation) := rfl

/-- Displayed evaluation of two independent displayed wirings is the displayed
parallel handler of their component evaluations. -/
def evalDisplayedParallel
    (domDisplay : (b : Boxes) → (port : Arity b) →
      Display.{uA, uB, uC, uD} (Dom b port))
    (codDisplay : (b : Boxes) → Display.{uA, uB, uC, uD} (Cod b))
    (inputDisplay : (i : Inputs) →
      Display.{uA, uB, uC, uD} (inputInterface i))
    (implementation : (b : Boxes) →
      (a : (Cod b).A) → FreeM (PFunctor.sigma (Dom b)) ((Cod b).B a))
    (displayedImplementation : (b : Boxes) →
      Display.Handler (codDisplay b) (Display.sigma (domDisplay b))
        (implementation b))
    {leftOutput rightOutput : PFunctor.{uA, uB}}
    {left : Wiring Boxes Arity Dom Cod Inputs inputInterface leftOutput}
    {right : Wiring Boxes Arity Dom Cod Inputs inputInterface rightOutput}
    {leftDisplay : Display.{uA, uB, uC, uD} leftOutput}
    {rightDisplay : Display.{uA, uB, uC, uD} rightOutput}
    (displayedLeft : Displayed domDisplay codDisplay inputDisplay left leftDisplay)
    (displayedRight : Displayed domDisplay codDisplay inputDisplay right rightDisplay) :
    Display.Handler (Display.parallelSum leftDisplay rightDisplay)
      (Display.parallelSum (Display.sigma inputDisplay)
        (Display.sigma inputDisplay))
      (evalParallel implementation left right) :=
  Display.Handler.parallel
    (evalDisplayed domDisplay codDisplay inputDisplay implementation
      displayedImplementation displayedLeft)
    (evalDisplayed domDisplay codDisplay inputDisplay implementation
      displayedImplementation displayedRight)

end Wiring
end PFunctor
