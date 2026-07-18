/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module


public import PolyFun.PFunctor.PatternRunsOnMatter.Parallel
public import PolyFun.PFunctor.Display.Parallel.Free
public import PolyFun.PFunctor.Dynamical.Responder.Parallel.VerifiedCoherence
public import PolyFun.PFunctor.Wiring.Parallel

/-!
# Regression tests for one-or-both parallel composition

The examples exercise all three interface branches, the residual one-sided
program phase, responder state freezing, displayed coalgebra closure,
reindexing compatibility, and the Pattern-Runs-on-Matter comparison.
-/

@[expose] public section

namespace PFunctor.ParallelExample

def Left : PFunctor.{0, 0} := ⟨Bool, fun _ => Bool⟩

def Right : PFunctor.{0, 0} := ⟨PUnit.{1}, fun _ => Nat⟩

def leftResponder : Responder Nat Left :=
  Responder.mk' (fun _ query => !query) (fun state _ => state + 1)

def rightResponder : Responder Nat Right :=
  Responder.mk' (fun state _ => state) (fun state _ => state + 10)

def leftProgram : FreeM Left Bool :=
  FreeM.liftBind true FreeM.pure

def rightProgram : FreeM Right Nat :=
  FreeM.liftBind PUnit.unit FreeM.pure

example :
    (Responder.parallel leftResponder rightResponder).runFree
      (FreeM.parallel leftProgram rightProgram) (0, 5) =
        ((false, 5), (1, 15)) :=
  rfl

example :
    (Responder.parallel leftResponder rightResponder).runFree
      (FreeM.parallel leftProgram (FreeM.pure 7)) (0, 5) =
        ((false, 7), (1, 5)) :=
  rfl

example :
    (Responder.parallel leftResponder rightResponder).runFree
      (FreeM.parallel (FreeM.pure true) rightProgram) (0, 5) =
        ((true, 5), (0, 15)) :=
  rfl

example :
    (PFunctor.Equiv.parallelSumDecomposition Left Right).equivA
        (.both true PUnit.unit) =
      Sum.inr (true, PUnit.unit) :=
  rfl

example (choice : ParallelChoice (ParallelChoice Bool Nat) PUnit) :
    (ParallelChoice.assoc Bool Nat PUnit).symm
        (ParallelChoice.assoc Bool Nat PUnit choice) = choice :=
  (ParallelChoice.assoc Bool Nat PUnit).left_inv choice

def leftDisplay : Display Left where
  position _ := PUnit
  direction _ _ _ := PUnit

def rightDisplay : Display Right where
  position _ := PUnit
  direction _ _ _ := PUnit

def leftInvariant (_ : Nat) : Type := PUnit

def rightInvariant (_ : Nat) : Type := PUnit

def displayedLeftResponder :
    Display.Coalgebra (Display.responder leftDisplay)
      leftResponder.out leftInvariant :=
  (Display.responderCoalgebraEquiv leftDisplay leftResponder leftInvariant).symm
    fun _ _ _ _ => (PUnit.unit, PUnit.unit)

def displayedRightResponder :
    Display.Coalgebra (Display.responder rightDisplay)
      rightResponder.out rightInvariant :=
  (Display.responderCoalgebraEquiv rightDisplay rightResponder rightInvariant).symm
    fun _ _ _ _ => (PUnit.unit, PUnit.unit)

def displayedLeftProgram :
    FreeM.Displayed
      (leftDisplay.toDisplayedAlgebra (fun _ => PUnit)) leftProgram :=
  ⟨PUnit.unit, fun answer _ => leftDisplay.leaf _ answer PUnit.unit⟩

def displayedRightProgram :
    FreeM.Displayed
      (rightDisplay.toDisplayedAlgebra (fun _ => PUnit)) rightProgram :=
  ⟨PUnit.unit, fun answer _ => rightDisplay.leaf _ answer PUnit.unit⟩

def displayedParallelProgram :
    FreeM.Displayed
      ((Display.parallelSum leftDisplay rightDisplay).toDisplayedAlgebra
        (fun _ => PUnit × PUnit))
      (FreeM.parallel leftProgram rightProgram) :=
  FreeM.Displayed.parallel leftProgram rightProgram
    displayedLeftProgram displayedRightProgram

def displayedParallelResponder :
    Display.Coalgebra
      (Display.responder (Display.parallelSum leftDisplay rightDisplay))
      (Responder.parallel leftResponder rightResponder).out
      (fun state => leftInvariant state.1 × rightInvariant state.2) :=
  Responder.parallelCoalgebra leftResponder rightResponder
    leftInvariant rightInvariant displayedLeftResponder displayedRightResponder

example :
    Responder.runFreeDisplayed
      (Display.parallelSum leftDisplay rightDisplay)
      (Responder.parallel leftResponder rightResponder)
      displayedParallelResponder displayedParallelProgram
      (0, 5) (PUnit.unit, PUnit.unit) =
        ((PUnit.unit, PUnit.unit), (PUnit.unit, PUnit.unit)) :=
  rfl

def leftIdentityHandler : Handler (FreeM Left) Left := Handler.id Left

def rightIdentityHandler : Handler (FreeM Right) Right := Handler.id Right

example :
    Responder.reindex
        (Handler.parallel leftIdentityHandler rightIdentityHandler)
        (Responder.parallel leftResponder rightResponder) =
      Responder.parallel
        (Responder.reindex leftIdentityHandler leftResponder)
        (Responder.reindex rightIdentityHandler rightResponder) :=
  Responder.reindex_parallel _ _ _ _

example :
    Responder.reindexViaRunAgainst
        (Handler.parallel leftIdentityHandler rightIdentityHandler)
        (Responder.parallel leftResponder rightResponder) =
      Responder.parallel
        (Responder.reindexViaRunAgainst leftIdentityHandler leftResponder)
        (Responder.reindexViaRunAgainst rightIdentityHandler rightResponder) :=
  Responder.reindexViaRunAgainst_parallel leftIdentityHandler
    rightIdentityHandler leftResponder rightResponder

end PFunctor.ParallelExample

namespace PFunctor.ParallelUniverseCanary

universe uA₁ uA₂ uA₃ uA₄ uA₅ uA₆ uB uB₁ uB₂ uE uF
  uC₁ uD₁ uC₂ uD₂ uC₃ uD₃ uC₄ uD₄ uC₅ uD₅ uC₆ uD₆
  uS₁ uS₂

def program
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {E : Type uE} {F : Type uF} :
    FreeM P E → FreeM Q F → FreeM (P ∥ Q) (E × F) :=
  FreeM.parallel

def display
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    Display.{max uA₁ uA₂, uB, max uC₁ uC₂, max uD₁ uD₂} (P ∥ Q) :=
  Display.parallelSum S T

def relationalDisplayLift
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC₁, uD₁} P)
    (right : Display.{uA₂, uB, uC₂, uD₂} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC₃, uD₃} (P ⊗ Q)) :
    Display.{max uA₁ uA₂, uB, max uC₁ uC₂ uC₃,
      max uD₁ uD₂ uD₃} (P ∥ Q) :=
  Display.parallelSumComponentsLift left right joint

def relationalDisplayLiftLeftPositionEquiv
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC₁, uD₁} P)
    (right : Display.{uA₂, uB, uC₂, uD₂} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC₃, uD₃} (P ⊗ Q))
    (a : P.A) :
    left.position a ≃
      (relationalDisplayLift left right joint).position (.left a) :=
  Display.parallelSumComponentsLiftPositionLeftEquiv left right joint a

def relationalDisplayLiftRightDirectionEquiv
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC₁, uD₁} P)
    (right : Display.{uA₂, uB, uC₂, uD₂} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC₃, uD₃} (P ⊗ Q))
    (b : Q.A) (contract : right.position b) (answer : Q.B b) :
    right.direction b contract answer ≃
      (relationalDisplayLift left right joint).direction
        (.right b) (ULift.up.{max uC₁ uC₃} contract) answer :=
  Display.parallelSumComponentsLiftDirectionRightEquiv
    left right joint b contract answer

def relationalDisplayLiftJointDirectionEquiv
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (left : Display.{uA₁, uB, uC₁, uD₁} P)
    (right : Display.{uA₂, uB, uC₂, uD₂} Q)
    (joint : Display.{max uA₁ uA₂, uB, uC₃, uD₃} (P ⊗ Q))
    (a : P.A) (b : Q.A) (contract : joint.position (a, b))
    (answer : P.B a × Q.B b) :
    joint.direction (a, b) contract answer ≃
      (relationalDisplayLift left right joint).direction
        (.both a b) (ULift.up.{max uC₁ uC₂} contract) answer :=
  Display.parallelSumComponentsLiftDirectionBothEquiv
    left right joint a b contract answer

/-- A displayed lens does not identify the response universes of its source
and target polynomial interfaces. -/
def heterogeneousDisplayLens
    {P : PFunctor.{uA₄, uB₁}} {Q : PFunctor.{uA₅, uB₂}}
    {S : Display.{uA₄, uB₁, uC₄, uD₄} P}
    {T : Display.{uA₅, uB₂, uC₅, uD₅} Q}
    (base : Lens P Q)
    (toPosition : (a : P.A) → S.position a → T.position (base.toFunA a))
    (toDirection : (a : P.A) → (c : S.position a) →
      (answer : Q.B (base.toFunA a)) →
      T.direction (base.toFunA a) (toPosition a c) answer →
        S.direction a c (base.toFunB a answer)) :
    Display.Lens S T base :=
  ⟨toPosition, toDirection⟩

/-- Totalization preserves the independent response universes exposed by a
displayed lens. -/
def heterogeneousDisplayLensTotal
    {P : PFunctor.{uA₄, uB₁}} {Q : PFunctor.{uA₅, uB₂}}
    {S : Display.{uA₄, uB₁, uC₄, uD₄} P}
    {T : Display.{uA₅, uB₂, uC₅, uD₅} Q}
    {base : Lens P Q} (displayed : Display.Lens S T base) :
    Lens S.total T.total :=
  displayed.toTotal

/-- The one-operation handler embedding preserves the independent response
universes exposed by a displayed lens. -/
def heterogeneousDisplayLensHandler
    {P : PFunctor.{uA₄, uB₁}} {Q : PFunctor.{uA₅, uB₂}}
    {S : Display.{uA₄, uB₁, uC₄, uD₄} P}
    {T : Display.{uA₅, uB₂, uC₅, uD₅} Q}
    {base : Lens P Q} (displayed : Display.Lens S T base) :
    Display.Handler S T (Handler.ofLens base) :=
  displayed.toHandler

def handler
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Handler (FreeM (P ∥ Q)) (P ∥ Q) :=
  Handler.parallel (Handler.id P) (Handler.id Q)

def displayedHandler
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    Display.Handler (Display.parallelSum S T) (Display.parallelSum S T)
      (handler (P := P) (Q := Q)) :=
  Display.Handler.parallel (Display.Handler.id S) (Display.Handler.id T)

def responder
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {LeftState : Type uS₁} {RightState : Type uS₂} :
    Responder LeftState P → Responder RightState Q →
      Responder (LeftState × RightState) (P ∥ Q) :=
  Responder.parallel

def behavior
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    PFunctor.M (P ⊸ X.{uA₁, uB}) →
    PFunctor.M (Q ⊸ X.{uA₂, uB}) →
      PFunctor.M ((P ∥ Q) ⊸ X.{max uA₁ uA₂, uB}) :=
  Responder.parallelBehavior

def verifiedBehavior
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right) :
    Display.M (Display.responder (Display.parallelSum S T))
      (behavior left right) :=
  Responder.parallelVerifiedBehavior S T left displayedLeft right displayedRight

theorem lensMapComp
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {W : PFunctor.{uA₅, uB}} {Y : PFunctor.{uA₆, uB}}
    (secondLeft : Lens R W) (secondRight : Lens V Y)
    (firstLeft : Lens P R) (firstRight : Lens Q V) :
    Lens.parallelSumMap secondLeft secondRight ∘ₗ
        Lens.parallelSumMap firstLeft firstRight =
      Lens.parallelSumMap (secondLeft ∘ₗ firstLeft)
        (secondRight ∘ₗ firstRight) :=
  Lens.parallelSumMap_comp secondLeft secondRight firstLeft firstRight

theorem lensAssocNatural
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}}
    {P' : PFunctor.{uA₄, uB}} {Q' : PFunctor.{uA₅, uB}}
    {R' : PFunctor.{uA₆, uB}}
    (left : Lens P P') (middle : Lens Q Q') (right : Lens R R') :
    Lens.parallelSumAssoc P' Q' R' ∘ₗ
        Lens.parallelSumMap (Lens.parallelSumMap left middle) right =
      Lens.parallelSumMap left (Lens.parallelSumMap middle right) ∘ₗ
        Lens.parallelSumAssoc P Q R :=
  Lens.parallelSumAssoc_natural left middle right

theorem displayLensMapComp
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}} {V : PFunctor.{uA₄, uB}}
    {W : PFunctor.{uA₅, uB}} {Y : PFunctor.{uA₆, uB}}
    {S₁ : Display.{uA₁, uB, uC₁, uD₁} P}
    {T₁ : Display.{uA₂, uB, uC₂, uD₂} Q}
    {S₂ : Display.{uA₃, uB, uC₃, uD₃} R}
    {T₂ : Display.{uA₄, uB, uC₄, uD₄} V}
    {S₃ : Display.{uA₅, uB, uC₅, uD₅} W}
    {T₃ : Display.{uA₆, uB, uC₆, uD₆} Y}
    {firstLeftBase : Lens P R} {firstRightBase : Lens Q V}
    {secondLeftBase : Lens R W} {secondRightBase : Lens V Y}
    (firstLeft : Display.Lens S₁ S₂ firstLeftBase)
    (firstRight : Display.Lens T₁ T₂ firstRightBase)
    (secondLeft : Display.Lens S₂ S₃ secondLeftBase)
    (secondRight : Display.Lens T₂ T₃ secondRightBase) :
    Display.Lens.transport
        (Lens.parallelSumMap_comp secondLeftBase secondRightBase
          firstLeftBase firstRightBase)
      (Display.Lens.comp
        (Display.Lens.parallelSumMap secondLeft secondRight)
        (Display.Lens.parallelSumMap firstLeft firstRight)) =
      Display.Lens.parallelSumMap
        (Display.Lens.comp secondLeft firstLeft)
        (Display.Lens.comp secondRight firstRight) :=
  Display.Lens.parallelSumMap_comp firstLeft firstRight secondLeft secondRight

theorem displayLensAssocNatural
    {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB}}
    {P' : PFunctor.{uA₄, uB}} {Q' : PFunctor.{uA₅, uB}}
    {R' : PFunctor.{uA₆, uB}}
    {S₁ : Display.{uA₁, uB, uC₁, uD₁} P}
    {T₁ : Display.{uA₂, uB, uC₂, uD₂} Q}
    {U₁ : Display.{uA₃, uB, uC₃, uD₃} R}
    {S₂ : Display.{uA₄, uB, uC₄, uD₄} P'}
    {T₂ : Display.{uA₅, uB, uC₅, uD₅} Q'}
    {U₂ : Display.{uA₆, uB, uC₆, uD₆} R'}
    {leftBase : Lens P P'} {middleBase : Lens Q Q'}
    {rightBase : Lens R R'}
    (left : Display.Lens S₁ S₂ leftBase)
    (middle : Display.Lens T₁ T₂ middleBase)
    (right : Display.Lens U₁ U₂ rightBase) :
    Display.Lens.transport
        (Lens.parallelSumAssoc_natural leftBase middleBase rightBase)
      (Display.Lens.comp (Display.Lens.parallelSumAssoc S₂ T₂ U₂)
        (Display.Lens.parallelSumMap
          (Display.Lens.parallelSumMap left middle) right)) =
      Display.Lens.comp
        (Display.Lens.parallelSumMap left
          (Display.Lens.parallelSumMap middle right))
        (Display.Lens.parallelSumAssoc S₁ T₁ U₁) :=
  Display.Lens.parallelSumAssoc_natural left middle right

end PFunctor.ParallelUniverseCanary

namespace PFunctor.ParallelLawCanary

def Step : PFunctor.{0, 0} := ⟨Bool, fun _ => PUnit⟩

def leftNegLens : Lens ParallelExample.Left ParallelExample.Left where
  toFunA (operation : Bool) := !operation
  toFunB _ (answer : Bool) := !answer

def rightSuccLens : Lens ParallelExample.Right ParallelExample.Right where
  toFunA _ := PUnit.unit
  toFunB _ (answer : Nat) := answer + 1

def leftBoolDisplay : Display ParallelExample.Left where
  position _ := Bool
  direction _ _ _ := Bool

def rightBoolDisplay : Display ParallelExample.Right where
  position _ := String
  direction _ _ _ := Bool

def displayedLeftNeg :
    Display.Lens leftBoolDisplay leftBoolDisplay leftNegLens where
  toPosition _ contract := by
    change Bool at contract ⊢
    exact !contract
  toDirection _ _ _ direction := by
    change Bool at direction ⊢
    exact !direction

def displayedRightSucc :
    Display.Lens rightBoolDisplay rightBoolDisplay rightSuccLens where
  toPosition _ contract := by
    change String at contract ⊢
    exact contract ++ "!"
  toDirection _ _ _ direction := by
    change Bool at direction ⊢
    exact !direction

def rightBoolInvariant (_ : Nat) : Type := PUnit

def rightBoolCoalgebra :
    Display.Coalgebra (Display.responder rightBoolDisplay)
      ParallelExample.rightResponder.out rightBoolInvariant :=
  (Display.responderCoalgebraEquiv rightBoolDisplay
    ParallelExample.rightResponder rightBoolInvariant).symm fun
      _ _ _ _ => ⟨false, PUnit.unit⟩

def rightBoolVerifiedBehavior :
    Display.M (Display.responder rightBoolDisplay)
      (ParallelExample.rightResponder.behavior 5) :=
  Responder.verifiedBehavior rightBoolDisplay
    ParallelExample.rightResponder rightBoolInvariant
    rightBoolCoalgebra 5 PUnit.unit

def rightBoolPresentationId :
    Responder.VerifiedPresentationHom rightBoolDisplay
      ParallelExample.rightResponder rightBoolInvariant rightBoolCoalgebra
      ParallelExample.rightResponder rightBoolInvariant rightBoolCoalgebra :=
  Responder.VerifiedPresentationHom.id

def rightBoolToTerminal :=
  Responder.VerifiedPresentationHom.toTerminal rightBoolDisplay
    ParallelExample.rightResponder rightBoolInvariant rightBoolCoalgebra

example : rightBoolPresentationId.toState 5 = 5 :=
  rfl

example :
    (rightBoolPresentationId.comp rightBoolPresentationId).toWitness
      5 PUnit.unit = PUnit.unit :=
  rfl

/-- Componentwise presentation parallel has genuine interchange even though
arbitrary free handlers do not have an unrestricted Kleisli interchange law. -/
example :
    (rightBoolToTerminal.parallel rightBoolPresentationId).comp
        (rightBoolPresentationId.parallel rightBoolPresentationId) =
      (rightBoolToTerminal.comp rightBoolPresentationId).parallel
        (rightBoolPresentationId.comp rightBoolPresentationId) :=
  Responder.VerifiedPresentationHom.parallel_comp _ _ _ _

example :
    Display.M.transport
        (Responder.mapBehavior_id
          (ParallelExample.rightResponder.behavior 5))
      (Responder.mapVerifiedBehavior (Display.Lens.id rightBoolDisplay)
        (ParallelExample.rightResponder.behavior 5)
        rightBoolVerifiedBehavior) =
      rightBoolVerifiedBehavior :=
  Responder.mapVerifiedBehavior_id _ _

/-- Composition order and transport orientation remain correct for a
genuinely nonidentity base lens and displayed lift. -/
example :
    Display.M.transport
        (Responder.mapBehavior_comp rightSuccLens rightSuccLens
          (ParallelExample.rightResponder.behavior 5))
      (Responder.mapVerifiedBehavior displayedRightSucc
        (Responder.mapBehavior rightSuccLens
          (ParallelExample.rightResponder.behavior 5))
        (Responder.mapVerifiedBehavior displayedRightSucc
          (ParallelExample.rightResponder.behavior 5)
          rightBoolVerifiedBehavior)) =
      Responder.mapVerifiedBehavior
        (Display.Lens.comp displayedRightSucc displayedRightSucc)
        (ParallelExample.rightResponder.behavior 5)
        rightBoolVerifiedBehavior :=
  Responder.mapVerifiedBehavior_comp _ _ _ _

def displayedNonidentityParallel :=
  Display.Lens.parallelSumMap displayedLeftNeg displayedRightSucc

def rightSuccAnswer :
    ParallelExample.Right.B (rightSuccLens.toFunA PUnit.unit) := by
  change Nat
  exact 4

def parallelMappedAnswer :
    (ParallelExample.Left ∥ ParallelExample.Right).B
      ((Lens.parallelSumMap leftNegLens rightSuccLens).toFunA
        (.both true PUnit.unit)) :=
  (true, rightSuccAnswer)

example :
    displayedNonidentityParallel.toPosition (.left true) (ULift.up false) =
      ULift.up true :=
  rfl

example :
    displayedNonidentityParallel.toPosition (.right PUnit.unit)
        (ULift.up "right") = ULift.up "right!" :=
  rfl

example :
    displayedNonidentityParallel.toPosition (.both true PUnit.unit)
        (false, "right") = (true, "right!") :=
  rfl

example :
    displayedNonidentityParallel.toDirection (.left true) (ULift.up false)
        true (ULift.up true) = ULift.up false :=
  rfl

example :
    displayedNonidentityParallel.toDirection (.right PUnit.unit)
        (ULift.up "right") rightSuccAnswer (ULift.up false) = ULift.up true :=
  rfl

example :
    displayedNonidentityParallel.toDirection (.both true PUnit.unit)
        (false, "right") parallelMappedAnswer (true, false) = (false, true) :=
  rfl

example : Display.Lens.TotalEq
    (Display.Lens.comp (Display.Lens.parallelSumZero leftBoolDisplay)
      (Display.Lens.parallelSumMap displayedLeftNeg
        (Display.Lens.id Display.zero)))
    (Display.Lens.comp displayedLeftNeg
      (Display.Lens.parallelSumZero leftBoolDisplay)) :=
  Display.Lens.parallelSumZero_natural_total displayedLeftNeg

example : Display.Lens.TotalEq
    (Display.Lens.comp (Display.Lens.zeroParallelSum leftBoolDisplay)
      (Display.Lens.parallelSumMap (Display.Lens.id Display.zero)
        displayedLeftNeg))
    (Display.Lens.comp displayedLeftNeg
      (Display.Lens.zeroParallelSum leftBoolDisplay)) :=
  Display.Lens.zeroParallelSum_natural_total displayedLeftNeg

example : Display.Lens.TotalEq
    (Display.Lens.comp
      (Display.Lens.parallelSumComm leftBoolDisplay rightBoolDisplay)
      displayedNonidentityParallel)
    (Display.Lens.comp
      (Display.Lens.parallelSumMap displayedRightSucc displayedLeftNeg)
      (Display.Lens.parallelSumComm leftBoolDisplay rightBoolDisplay)) :=
  Display.Lens.parallelSumComm_natural_total displayedLeftNeg displayedRightSucc

/-- The public transported-equality theorem remains usable for genuinely
nonidentity displayed maps, rather than only through its total-polynomial
formulation. -/
example :
    Display.Lens.transport
        (Lens.parallelSumComm_natural leftNegLens rightSuccLens)
      (Display.Lens.comp
        (Display.Lens.parallelSumComm leftBoolDisplay rightBoolDisplay)
        displayedNonidentityParallel) =
      Display.Lens.comp
        (Display.Lens.parallelSumMap displayedRightSucc displayedLeftNeg)
        (Display.Lens.parallelSumComm leftBoolDisplay rightBoolDisplay) :=
  Display.Lens.parallelSumComm_natural displayedLeftNeg displayedRightSucc

/-- A total-polynomial proof promotes canonically to ordinary equality in the
target base-lens fiber. -/
example :
    Display.Lens.transport
        (Lens.parallelSumZero_natural leftNegLens)
      (Display.Lens.comp
        (Display.Lens.parallelSumZero leftBoolDisplay)
        (Display.Lens.parallelSumMap displayedLeftNeg
          (Display.Lens.id Display.zero))) =
      Display.Lens.comp displayedLeftNeg
        (Display.Lens.parallelSumZero leftBoolDisplay) :=
  Display.Lens.transport_eq_of_totalEq
    (Lens.parallelSumZero_natural leftNegLens) _ _
    (Display.Lens.parallelSumZero_natural_total displayedLeftNeg)

example : Display.Lens.TotalEq
    (Display.Lens.parallelSumMap
      (Display.Lens.parallelSumZero leftBoolDisplay)
      (Display.Lens.id rightBoolDisplay))
    (Display.Lens.comp
      (Display.Lens.parallelSumMap (Display.Lens.id leftBoolDisplay)
        (Display.Lens.zeroParallelSum rightBoolDisplay))
      (Display.Lens.parallelSumAssoc leftBoolDisplay Display.zero
        rightBoolDisplay)) :=
  Display.Lens.parallelSum_triangle_total leftBoolDisplay rightBoolDisplay

example :
    Responder.mapBehavior
        (Lens.parallelSumComm ParallelExample.Left ParallelExample.Right)
        (Responder.parallelBehavior
          (ParallelExample.rightResponder.behavior 5)
          (ParallelExample.leftResponder.behavior 0)) =
      Responder.parallelBehavior
        (ParallelExample.leftResponder.behavior 0)
        (ParallelExample.rightResponder.behavior 5) :=
  Responder.mapBehavior_parallel_comm _ _

example :
    Responder.mapBehavior
        (Lens.parallelSumZero ParallelExample.Left :
          Lens (ParallelExample.Left ∥ (0 : PFunctor)) ParallelExample.Left)
        (ParallelExample.leftResponder.behavior 0) =
      Responder.parallelBehavior
        (ParallelExample.leftResponder.behavior 0)
        ((Responder.zero : Responder PUnit.{1} (0 : PFunctor.{0, 0})).behavior
          PUnit.unit) :=
  Responder.mapBehavior_parallel_zero_right _

example :
    Responder.mapBehavior
        (Lens.zeroParallelSum ParallelExample.Left :
          Lens ((0 : PFunctor) ∥ ParallelExample.Left) ParallelExample.Left)
        (ParallelExample.leftResponder.behavior 0) =
      Responder.parallelBehavior
        ((Responder.zero : Responder PUnit.{1} (0 : PFunctor.{0, 0})).behavior
          PUnit.unit)
        (ParallelExample.leftResponder.behavior 0) :=
  Responder.mapBehavior_parallel_zero_left _

example :
    Responder.mapBehavior
        (Lens.parallelSumAssoc ParallelExample.Left ParallelExample.Right
          ParallelExample.Left)
        (Responder.parallelBehavior
          (ParallelExample.leftResponder.behavior 0)
          (Responder.parallelBehavior
            (ParallelExample.rightResponder.behavior 5)
            (ParallelExample.leftResponder.behavior 7))) =
      Responder.parallelBehavior
        (Responder.parallelBehavior
          (ParallelExample.leftResponder.behavior 0)
          (ParallelExample.rightResponder.behavior 5))
        (ParallelExample.leftResponder.behavior 7) :=
  Responder.mapBehavior_parallel_assoc _ _ _

def unaryDisplay : Display Step where
  position _ := PUnit
  direction _ _ _ := PUnit

/-- A genuinely relational joint contract: simultaneous operations must be
equal.  This cannot be factored as independent unary contracts. -/
def jointEqualityDisplay : Display (Step ⊗ Step) where
  position operation := PLift (operation.1 = operation.2)
  direction _ _ _ := PUnit

def relationalDisplay : Display (Step ∥ Step) :=
  Display.parallelSumComponents unaryDisplay unaryDisplay jointEqualityDisplay

example : Nonempty (relationalDisplay.position (.both false false)) :=
  ⟨⟨rfl⟩⟩

example : IsEmpty (relationalDisplay.position (.both false true)) :=
  ⟨fun witness => Bool.noConfusion witness.down⟩

example : Display.jointComponent relationalDisplay = jointEqualityDisplay := by
  rfl

/-! Nontrivial dependent displays used to prevent the displayed API from
silently swapping or erasing component witnesses. -/

def dependentLeftDisplay : Display ParallelExample.Left where
  position (operation : Bool) := if operation then Nat else Bool
  direction (_ : Bool) _ (answer : Bool) := if answer then Fin 2 else Fin 3

def dependentRightDisplay : Display ParallelExample.Right where
  position _ := String
  direction _ _ (answer : Nat) := Fin (answer + 1)

def leftPost (answer : Bool) :
    (if answer then Fin 2 else Fin 3) := by
  cases answer <;> exact ⟨0, Nat.zero_lt_succ _⟩

def rightPost (answer : Nat) : Fin (answer + 1) :=
  ⟨0, Nat.zero_lt_succ _⟩

def dependentParallelIdentity :
    Display.Handler
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Handler.parallel (Handler.id ParallelExample.Left)
        (Handler.id ParallelExample.Right)) :=
  Display.Handler.parallel (Display.Handler.id dependentLeftDisplay)
    (Display.Handler.id dependentRightDisplay)

def sampleLeftContract : dependentLeftDisplay.position true := by
  change Nat
  exact 5

def sampleRightContract : dependentRightDisplay.position PUnit.unit := by
  change String
  exact "right"

def sampleLeftAnswer : ParallelExample.Left.B true := by
  change Bool
  exact false

def sampleRightAnswer : ParallelExample.Right.B PUnit.unit := by
  change Nat
  exact 4

example :
    (dependentParallelIdentity (.both true PUnit.unit)
      (sampleLeftContract, sampleRightContract)).1 =
        (sampleLeftContract, sampleRightContract) :=
  rfl

example :
    ((dependentParallelIdentity (.both true PUnit.unit)
      (sampleLeftContract, sampleRightContract)).2
        (sampleLeftAnswer, sampleRightAnswer)
        (leftPost false, rightPost 4)).down =
      (leftPost false, rightPost 4) :=
  rfl

def dependentLeftInvariant (state : Nat) : Type := Fin (state + 1)

def dependentRightInvariant (state : Nat) : Type := PLift (state = state)

def dependentLeftCoalgebra :
    Display.Coalgebra (Display.responder dependentLeftDisplay)
      ParallelExample.leftResponder.out dependentLeftInvariant :=
  (Display.responderCoalgebraEquiv dependentLeftDisplay
    ParallelExample.leftResponder dependentLeftInvariant).symm fun
      state _ operation _ => by
        refine ⟨?_, ⟨0, Nat.zero_lt_succ _⟩⟩
        change (if !operation then Fin 2 else Fin 3)
        exact leftPost (!operation)

def dependentRightCoalgebra :
    Display.Coalgebra (Display.responder dependentRightDisplay)
      ParallelExample.rightResponder.out dependentRightInvariant :=
  (Display.responderCoalgebraEquiv dependentRightDisplay
    ParallelExample.rightResponder dependentRightInvariant).symm fun
      state _ _ _ => by
        refine ⟨rightPost state, ?_⟩
        exact ⟨rfl⟩

def dependentLeftVerifiedBehavior :
    Display.M (Display.responder dependentLeftDisplay)
      (ParallelExample.leftResponder.behavior 0) :=
  Responder.verifiedBehavior dependentLeftDisplay
    ParallelExample.leftResponder dependentLeftInvariant
    dependentLeftCoalgebra 0 ⟨0, Nat.zero_lt_succ _⟩

def dependentRightVerifiedBehavior :
    Display.M (Display.responder dependentRightDisplay)
      (ParallelExample.rightResponder.behavior 5) :=
  Responder.verifiedBehavior dependentRightDisplay
    ParallelExample.rightResponder dependentRightInvariant
    dependentRightCoalgebra 5 ⟨rfl⟩

/-- Reindexing verified behavior is observed through genuinely dependent,
nonconstant postcondition evidence. -/
example :
    (Responder.appD dependentLeftDisplay
      (Responder.mapVerifiedBehavior
        (Display.Lens.id dependentLeftDisplay)
        (ParallelExample.leftResponder.behavior 0)
        dependentLeftVerifiedBehavior)
      true sampleLeftContract).1 = leftPost false := by
  rw [Responder.appD_mapVerifiedBehavior_post]
  rfl

def dependentParallelVerifiedBehavior :
    Display.M
      (Display.responder
        (Display.parallelSum dependentLeftDisplay dependentRightDisplay))
      (Responder.parallelBehavior
        (ParallelExample.leftResponder.behavior 0)
        (ParallelExample.rightResponder.behavior 5)) :=
  Responder.parallelVerifiedBehavior dependentLeftDisplay dependentRightDisplay
    (ParallelExample.leftResponder.behavior 0) dependentLeftVerifiedBehavior
    (ParallelExample.rightResponder.behavior 5) dependentRightVerifiedBehavior

example :
    Display.M.transport
        (Responder.mapBehavior_parallel_comm
          (ParallelExample.leftResponder.behavior 0)
          (ParallelExample.rightResponder.behavior 5))
      (Responder.mapVerifiedBehavior
        (Display.Lens.parallelSumComm dependentLeftDisplay
          dependentRightDisplay)
        (Responder.parallelBehavior
          (ParallelExample.rightResponder.behavior 5)
          (ParallelExample.leftResponder.behavior 0))
        (Responder.parallelVerifiedBehavior dependentRightDisplay
          dependentLeftDisplay
          (ParallelExample.rightResponder.behavior 5)
          dependentRightVerifiedBehavior
          (ParallelExample.leftResponder.behavior 0)
          dependentLeftVerifiedBehavior)) =
      dependentParallelVerifiedBehavior :=
  Responder.mapVerifiedBehavior_parallel_comm _ _ _ _ _ _

example :
    Display.M.transport
        (Responder.mapBehavior_parallel_zero_right
          (ParallelExample.leftResponder.behavior 0))
      (Responder.mapVerifiedBehavior
        (Display.Lens.parallelSumZero dependentLeftDisplay)
        (ParallelExample.leftResponder.behavior 0)
        dependentLeftVerifiedBehavior) =
      Responder.parallelVerifiedBehavior dependentLeftDisplay Display.zero
        (ParallelExample.leftResponder.behavior 0)
        dependentLeftVerifiedBehavior Responder.zeroBehavior
        Responder.zeroVerifiedBehavior :=
  Responder.mapVerifiedBehavior_parallel_zero_right _ _ _

example :
    Display.M.transport
        (Responder.mapBehavior_parallel_zero_left
          (ParallelExample.leftResponder.behavior 0))
      (Responder.mapVerifiedBehavior
        (Display.Lens.zeroParallelSum dependentLeftDisplay)
        (ParallelExample.leftResponder.behavior 0)
        dependentLeftVerifiedBehavior) =
      Responder.parallelVerifiedBehavior Display.zero dependentLeftDisplay
        Responder.zeroBehavior Responder.zeroVerifiedBehavior
        (ParallelExample.leftResponder.behavior 0)
        dependentLeftVerifiedBehavior :=
  Responder.mapVerifiedBehavior_parallel_zero_left _ _ _

example :
    Display.M.transport
        (Responder.mapBehavior_parallel_assoc
          (ParallelExample.leftResponder.behavior 0)
          (ParallelExample.rightResponder.behavior 5)
          (ParallelExample.leftResponder.behavior 0))
      (Responder.mapVerifiedBehavior
        (Display.Lens.parallelSumAssoc dependentLeftDisplay
          dependentRightDisplay dependentLeftDisplay)
        (Responder.parallelBehavior
          (ParallelExample.leftResponder.behavior 0)
          (Responder.parallelBehavior
            (ParallelExample.rightResponder.behavior 5)
            (ParallelExample.leftResponder.behavior 0)))
        (Responder.parallelVerifiedBehavior dependentLeftDisplay
          (Display.parallelSum dependentRightDisplay dependentLeftDisplay)
          (ParallelExample.leftResponder.behavior 0)
          dependentLeftVerifiedBehavior
          (Responder.parallelBehavior
            (ParallelExample.rightResponder.behavior 5)
            (ParallelExample.leftResponder.behavior 0))
          (Responder.parallelVerifiedBehavior dependentRightDisplay
            dependentLeftDisplay
            (ParallelExample.rightResponder.behavior 5)
            dependentRightVerifiedBehavior
            (ParallelExample.leftResponder.behavior 0)
            dependentLeftVerifiedBehavior))) =
      Responder.parallelVerifiedBehavior
        (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
        dependentLeftDisplay
        (Responder.parallelBehavior
          (ParallelExample.leftResponder.behavior 0)
          (ParallelExample.rightResponder.behavior 5))
        (Responder.parallelVerifiedBehavior dependentLeftDisplay
          dependentRightDisplay
          (ParallelExample.leftResponder.behavior 0)
          dependentLeftVerifiedBehavior
          (ParallelExample.rightResponder.behavior 5)
          dependentRightVerifiedBehavior)
        (ParallelExample.leftResponder.behavior 0)
        dependentLeftVerifiedBehavior :=
  Responder.mapVerifiedBehavior_parallel_assoc _ _ _ _ _ _ _ _ _

example :
    (Responder.appD
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      dependentParallelVerifiedBehavior (.both true PUnit.unit)
      (sampleLeftContract, sampleRightContract)).1 =
        (leftPost false, rightPost 5) := by
  unfold dependentParallelVerifiedBehavior
  rw [Responder.appD_post]
  rw [Responder.appD_parallelVerifiedBehavior_post_both]
  rfl

def sampleFalseContract : dependentLeftDisplay.position false := by
  change Bool
  exact true

example :
    (Responder.terminal (P := ParallelExample.Left ∥ ParallelExample.Right)).answer
      ((Responder.parallelBehavior
        (ParallelExample.leftResponder.behavior 0)
        (ParallelExample.rightResponder.behavior 5)).children
          ⟨(.both true PUnit.unit), PUnit.unit⟩)
      (.left false) = true := by
  rw [Responder.parallelBehavior_child_both,
    Responder.parallelBehavior_answer_left]
  rfl

example :
    (Responder.appD
      (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
      (Responder.appD
        (Display.parallelSum dependentLeftDisplay dependentRightDisplay)
        dependentParallelVerifiedBehavior (.both true PUnit.unit)
        (sampleLeftContract, sampleRightContract)).2
      (.left false) (ULift.up sampleFalseContract)).1 =
        ULift.up (leftPost true) := by
  rfl

/-! Parallel wiring evaluation keeps the two external resources separate.
The two sigma operations below carry distinct Boolean queries and are joined
only by the outer one-or-both interface. -/

namespace WiringCanary

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

example :
    Wiring.evalParallel implementation inputWiring inputWiring
        (.both false true) =
      @FreeM.liftBind
        (PFunctor.sigma inputInterface ∥ PFunctor.sigma inputInterface)
        (PUnit × PUnit)
        (ParallelChoice.both ⟨PUnit.unit, false⟩ ⟨PUnit.unit, true⟩ :
          (PFunctor.sigma inputInterface ∥
            PFunctor.sigma inputInterface).A)
        (fun answer => FreeM.pure answer) :=
  rfl

def domDisplay (box : Boxes) :
    (port : Arity box) → Display (Dom box port) :=
  nomatch box

def codDisplay (box : Boxes) : Display (Cod box) := nomatch box

def inputDisplay (_ : Inputs) : Display Step := unaryDisplay

def displayedImplementation (box : Boxes) :
    Display.Handler (codDisplay box) (Display.sigma (domDisplay box))
      (implementation box) :=
  nomatch box

def displayedInputWiring :
    Wiring.Displayed domDisplay codDisplay inputDisplay inputWiring unaryDisplay :=
  .input PUnit.unit

example :
    (Wiring.evalDisplayedParallel domDisplay codDisplay inputDisplay
      implementation displayedImplementation displayedInputWiring
      displayedInputWiring (.both false true) (PUnit.unit, PUnit.unit)).1 =
        (PUnit.unit, PUnit.unit) :=
  rfl

end WiringCanary

example :
    (PFunctor.Equiv.parallelSumComm ParallelExample.Left
      ParallelExample.Right).equivB (.both true PUnit.unit)
        (false, (7 : Nat)) =
      ((7 : Nat), false) :=
  rfl

example :
    ((PFunctor.Equiv.parallelSumComm ParallelExample.Left
      ParallelExample.Right).equivB (.both true PUnit.unit)).symm
        ((7 : Nat), false) =
      (false, (7 : Nat)) :=
  rfl

example :
    (PFunctor.Equiv.parallelSumAssoc ParallelExample.Left
      ParallelExample.Right ParallelExample.Left).equivB
        (.both (.both true PUnit.unit) false)
        ((false, (9 : Nat)), true) =
      (false, ((9 : Nat), true)) :=
  rfl

example :
    ((PFunctor.Equiv.parallelSumAssoc ParallelExample.Left
      ParallelExample.Right ParallelExample.Left).equivB
        (.both (.both true PUnit.unit) false)).symm
        (false, ((9 : Nat), true)) =
      ((false, (9 : Nat)), true) :=
  rfl

example :
    (PFunctor.Equiv.parallelSumDecomposition ParallelExample.Left
      ParallelExample.Right).equivA.symm
        (Sum.inr (true, PUnit.unit)) = .both true PUnit.unit :=
  rfl

example :
    ((PFunctor.Equiv.parallelSumDecomposition ParallelExample.Left
      ParallelExample.Right).equivB (.both true PUnit.unit)).symm
        (false, (4 : Nat)) =
      (false, (4 : Nat)) :=
  rfl

example :
    (PFunctor.Equiv.parallelSumZero ParallelExample.Left).equivB
      (.left true) false = false :=
  rfl

example :
    (PFunctor.Equiv.zeroParallelSum ParallelExample.Right).equivB
      (.right PUnit.unit) (4 : Nat) = (4 : Nat) :=
  rfl

example :
    (PFunctor.Equiv.parallelSumDecomposition ParallelExample.Left
      ParallelExample.Right).equivB (.both true PUnit.unit)
        (false, (4 : Nat)) =
      (false, (4 : Nat)) :=
  rfl

example :
    Lens.parallelSumComm ParallelExample.Right ParallelExample.Left ∘ₗ
        Lens.parallelSumComm ParallelExample.Left ParallelExample.Right =
      Lens.id (ParallelExample.Left ∥ ParallelExample.Right) :=
  Lens.parallelSumComm_involutive _ _

example :
    Lens.parallelSumMap leftNegLens rightSuccLens ∘ₗ
        Lens.parallelSumMap leftNegLens rightSuccLens =
      Lens.parallelSumMap (leftNegLens ∘ₗ leftNegLens)
        (rightSuccLens ∘ₗ rightSuccLens) :=
  Lens.parallelSumMap_comp _ _ _ _

example :
    Lens.parallelSumComm ParallelExample.Left ParallelExample.Right ∘ₗ
        Lens.parallelSumMap leftNegLens rightSuccLens =
      Lens.parallelSumMap rightSuccLens leftNegLens ∘ₗ
        Lens.parallelSumComm ParallelExample.Left ParallelExample.Right :=
  Lens.parallelSumComm_natural _ _

example :
    Lens.parallelSumAssoc ParallelExample.Left ParallelExample.Right Step ∘ₗ
        Lens.parallelSumMap
          (Lens.parallelSumMap leftNegLens rightSuccLens)
          (Lens.id Step) =
      Lens.parallelSumMap leftNegLens
          (Lens.parallelSumMap rightSuccLens (Lens.id Step)) ∘ₗ
        Lens.parallelSumAssoc ParallelExample.Left ParallelExample.Right Step :=
  Lens.parallelSumAssoc_natural _ _ _

example :
    (Lens.parallelSumZero ParallelExample.Left :
      Lens (ParallelExample.Left ∥ (0 : PFunctor)) ParallelExample.Left) ∘ₗ
        Lens.parallelSumMap leftNegLens
          (Lens.id (0 : PFunctor)) =
      leftNegLens ∘ₗ
        (Lens.parallelSumZero ParallelExample.Left :
          Lens (ParallelExample.Left ∥ (0 : PFunctor))
            ParallelExample.Left) :=
  Lens.parallelSumZero_natural leftNegLens

example :
    (Lens.zeroParallelSum ParallelExample.Left :
      Lens ((0 : PFunctor) ∥ ParallelExample.Left) ParallelExample.Left) ∘ₗ
        Lens.parallelSumMap (Lens.id (0 : PFunctor)) leftNegLens =
      leftNegLens ∘ₗ
        (Lens.zeroParallelSum ParallelExample.Left :
          Lens ((0 : PFunctor) ∥ ParallelExample.Left)
            ParallelExample.Left) :=
  Lens.zeroParallelSum_natural leftNegLens

example :
    Lens.parallelSumAssoc ParallelExample.Right Step ParallelExample.Left ∘ₗ
        (Lens.parallelSumComm ParallelExample.Left
          (ParallelExample.Right ∥ Step) ∘ₗ
          Lens.parallelSumAssoc ParallelExample.Left ParallelExample.Right Step) =
      Lens.parallelSumMap (Lens.id ParallelExample.Right)
          (Lens.parallelSumComm ParallelExample.Left Step) ∘ₗ
        (Lens.parallelSumAssoc ParallelExample.Right ParallelExample.Left Step ∘ₗ
          Lens.parallelSumMap
            (Lens.parallelSumComm ParallelExample.Left ParallelExample.Right)
            (Lens.id Step)) :=
  Lens.parallelSum_hexagon _ _ _

example :
    Lens.parallelSumMap (Lens.id ParallelExample.Left)
        (Lens.parallelSumAssoc ParallelExample.Right ParallelExample.Left Step) ∘ₗ
      (Lens.parallelSumAssoc ParallelExample.Left
          (ParallelExample.Right ∥ ParallelExample.Left) Step ∘ₗ
        Lens.parallelSumMap
          (Lens.parallelSumAssoc ParallelExample.Left ParallelExample.Right
            ParallelExample.Left) (Lens.id Step)) =
      Lens.parallelSumAssoc ParallelExample.Left ParallelExample.Right
          (ParallelExample.Left ∥ Step) ∘ₗ
        Lens.parallelSumAssoc
          (ParallelExample.Left ∥ ParallelExample.Right)
          ParallelExample.Left Step :=
  Lens.parallelSumAssoc_pentagon _ _ _ _

example :
    Lens.parallelSumMap
        (Lens.parallelSumZero ParallelExample.Left :
          Lens (ParallelExample.Left ∥ (0 : PFunctor))
            ParallelExample.Left)
        (Lens.id ParallelExample.Right) =
      Lens.parallelSumMap (Lens.id ParallelExample.Left)
          (Lens.zeroParallelSum ParallelExample.Right :
            Lens ((0 : PFunctor) ∥ ParallelExample.Right)
              ParallelExample.Right) ∘ₗ
        Lens.parallelSumAssoc ParallelExample.Left (0 : PFunctor)
          ParallelExample.Right :=
  Lens.parallelSum_triangle _ _

/-! The lockstep program operation is symmetric and associative. -/

example :
    FreeM.map (fun result => (result.2, result.1))
        ((FreeM.parallel ParallelExample.leftProgram
          ParallelExample.rightProgram).mapLens
            (Lens.parallelSumComm ParallelExample.Left
              ParallelExample.Right)) =
      FreeM.parallel ParallelExample.rightProgram ParallelExample.leftProgram :=
  FreeM.parallel_comm _ _

example :
    FreeM.map Prod.fst
        ((FreeM.parallel ParallelExample.leftProgram
          (FreeM.pure PUnit.unit : FreeM (0 : PFunctor) PUnit)).mapLens
            (Lens.parallelSumZero ParallelExample.Left)) =
      ParallelExample.leftProgram :=
  FreeM.parallel_pureUnit_right _

example :
    FreeM.map Prod.snd
        ((FreeM.parallel
          (FreeM.pure PUnit.unit : FreeM (0 : PFunctor) PUnit)
          ParallelExample.leftProgram).mapLens
            (Lens.zeroParallelSum ParallelExample.Left)) =
      ParallelExample.leftProgram :=
  FreeM.parallel_pureUnit_left _

example :
    FreeM.map (fun result => (result.1.1, (result.1.2, result.2)))
        ((FreeM.parallel
          (FreeM.parallel ParallelExample.leftProgram
            ParallelExample.rightProgram)
          ParallelExample.leftProgram).mapLens
            (Lens.parallelSumAssoc ParallelExample.Left
              ParallelExample.Right ParallelExample.Left)) =
      FreeM.parallel ParallelExample.leftProgram
        (FreeM.parallel ParallelExample.rightProgram
          ParallelExample.leftProgram) :=
  FreeM.parallel_assoc _ _ _

example :
    (Responder.parallel ParallelExample.rightResponder
      ParallelExample.leftResponder).answer (5, 0)
        ((PFunctor.Equiv.parallelSumComm ParallelExample.Left
          ParallelExample.Right).equivA (.both true PUnit.unit)) =
      (PFunctor.Equiv.parallelSumComm ParallelExample.Left
        ParallelExample.Right).equivB (.both true PUnit.unit)
          ((Responder.parallel ParallelExample.leftResponder
            ParallelExample.rightResponder).answer (0, 5)
              (.both true PUnit.unit)) :=
  Responder.parallel_answer_comm
    (P := ParallelExample.Left) (Q := ParallelExample.Right)
    ParallelExample.leftResponder ParallelExample.rightResponder
    ((0, 5) : Nat × Nat) (.both true PUnit.unit)

example :
    (Responder.parallel ParallelExample.leftResponder
      (Responder.parallel ParallelExample.rightResponder
        ParallelExample.leftResponder)).next (0, (5, 10))
        ((PFunctor.Equiv.parallelSumAssoc ParallelExample.Left
          ParallelExample.Right ParallelExample.Left).equivA
            (.both (.both true PUnit.unit) false)) =
      let next := (Responder.parallel
        (Responder.parallel ParallelExample.leftResponder
          ParallelExample.rightResponder)
        ParallelExample.leftResponder).next ((0, 5), 10)
          (.both (.both true PUnit.unit) false)
      (next.1.1, (next.1.2, next.2)) :=
  Responder.parallel_next_assoc
    (P := ParallelExample.Left) (Q := ParallelExample.Right)
    (R := ParallelExample.Left)
    ParallelExample.leftResponder ParallelExample.rightResponder
    ParallelExample.leftResponder (((0, 5), 10) : (Nat × Nat) × Nat)
    (.both (.both true PUnit.unit) false)

/-! Kleisli interchange fails for lockstep scheduling.  The first left
implementation performs `false` and then `true`; its interpreter erases the
first operation but retains the second.  Interpreting before parallelization
therefore exposes the second left operation soon enough to synchronize with
the right, while parallelizing first emits a right-only operation. -/

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

end PFunctor.ParallelLawCanary
