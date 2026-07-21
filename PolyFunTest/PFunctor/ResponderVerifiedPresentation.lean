/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder.Lens

/-!
# Regression tests for verified responder presentations

The examples exercise presentation identity/composition/terminal semantics,
nonidentity lens reindexing, proof-relevant state-free transport, and
independent source/target response universes.
-/

@[expose] public section

namespace PFunctor.ResponderVerifiedPresentationCanary

universe uA uB uC uD uA' uB' uC' uD' uS uI

def mapBehavior
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    (base : Lens P Q)
    (behavior : PFunctor.M (Q ⊸ X.{uA', uB'})) :
    PFunctor.M (P ⊸ X.{uA, uB}) :=
  Responder.mapBehavior base behavior

def mapVerifiedBehavior
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB', uC', uD'} Q}
    {base : Lens P Q} (displayedLens : Display.Lens S T base)
    (behavior : PFunctor.M (Q ⊸ X.{uA', uB'}))
    (displayedBehavior : Display.M (Display.responder T) behavior) :
    Display.M (Display.responder S) (Responder.mapBehavior base behavior) :=
  Responder.mapVerifiedBehavior displayedLens behavior displayedBehavior

def reindexPresentation
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB', uC', uD'} Q}
    (base : Handler (FreeM Q) P)
    (displayedHandler : Display.Handler S T base)
    {State : Type uS} (target : Responder State Q)
    (Invariant : State → Type uI)
    (displayedTarget :
      Display.Coalgebra (Display.responder T) target.out Invariant) :=
  Responder.reindexVerifiedPresentationHom base displayedHandler
    target Invariant displayedTarget

abbrev Interface : PFunctor.{0, 0} := ⟨PUnit, fun _ => Nat⟩

def responder : Responder Nat Interface :=
  Responder.mk' (fun state _ => state) (fun state _ => state + 10)

abbrev contract : Display Interface where
  position _ := String
  direction _ _ _ := Bool

def Invariant (_ : Nat) : Type := PUnit

def verified :
    Display.Coalgebra (Display.responder contract) responder.out Invariant :=
  (Display.responderCoalgebraEquiv contract responder Invariant).symm fun
    _ _ _ _ => ⟨false, PUnit.unit⟩

def verifiedBehavior :
    Display.M (Display.responder contract) (responder.behavior 5) :=
  Responder.verifiedBehavior contract responder Invariant verified 5 PUnit.unit

def presentationId :
    Responder.VerifiedPresentationHom contract
      responder Invariant verified responder Invariant verified :=
  Responder.VerifiedPresentationHom.id

def toTerminal :=
  Responder.VerifiedPresentationHom.toTerminal contract
    responder Invariant verified

example : presentationId.toState 5 = 5 :=
  rfl

example : presentationId.toWitness 5 PUnit.unit = PUnit.unit :=
  rfl

example :
    (presentationId.comp presentationId).toState 5 = 5 :=
  rfl

example :
    (toTerminal.comp presentationId).toState 5 = responder.behavior 5 :=
  rfl

example :
    (toTerminal.comp presentationId).toWitness 5 PUnit.unit =
      verifiedBehavior :=
  rfl

abbrev succLens : Lens Interface Interface where
  toFunA _ := PUnit.unit
  toFunB _ answer := answer + 1

abbrev displayedSucc : Display.Lens contract contract succLens where
  toPosition _ evidence := evidence ++ "!"
  toDirection _ _ _ direction := !direction

example : displayedSucc.toPosition PUnit.unit "state" = "state!" :=
  rfl

example : displayedSucc.toDirection PUnit.unit "state" 4 false = true :=
  rfl

def mappedBehavior :=
  Responder.mapBehavior succLens (responder.behavior 5)

def mappedVerifiedBehavior :
    Display.M (Display.responder contract) mappedBehavior :=
  Responder.mapVerifiedBehavior displayedSucc
    (responder.behavior 5) verifiedBehavior

/-- The backward action of the ordinary lens is observable in the answer. -/
example : (Responder.terminal (P := Interface)).answer
    mappedBehavior PUnit.unit = 6 :=
  rfl

/-- The backward action of the displayed lens is observable in the returned
postcondition. -/
example :
    (Responder.respondDisplayed contract mappedVerifiedBehavior
      PUnit.unit "state").1 = true :=
  rfl

/-- The mapped continuation advances the underlying presentation to state
`15`; observing it through the same lens therefore returns `16`. -/
example : (Responder.terminal (P := Interface)).answer
    (mappedBehavior.children ⟨PUnit.unit, PUnit.unit⟩) PUnit.unit = 16 :=
  rfl

example :
    (Responder.respondDisplayed contract
      (Responder.respondDisplayed contract mappedVerifiedBehavior
        PUnit.unit "state").2 PUnit.unit "next").1 = true :=
  rfl

/-- The terminal presentation witness exposes the independently expected
verified postcondition, rather than merely its definitional carrier. -/
example :
    (Responder.respondDisplayed contract (toTerminal.toWitness 5 PUnit.unit)
      PUnit.unit "state").1 = false :=
  rfl

example :
    Display.M.transport
        (Responder.mapBehavior_id (responder.behavior 5))
      (Responder.mapVerifiedBehavior (Display.Lens.id contract)
        (responder.behavior 5) verifiedBehavior) =
      verifiedBehavior :=
  Responder.mapVerifiedBehavior_id _ _

example :
    Display.M.transport
        (Responder.mapBehavior_comp succLens succLens (responder.behavior 5))
      (Responder.mapVerifiedBehavior displayedSucc
        (Responder.mapBehavior succLens (responder.behavior 5))
        (Responder.mapVerifiedBehavior displayedSucc
          (responder.behavior 5) verifiedBehavior)) =
      Responder.mapVerifiedBehavior
        (Display.Lens.comp displayedSucc displayedSucc)
        (responder.behavior 5) verifiedBehavior :=
  Responder.mapVerifiedBehavior_comp _ _ _ _

end PFunctor.ResponderVerifiedPresentationCanary
