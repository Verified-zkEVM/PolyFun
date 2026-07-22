/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Parallel.Lens
public import PolyFun.PFunctor.Dynamical.Responder.Parallel.Coherence
public import PolyFun.PFunctor.Dynamical.Responder.Parallel.VerifiedPresentation

/-!
# Associativity of verified parallel responder behavior

The displayed parallel associator is realized first between explicit verified
responder presentations, then transported to the canonical state-free API.
The public theorem exposes only the ordinary named associativity equality.
-/

@[expose] public section

universe uA₁ uA₂ uA₃ uB uC₁ uD₁ uC₂ uD₂ uC₃ uD₃ uLift

namespace PFunctor
namespace Responder

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}


/-- The displayed associator is a verified presentation homomorphism between
the two raw three-responder presentations. -/
private def parallelAssocVerifiedPresentationHom
    {R : PFunctor.{uA₃, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (U : Display.{uA₃, uB, uC₃, uD₃} R) :
    VerifiedPresentationHom
      (Display.parallelSum (Display.parallelSum S T) U)
      (Responder.parallel
        (Responder.parallel (Responder.terminal (P := P))
          (Responder.terminal (P := Q)))
        (Responder.terminal (P := R)))
      (fun state =>
        (Display.M (Display.responder S) state.1.1 ×
          Display.M (Display.responder T) state.1.2) ×
        Display.M (Display.responder U) state.2)
      (parallelCoalgebra
        (Responder.parallel (Responder.terminal (P := P))
          (Responder.terminal (P := Q)))
        (Responder.terminal (P := R))
        (fun state =>
          Display.M (Display.responder S) state.1 ×
            Display.M (Display.responder T) state.2)
        (Display.M (Display.responder U))
        (parallelCoalgebra (Responder.terminal (P := P))
          (Responder.terminal (P := Q))
          (Display.M (Display.responder S))
          (Display.M (Display.responder T))
          (Display.Coalgebra.terminal (Display.responder S))
          (Display.Coalgebra.terminal (Display.responder T)))
        (Display.Coalgebra.terminal (Display.responder U)))
      (Responder.reindex
        (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumAssoc P Q R))
        (Responder.parallel (Responder.terminal (P := P))
          (Responder.parallel (Responder.terminal (P := Q))
            (Responder.terminal (P := R)))))
      (fun state =>
        Display.M (Display.responder S) state.1 ×
          (Display.M (Display.responder T) state.2.1 ×
            Display.M (Display.responder U) state.2.2))
      (Responder.reindexCoalgebra
        (Display.parallelSum (Display.parallelSum S T) U)
        (Display.parallelSum S (Display.parallelSum T U))
        (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumAssoc P Q R))
        (Display.Lens.parallelSumAssoc S T U).toHandler
        (Responder.parallel (Responder.terminal (P := P))
          (Responder.parallel (Responder.terminal (P := Q))
            (Responder.terminal (P := R))))
        (parallelCoalgebra (Responder.terminal (P := P))
          (Responder.parallel (Responder.terminal (P := Q))
            (Responder.terminal (P := R)))
          (Display.M (Display.responder S))
          (fun state =>
            Display.M (Display.responder T) state.1 ×
              Display.M (Display.responder U) state.2)
          (Display.Coalgebra.terminal (Display.responder S))
          (parallelCoalgebra (Responder.terminal (P := Q))
            (Responder.terminal (P := R))
            (Display.M (Display.responder T))
            (Display.M (Display.responder U))
            (Display.Coalgebra.terminal (Display.responder T))
            (Display.Coalgebra.terminal (Display.responder U))))) where
  toState state := (state.1.1, (state.1.2, state.2))
  toWitness _ witness := (witness.1.1, (witness.1.2, witness.2))
  map_step := by
    intro state witness
    rcases state with ⟨⟨left, middle⟩, right⟩
    rcases witness with ⟨⟨displayedLeft, displayedMiddle⟩,
      displayedRight⟩
    have hBase := behavior_eq_of_responderMap
      (Responder.reindex
        (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumAssoc P Q R))
        (Responder.parallel (Responder.terminal (P := P))
          (Responder.parallel (Responder.terminal (P := Q))
            (Responder.terminal (P := R)))))
      (Responder.parallel
        (Responder.parallel (Responder.terminal (P := P))
          (Responder.terminal (P := Q)))
        (Responder.terminal (P := R)))
      (fun state => (state.1.1, (state.1.2, state.2)))
      (by
        intro state operation
        rw [Responder.answer_reindex, runFree_ofLens]
        cases operation with
        | left operation => cases operation <;> rfl
        | right operation => rfl
        | both operation rightOperation => cases operation <;> rfl)
      (by
        intro state operation
        rw [Responder.next_reindex, runFree_ofLens]
        cases operation with
        | left operation => cases operation <;> rfl
        | right operation => rfl
        | both operation rightOperation => cases operation <;> rfl)
      ((left, middle), right)
    dsimp [verifiedTotalStep, VerifiedPresentationHom.totalMap]
    apply Sigma.ext_iff.mpr
    constructor
    · apply Sigma.ext_iff.mpr
      constructor
      · exact hBase
      · apply Function.hfunext rfl
        intro operation operation' hOperation
        cases hOperation
        apply Function.hfunext rfl
        intro contract contract' hContract
        cases hContract
        cases operation with
        | left operation => cases operation <;> rfl
        | right operation => rfl
        | both operation rightOperation => cases operation <;> rfl
    · apply Function.hfunext
      · apply congrArg
          (Display.mStep (Display.responder
            (Display.parallelSum (Display.parallelSum S T) U))).sigmaPFunctor.B
        apply Sigma.ext_iff.mpr
        constructor
        · exact hBase
        · apply Function.hfunext rfl
          intro operation operation' hOperation
          cases hOperation
          apply Function.hfunext rfl
          intro contract contract' hContract
          cases hContract
          cases operation with
          | left operation => cases operation <;> rfl
          | right operation => rfl
          | both operation rightOperation => cases operation <;> rfl
      · intro direction direction' hDirection
        cases hDirection
        rcases direction with ⟨⟨operation, trivialDirection⟩, contract⟩
        cases trivialDirection
        cases operation with
        | left operation => cases operation <;> rfl
        | right operation => rfl
        | both operation rightOperation => cases operation <;> rfl

/-- Present a raw right-associated parallel responder by terminalizing its
inner parallel component. -/
private def parallelAssocRightPresentationHom
    {R : PFunctor.{uA₃, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (U : Display.{uA₃, uB, uC₃, uD₃} R) :=
  VerifiedPresentationHom.parallel
    (VerifiedPresentationHom.id (S := S)
      (source := Responder.terminal (P := P))
      (SourceWitness := Display.M (Display.responder S))
      (displayedSource := Display.Coalgebra.terminal (Display.responder S)))
    (VerifiedPresentationHom.toTerminal (Display.parallelSum T U)
      (Responder.parallel (Responder.terminal (P := Q))
        (Responder.terminal (P := R)))
      (fun state => Display.M (Display.responder T) state.1 ×
        Display.M (Display.responder U) state.2)
      (parallelCoalgebra (Responder.terminal (P := Q))
        (Responder.terminal (P := R))
        (Display.M (Display.responder T))
        (Display.M (Display.responder U))
        (Display.Coalgebra.terminal (Display.responder T))
        (Display.Coalgebra.terminal (Display.responder U))))

/-- Present a raw left-associated parallel responder by terminalizing its
inner parallel component. -/
private def parallelAssocLeftPresentationHom
    {R : PFunctor.{uA₃, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (U : Display.{uA₃, uB, uC₃, uD₃} R) :=
  VerifiedPresentationHom.parallel
    (VerifiedPresentationHom.toTerminal (Display.parallelSum S T)
      (Responder.parallel (Responder.terminal (P := P))
        (Responder.terminal (P := Q)))
      (fun state => Display.M (Display.responder S) state.1 ×
        Display.M (Display.responder T) state.2)
      (parallelCoalgebra (Responder.terminal (P := P))
        (Responder.terminal (P := Q))
        (Display.M (Display.responder S))
        (Display.M (Display.responder T))
        (Display.Coalgebra.terminal (Display.responder S))
        (Display.Coalgebra.terminal (Display.responder T))))
    (VerifiedPresentationHom.id (S := U)
      (source := Responder.terminal (P := R))
      (SourceWitness := Display.M (Display.responder U))
      (displayedSource := Display.Coalgebra.terminal (Display.responder U)))

/-- Verified parallel behavior associates after the single canonical
transport along the ordinary associator law. -/
theorem mapVerifiedBehavior_parallel_assoc
    {R : PFunctor.{uA₃, uB}}
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (U : Display.{uA₃, uB, uC₃, uD₃} R)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (middle : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedMiddle : Display.M (Display.responder T) middle)
    (right : PFunctor.M (R ⊸ X.{uA₃, uB}))
    (displayedRight : Display.M (Display.responder U) right) :
    Display.M.transport (mapBehavior_parallel_assoc left middle right)
        (mapVerifiedBehavior (Display.Lens.parallelSumAssoc S T U)
          (parallelBehavior left (parallelBehavior middle right))
          (parallelVerifiedBehavior S (Display.parallelSum T U)
            left displayedLeft (parallelBehavior middle right)
            (parallelVerifiedBehavior T U middle displayedMiddle
              right displayedRight))) =
      parallelVerifiedBehavior (Display.parallelSum S T) U
        (parallelBehavior left middle)
        (parallelVerifiedBehavior S T left displayedLeft middle displayedMiddle)
        right displayedRight := by
  let pResponder := Responder.terminal (P := P)
  let qResponder := Responder.terminal (P := Q)
  let rResponder := Responder.terminal (P := R)
  let rawRight := Responder.parallel pResponder
    (Responder.parallel qResponder rResponder)
  let rawLeft := Responder.parallel
    (Responder.parallel pResponder qResponder) rResponder
  let rawRightWitness := fun state :
      PFunctor.M (P ⊸ X.{uA₁, uB}) ×
        (PFunctor.M (Q ⊸ X.{uA₂, uB}) ×
          PFunctor.M (R ⊸ X.{uA₃, uB})) =>
    Display.M (Display.responder S) state.1 ×
      (Display.M (Display.responder T) state.2.1 ×
        Display.M (Display.responder U) state.2.2)
  let rawLeftWitness := fun state :
      (PFunctor.M (P ⊸ X.{uA₁, uB}) ×
        PFunctor.M (Q ⊸ X.{uA₂, uB})) ×
          PFunctor.M (R ⊸ X.{uA₃, uB}) =>
    (Display.M (Display.responder S) state.1.1 ×
      Display.M (Display.responder T) state.1.2) ×
        Display.M (Display.responder U) state.2
  let displayedRawRight := parallelCoalgebra pResponder
    (Responder.parallel qResponder rResponder)
    (Display.M (Display.responder S))
    (fun state => Display.M (Display.responder T) state.1 ×
      Display.M (Display.responder U) state.2)
    (Display.Coalgebra.terminal (Display.responder S))
    (parallelCoalgebra qResponder rResponder
      (Display.M (Display.responder T))
      (Display.M (Display.responder U))
      (Display.Coalgebra.terminal (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder U)))
  let displayedRawLeft := parallelCoalgebra
    (Responder.parallel pResponder qResponder) rResponder
    (fun state => Display.M (Display.responder S) state.1 ×
      Display.M (Display.responder T) state.2)
    (Display.M (Display.responder U))
    (parallelCoalgebra pResponder qResponder
      (Display.M (Display.responder S))
      (Display.M (Display.responder T))
      (Display.Coalgebra.terminal (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder T)))
    (Display.Coalgebra.terminal (Display.responder U))
  let sourceDisplayed := parallelVerifiedBehavior S
    (Display.parallelSum T U) left displayedLeft
    (parallelBehavior middle right)
    (parallelVerifiedBehavior T U middle displayedMiddle right displayedRight)
  let rawRightDisplayed := verifiedBehavior
    (Display.parallelSum S (Display.parallelSum T U))
    rawRight rawRightWitness displayedRawRight
    (left, (middle, right))
    (displayedLeft, (displayedMiddle, displayedRight))
  let rawLeftDisplayed := verifiedBehavior
    (Display.parallelSum (Display.parallelSum S T) U)
    rawLeft rawLeftWitness displayedRawLeft
    ((left, middle), right)
    ((displayedLeft, displayedMiddle), displayedRight)
  let publicLeftDisplayed := parallelVerifiedBehavior
    (Display.parallelSum S T) U (parallelBehavior left middle)
    (parallelVerifiedBehavior S T left displayedLeft middle displayedMiddle)
    right displayedRight
  let rightEq :=
    (parallelAssocRightPresentationHom S T U).behavior_eq
      (left, (middle, right))
      (displayedLeft, (displayedMiddle, displayedRight))
  have hRight : Display.M.transport rightEq sourceDisplayed =
      rawRightDisplayed := by
    have h := (parallelAssocRightPresentationHom S T U).verifiedBehavior_naturality
        (left, (middle, right))
        (displayedLeft, (displayedMiddle, displayedRight))
    change Display.M.transport _ sourceDisplayed = rawRightDisplayed at h
    exact (Display.M.transport_proof_irrel rightEq _ sourceDisplayed).trans h
  let mappedPublic := mapVerifiedBehavior
    (Display.Lens.parallelSumAssoc S T U) _ sourceDisplayed
  let mappedRawInput := mapVerifiedBehavior
    (Display.Lens.parallelSumAssoc S T U) _ rawRightDisplayed
  let mappedRightEq := congrArg
    (mapBehavior (PFunctor.Lens.parallelSumAssoc P Q R)) rightEq
  have hMappedRight : Display.M.transport mappedRightEq mappedPublic =
      mappedRawInput := by
    calc
      _ = mapVerifiedBehavior (Display.Lens.parallelSumAssoc S T U) _
          (Display.M.transport rightEq sourceDisplayed) :=
        mapVerifiedBehavior_transport
          (Display.Lens.parallelSumAssoc S T U) rightEq sourceDisplayed
      _ = mappedRawInput := congrArg
        (mapVerifiedBehavior (Display.Lens.parallelSumAssoc S T U) _)
        hRight
  let handler := PFunctor.Handler.ofLens
    (PFunctor.Lens.parallelSumAssoc P Q R)
  let presentationEq := reindexBehavior_behavior handler rawRight
    (left, (middle, right))
  let rawMapped := verifiedBehavior
    (Display.parallelSum (Display.parallelSum S T) U)
    (Responder.reindex handler rawRight) rawRightWitness
    (Responder.reindexCoalgebra
      (Display.parallelSum (Display.parallelSum S T) U)
      (Display.parallelSum S (Display.parallelSum T U)) handler
      (Display.Lens.parallelSumAssoc S T U).toHandler
      rawRight displayedRawRight)
    (left, (middle, right))
    (displayedLeft, (displayedMiddle, displayedRight))
  have hPresentation : Display.M.transport presentationEq mappedRawInput =
      rawMapped := by
    exact reindexVerifiedBehavior_verifiedBehavior handler
      (Display.Lens.parallelSumAssoc S T U).toHandler rawRight
      rawRightWitness displayedRawRight _ _
  let rawEq := (parallelAssocVerifiedPresentationHom S T U).behavior_eq
    ((left, middle), right)
    ((displayedLeft, displayedMiddle), displayedRight)
  have hRaw : Display.M.transport rawEq rawMapped = rawLeftDisplayed := by
    have h := (parallelAssocVerifiedPresentationHom S T U).verifiedBehavior_naturality
        ((left, middle), right)
        ((displayedLeft, displayedMiddle), displayedRight)
    change Display.M.transport _ rawMapped = rawLeftDisplayed at h
    exact (Display.M.transport_proof_irrel rawEq _ rawMapped).trans h
  let leftEq :=
    (parallelAssocLeftPresentationHom S T U).behavior_eq
      ((left, middle), right)
      ((displayedLeft, displayedMiddle), displayedRight)
  have hLeft : Display.M.transport leftEq publicLeftDisplayed =
      rawLeftDisplayed := by
    have h := (parallelAssocLeftPresentationHom S T U).verifiedBehavior_naturality
        ((left, middle), right)
        ((displayedLeft, displayedMiddle), displayedRight)
    change Display.M.transport _ publicLeftDisplayed = rawLeftDisplayed at h
    exact (Display.M.transport_proof_irrel leftEq _ publicLeftDisplayed).trans h
  have hRawToPublic : Display.M.transport leftEq.symm rawLeftDisplayed =
      publicLeftDisplayed := by
    calc
      _ = Display.M.transport leftEq.symm
          (Display.M.transport leftEq publicLeftDisplayed) :=
        congrArg (Display.M.transport leftEq.symm) hLeft.symm
      _ = _ := Display.M.transport_symm_transport leftEq publicLeftDisplayed
  let chainEq := (((mappedRightEq.trans presentationEq).trans rawEq).trans
    leftEq.symm)
  have hChain : Display.M.transport chainEq mappedPublic =
      publicLeftDisplayed := by
    calc
      _ = Display.M.transport leftEq.symm
          (Display.M.transport ((mappedRightEq.trans presentationEq).trans rawEq)
            mappedPublic) :=
        (Display.M.transport_trans
          ((mappedRightEq.trans presentationEq).trans rawEq)
          leftEq.symm mappedPublic).symm
      _ = Display.M.transport leftEq.symm
          (Display.M.transport rawEq
            (Display.M.transport (mappedRightEq.trans presentationEq)
              mappedPublic)) :=
        congrArg (Display.M.transport leftEq.symm)
          (Display.M.transport_trans (mappedRightEq.trans presentationEq)
            rawEq mappedPublic).symm
      _ = Display.M.transport leftEq.symm
          (Display.M.transport rawEq
            (Display.M.transport presentationEq
              (Display.M.transport mappedRightEq mappedPublic))) :=
        congrArg (fun displayed =>
          Display.M.transport leftEq.symm
            (Display.M.transport rawEq displayed))
          (Display.M.transport_trans mappedRightEq presentationEq
            mappedPublic).symm
      _ = Display.M.transport leftEq.symm
          (Display.M.transport rawEq
            (Display.M.transport presentationEq mappedRawInput)) := by
        exact congrArg (fun displayed =>
          Display.M.transport leftEq.symm
            (Display.M.transport rawEq
              (Display.M.transport presentationEq displayed))) hMappedRight
      _ = Display.M.transport leftEq.symm
          (Display.M.transport rawEq rawMapped) := by
        exact congrArg (fun displayed =>
          Display.M.transport leftEq.symm
            (Display.M.transport rawEq displayed)) hPresentation
      _ = Display.M.transport leftEq.symm rawLeftDisplayed := by
        exact congrArg (Display.M.transport leftEq.symm) hRaw
      _ = publicLeftDisplayed := hRawToPublic
  exact (Display.M.transport_proof_irrel
    (mapBehavior_parallel_assoc left middle right) chainEq mappedPublic).trans
    hChain

end Responder
end PFunctor
