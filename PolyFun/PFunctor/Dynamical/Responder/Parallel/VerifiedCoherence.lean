/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder.Parallel.VerifiedAssociativity

/-!
# Proof-relevant coherence of verified parallel responder behavior

Verified presentation homomorphisms lift the ordinary parallel unit, symmetry,
and associativity laws to `Type`-valued displayed responder evidence. Internal
raw responder presentations are reconciled with the canonical state-free API;
only the canonical zero evidence and final transported laws are public.
-/

@[expose] public section

universe uA₁ uA₂ uA₃ uB uC₁ uD₁ uC₂ uD₂ uC₃ uD₃ uLift

namespace PFunctor
namespace Responder

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}


/-- The displayed braiding is a verified presentation homomorphism between
the two raw parallel responder presentations. -/
private def parallelCommVerifiedPresentationHom
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q) :
    VerifiedPresentationHom (Display.parallelSum S T)
      (Responder.parallel (Responder.terminal (P := P))
        (Responder.terminal (P := Q)))
      (fun state => Display.M (Display.responder S) state.1 ×
        Display.M (Display.responder T) state.2)
      (parallelCoalgebra (Responder.terminal (P := P))
        (Responder.terminal (P := Q))
        (Display.M (Display.responder S))
        (Display.M (Display.responder T))
        (Display.Coalgebra.terminal (Display.responder S))
        (Display.Coalgebra.terminal (Display.responder T)))
      (Responder.reindex
        (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumComm P Q))
        (Responder.parallel (Responder.terminal (P := Q))
          (Responder.terminal (P := P))))
      (fun state => Display.M (Display.responder T) state.1 ×
        Display.M (Display.responder S) state.2)
      (Responder.reindexCoalgebra (Display.parallelSum S T)
        (Display.parallelSum T S)
        (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumComm P Q))
        (Display.Lens.parallelSumComm S T).toHandler
        (Responder.parallel (Responder.terminal (P := Q))
          (Responder.terminal (P := P)))
        (parallelCoalgebra (Responder.terminal (P := Q))
          (Responder.terminal (P := P))
          (Display.M (Display.responder T))
          (Display.M (Display.responder S))
          (Display.Coalgebra.terminal (Display.responder T))
          (Display.Coalgebra.terminal (Display.responder S)))) where
  toState state := state.swap
  toWitness _ witness := witness.swap
  map_step := by
    intro state witness
    rcases state with ⟨left, right⟩
    rcases witness with ⟨displayedLeft, displayedRight⟩
    have hBase := behavior_eq_of_responderMap
      (Responder.reindex
        (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumComm P Q))
        (Responder.parallel (Responder.terminal (P := Q))
          (Responder.terminal (P := P))))
      (Responder.parallel (Responder.terminal (P := P))
        (Responder.terminal (P := Q)))
      Prod.swap
      (by
        intro state operation
        rw [Responder.answer_reindex, runFree_ofLens]
        cases operation <;> rfl)
      (by
        intro state operation
        rw [Responder.next_reindex, runFree_ofLens]
        cases operation <;> rfl)
      (left, right)
    dsimp [verifiedTotalStep, VerifiedPresentationHom.totalMap]
    apply verifiedTotalStepObj_ext _ _ _ hBase
    · apply Function.hfunext rfl
      intro operation operation' hOperation
      cases hOperation
      apply Function.hfunext rfl
      intro contract contract' hContract
      cases hContract
      cases operation <;> rfl
    · apply Function.hfunext
      · apply congrArg
          (Display.mStep
            (Display.responder (Display.parallelSum S T))).sigmaPFunctor.B
        apply Sigma.ext_iff.mpr
        constructor
        · exact hBase
        · apply Function.hfunext rfl
          intro operation operation' hOperation
          cases hOperation
          apply Function.hfunext rfl
          intro contract contract' hContract
          cases hContract
          cases operation <;> rfl
      · intro direction direction' hDirection
        cases hDirection
        rcases direction with ⟨⟨operation, trivialDirection⟩, contract⟩
        cases trivialDirection
        cases operation <;> rfl

private theorem verifiedBehavior_parallel_comm_presented
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right) :
    Display.M.transport
        ((parallelCommVerifiedPresentationHom S T).behavior_eq
          (left, right) (displayedLeft, displayedRight))
        (verifiedBehavior (Display.parallelSum S T)
          (Responder.reindex
            (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumComm P Q))
            (Responder.parallel (Responder.terminal (P := Q))
              (Responder.terminal (P := P))))
          (fun state => Display.M (Display.responder T) state.1 ×
            Display.M (Display.responder S) state.2)
          (Responder.reindexCoalgebra (Display.parallelSum S T)
            (Display.parallelSum T S)
            (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumComm P Q))
            (Display.Lens.parallelSumComm S T).toHandler
            (Responder.parallel (Responder.terminal (P := Q))
              (Responder.terminal (P := P)))
            (parallelCoalgebra (Responder.terminal (P := Q))
              (Responder.terminal (P := P))
              (Display.M (Display.responder T))
              (Display.M (Display.responder S))
              (Display.Coalgebra.terminal (Display.responder T))
              (Display.Coalgebra.terminal (Display.responder S))))
          (right, left) (displayedRight, displayedLeft)) =
      parallelVerifiedBehavior S T left displayedLeft right displayedRight := by
  exact (parallelCommVerifiedPresentationHom S T).verifiedBehavior_naturality
    (left, right) (displayedLeft, displayedRight)


/-- The unique proof-relevant coalgebra over the empty responder. -/
def zeroDisplayedCoalgebra :
    Display.Coalgebra
      (Display.responder (Display.zero :
        Display (0 : PFunctor.{uA₁, uB})))
      (Responder.zero : Responder PUnit.{1}
        (0 : PFunctor.{uA₁, uB})).out
      (fun _ => PUnit.{1}) :=
  (Display.responderCoalgebraEquiv
    (Display.zero : Display (0 : PFunctor.{uA₁, uB}))
    (Responder.zero : Responder PUnit.{1}
      (0 : PFunctor.{uA₁, uB}))
    (fun _ => PUnit.{1})).symm
    fun _ _ query => PEmpty.elim query

/-- Canonical verified behavior of the empty interface. -/
def zeroVerifiedBehavior :
    Display.M
      (Display.responder (Display.zero :
        Display (0 : PFunctor.{uA₁, uB})))
      ((Responder.zero : Responder PUnit.{1}
        (0 : PFunctor.{uA₁, uB})).behavior PUnit.unit) :=
  verifiedBehavior
    (Display.zero : Display (0 : PFunctor.{uA₁, uB}))
    (Responder.zero : Responder PUnit.{1}
      (0 : PFunctor.{uA₁, uB}))
    (fun _ => PUnit.{1}) zeroDisplayedCoalgebra PUnit.unit PUnit.unit

/-- The displayed right unitor is a verified presentation homomorphism
between raw responder presentations. -/
private def parallelZeroRightVerifiedPresentationHom
    (S : Display.{uA₁, uB, uC₁, uD₁} P) :
    VerifiedPresentationHom
      (Display.parallelSum S
        (Display.zero : Display (0 : PFunctor.{uA₂, uB})))
      (Responder.parallel (Responder.terminal (P := P))
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB})))
      (fun state => Display.M (Display.responder S) state.1 × PUnit)
      (parallelCoalgebra (Responder.terminal (P := P))
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB}))
        (Display.M (Display.responder S)) (fun _ => PUnit)
        (Display.Coalgebra.terminal (Display.responder S))
        zeroDisplayedCoalgebra)
      (Responder.reindex
        (PFunctor.Handler.ofLens
          (PFunctor.Lens.parallelSumZero P :
            PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P))
        (Responder.terminal (P := P)))
      (Display.M (Display.responder S))
      (Responder.reindexCoalgebra
        (Display.parallelSum S
          (Display.zero : Display (0 : PFunctor.{uA₂, uB}))) S
        (PFunctor.Handler.ofLens
          (PFunctor.Lens.parallelSumZero P :
            PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P))
        (Display.Lens.parallelSumZero S).toHandler
        (Responder.terminal (P := P))
        (Display.Coalgebra.terminal (Display.responder S))) where
  toState state := state.1
  toWitness _ witness := witness.1
  map_step := by
    intro state witness
    rcases state with ⟨left, emptyState⟩
    rcases emptyState with ⟨⟩
    rcases witness with ⟨displayedLeft, emptyWitness⟩
    rcases emptyWitness with ⟨⟩
    have hBase := behavior_eq_of_responderMap
      (Responder.reindex
        (PFunctor.Handler.ofLens
          (PFunctor.Lens.parallelSumZero P :
            PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P))
        (Responder.terminal (P := P)))
      (Responder.parallel (Responder.terminal (P := P))
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB})))
      Prod.fst
      (by
        intro state operation
        rw [Responder.answer_reindex, runFree_ofLens]
        cases operation with
        | left operation => rfl
        | right impossible => exact PEmpty.elim impossible
        | both operation impossible => exact PEmpty.elim impossible)
      (by
        intro state operation
        rw [Responder.next_reindex, runFree_ofLens]
        cases operation with
        | left operation => rfl
        | right impossible => exact PEmpty.elim impossible
        | both operation impossible => exact PEmpty.elim impossible)
      (left, PUnit.unit)
    dsimp [verifiedTotalStep, VerifiedPresentationHom.totalMap]
    apply verifiedTotalStepObj_ext _ _ _ hBase
    · apply Function.hfunext rfl
      intro operation operation' hOperation
      cases hOperation
      apply Function.hfunext rfl
      intro contract contract' hContract
      cases hContract
      cases operation with
      | left operation => rfl
      | right impossible => exact PEmpty.elim impossible
      | both operation impossible => exact PEmpty.elim impossible
    · apply Function.hfunext
      · apply congrArg
          (Display.mStep (Display.responder
            (Display.parallelSum S
              (Display.zero : Display
                (0 : PFunctor.{uA₂, uB}))))).sigmaPFunctor.B
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
          | left operation => rfl
          | right impossible => exact PEmpty.elim impossible
          | both operation impossible => exact PEmpty.elim impossible
      · intro direction direction' hDirection
        cases hDirection
        rcases direction with ⟨⟨operation, trivialDirection⟩, contract⟩
        cases trivialDirection
        cases operation with
        | left operation => rfl
        | right impossible => exact PEmpty.elim impossible
        | both operation impossible => exact PEmpty.elim impossible

private theorem verifiedBehavior_parallel_zero_right_presented
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left) :
    Display.M.transport
        ((parallelZeroRightVerifiedPresentationHom S).behavior_eq
          (left, PUnit.unit) (displayedLeft, PUnit.unit))
        (verifiedBehavior
          (Display.parallelSum S
            (Display.zero : Display (0 : PFunctor.{uA₂, uB})))
          (Responder.reindex
            (PFunctor.Handler.ofLens
              (PFunctor.Lens.parallelSumZero P :
                PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P))
            (Responder.terminal (P := P)))
          (Display.M (Display.responder S))
          (Responder.reindexCoalgebra
            (Display.parallelSum S
              (Display.zero : Display (0 : PFunctor.{uA₂, uB}))) S
            (PFunctor.Handler.ofLens
              (PFunctor.Lens.parallelSumZero P :
                PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P))
            (Display.Lens.parallelSumZero S).toHandler
            (Responder.terminal (P := P))
            (Display.Coalgebra.terminal (Display.responder S)))
          left displayedLeft) =
      verifiedBehavior
        (Display.parallelSum S
          (Display.zero : Display (0 : PFunctor.{uA₂, uB})))
        (Responder.parallel (Responder.terminal (P := P))
          (Responder.zero : Responder PUnit.{1}
            (0 : PFunctor.{uA₂, uB})))
        (fun state => Display.M (Display.responder S) state.1 × PUnit)
        (parallelCoalgebra (Responder.terminal (P := P))
          (Responder.zero : Responder PUnit.{1}
            (0 : PFunctor.{uA₂, uB}))
          (Display.M (Display.responder S)) (fun _ => PUnit)
          (Display.Coalgebra.terminal (Display.responder S))
          zeroDisplayedCoalgebra)
        (left, PUnit.unit) (displayedLeft, PUnit.unit) := by
  exact (parallelZeroRightVerifiedPresentationHom S).verifiedBehavior_naturality
    (left, PUnit.unit) (displayedLeft, PUnit.unit)

/-- Replacing the operational presentation of the empty responder by its
terminal state-free presentation preserves the complete verified parallel
step.  This is the second presentation map needed by the public right-unit
law: `parallelVerifiedBehavior` uses terminal presentations on both sides,
whereas `parallelZeroRightVerifiedPresentationHom` deliberately exposes the raw
empty responder. -/
private def parallelZeroRightPresentationHom
    (S : Display.{uA₁, uB, uC₁, uD₁} P) :
    VerifiedPresentationHom
      (Display.parallelSum S
        (Display.zero : Display (0 : PFunctor.{uA₂, uB})))
      (Responder.parallel (Responder.terminal (P := P))
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB})))
      (fun state => Display.M (Display.responder S) state.1 × PUnit)
      (parallelCoalgebra (Responder.terminal (P := P))
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB}))
        (Display.M (Display.responder S)) (fun _ => PUnit)
        (Display.Coalgebra.terminal (Display.responder S))
        zeroDisplayedCoalgebra)
      (Responder.parallel (Responder.terminal (P := P))
        (Responder.terminal (P := (0 : PFunctor.{uA₂, uB}))))
      (fun state => Display.M (Display.responder S) state.1 ×
        Display.M
          (Display.responder
            (Display.zero : Display (0 : PFunctor.{uA₂, uB})))
          state.2)
      (parallelCoalgebra (Responder.terminal (P := P))
        (Responder.terminal (P := (0 : PFunctor.{uA₂, uB})))
        (Display.M (Display.responder S))
        (Display.M
          (Display.responder
            (Display.zero : Display (0 : PFunctor.{uA₂, uB}))))
        (Display.Coalgebra.terminal (Display.responder S))
        (Display.Coalgebra.terminal
          (Display.responder
            (Display.zero : Display (0 : PFunctor.{uA₂, uB}))))) where
  toState state := (state.1,
    (Responder.zero : Responder PUnit.{1}
      (0 : PFunctor.{uA₂, uB})).behavior state.2)
  toWitness _ witness := (witness.1, zeroVerifiedBehavior)
  map_step := by
    intro state witness
    rcases state with ⟨left, emptyState⟩
    rcases emptyState with ⟨⟩
    rcases witness with ⟨displayedLeft, emptyWitness⟩
    rcases emptyWitness with ⟨⟩
    have hBase := behavior_eq_of_responderMap
      (Responder.parallel (Responder.terminal (P := P))
        (Responder.terminal (P := (0 : PFunctor.{uA₂, uB}))))
      (Responder.parallel (Responder.terminal (P := P))
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB})))
      (fun state => (state.1,
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB})).behavior state.2))
      (by
        intro state operation
        cases operation with
        | left operation => rfl
        | right impossible => exact PEmpty.elim impossible
        | both operation impossible => exact PEmpty.elim impossible)
      (by
        intro state operation
        cases operation with
        | left operation => rfl
        | right impossible => exact PEmpty.elim impossible
        | both operation impossible => exact PEmpty.elim impossible)
      (left, PUnit.unit)
    dsimp [verifiedTotalStep, VerifiedPresentationHom.totalMap]
    apply verifiedTotalStepObj_ext _ _ _ hBase
    · apply Function.hfunext rfl
      intro operation operation' hOperation
      cases hOperation
      apply Function.hfunext rfl
      intro contract contract' hContract
      cases hContract
      cases operation with
      | left operation => rfl
      | right impossible => exact PEmpty.elim impossible
      | both operation impossible => exact PEmpty.elim impossible
    · apply Function.hfunext
      · apply congrArg
          (Display.mStep (Display.responder
            (Display.parallelSum S
              (Display.zero : Display
                (0 : PFunctor.{uA₂, uB}))))).sigmaPFunctor.B
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
          | left operation => rfl
          | right impossible => exact PEmpty.elim impossible
          | both operation impossible => exact PEmpty.elim impossible
      · intro direction direction' hDirection
        cases hDirection
        rcases direction with ⟨⟨operation, trivialDirection⟩, contract⟩
        cases trivialDirection
        cases operation with
        | left operation => rfl
        | right impossible => exact PEmpty.elim impossible
        | both operation impossible => exact PEmpty.elim impossible

private theorem verifiedBehavior_parallel_zero_right_presentation
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left) :
    Display.M.transport
        ((parallelZeroRightPresentationHom S).behavior_eq
          (left, PUnit.unit) (displayedLeft, PUnit.unit))
        (parallelVerifiedBehavior S
          (Display.zero : Display (0 : PFunctor.{uA₂, uB}))
          left displayedLeft
          ((Responder.zero : Responder PUnit.{1}
            (0 : PFunctor.{uA₂, uB})).behavior PUnit.unit)
          zeroVerifiedBehavior) =
      verifiedBehavior
        (Display.parallelSum S
          (Display.zero : Display (0 : PFunctor.{uA₂, uB})))
        (Responder.parallel (Responder.terminal (P := P))
          (Responder.zero : Responder PUnit.{1}
            (0 : PFunctor.{uA₂, uB})))
        (fun state => Display.M (Display.responder S) state.1 × PUnit)
        (parallelCoalgebra (Responder.terminal (P := P))
          (Responder.zero : Responder PUnit.{1}
            (0 : PFunctor.{uA₂, uB}))
          (Display.M (Display.responder S)) (fun _ => PUnit)
          (Display.Coalgebra.terminal (Display.responder S))
          zeroDisplayedCoalgebra)
        (left, PUnit.unit) (displayedLeft, PUnit.unit) := by
  exact (parallelZeroRightPresentationHom S).verifiedBehavior_naturality
    (left, PUnit.unit) (displayedLeft, PUnit.unit)

/-- The displayed left unitor as a verified map between raw responder
presentations. -/
private def parallelZeroLeftVerifiedPresentationHom
    (S : Display.{uA₁, uB, uC₁, uD₁} P) :
    VerifiedPresentationHom
      (Display.parallelSum
        (Display.zero : Display (0 : PFunctor.{uA₂, uB})) S)
      (Responder.parallel
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB}))
        (Responder.terminal (P := P)))
      (fun state => PUnit × Display.M (Display.responder S) state.2)
      (parallelCoalgebra
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB}))
        (Responder.terminal (P := P))
        (fun _ => PUnit) (Display.M (Display.responder S))
        zeroDisplayedCoalgebra
        (Display.Coalgebra.terminal (Display.responder S)))
      (Responder.reindex
        (PFunctor.Handler.ofLens
          (PFunctor.Lens.zeroParallelSum P :
            PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P))
        (Responder.terminal (P := P)))
      (Display.M (Display.responder S))
      (Responder.reindexCoalgebra
        (Display.parallelSum
          (Display.zero : Display (0 : PFunctor.{uA₂, uB})) S) S
        (PFunctor.Handler.ofLens
          (PFunctor.Lens.zeroParallelSum P :
            PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P))
        (Display.Lens.zeroParallelSum S).toHandler
        (Responder.terminal (P := P))
        (Display.Coalgebra.terminal (Display.responder S))) where
  toState state := state.2
  toWitness _ witness := witness.2
  map_step := by
    intro state witness
    rcases state with ⟨emptyState, right⟩
    rcases emptyState with ⟨⟩
    rcases witness with ⟨emptyWitness, displayedRight⟩
    rcases emptyWitness with ⟨⟩
    have hBase := behavior_eq_of_responderMap
      (Responder.reindex
        (PFunctor.Handler.ofLens
          (PFunctor.Lens.zeroParallelSum P :
            PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P))
        (Responder.terminal (P := P)))
      (Responder.parallel
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB}))
        (Responder.terminal (P := P)))
      Prod.snd
      (by
        intro state operation
        rw [Responder.answer_reindex, runFree_ofLens]
        cases operation with
        | left impossible => exact PEmpty.elim impossible
        | right operation => rfl
        | both impossible operation => exact PEmpty.elim impossible)
      (by
        intro state operation
        rw [Responder.next_reindex, runFree_ofLens]
        cases operation with
        | left impossible => exact PEmpty.elim impossible
        | right operation => rfl
        | both impossible operation => exact PEmpty.elim impossible)
      (PUnit.unit, right)
    dsimp [verifiedTotalStep, VerifiedPresentationHom.totalMap]
    apply verifiedTotalStepObj_ext _ _ _ hBase
    · apply Function.hfunext rfl
      intro operation operation' hOperation
      cases hOperation
      apply Function.hfunext rfl
      intro contract contract' hContract
      cases hContract
      cases operation with
      | left impossible => exact PEmpty.elim impossible
      | right operation => rfl
      | both impossible operation => exact PEmpty.elim impossible
    · apply Function.hfunext
      · apply congrArg
          (Display.mStep (Display.responder
            (Display.parallelSum
              (Display.zero : Display
                (0 : PFunctor.{uA₂, uB})) S))).sigmaPFunctor.B
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
          | left impossible => exact PEmpty.elim impossible
          | right operation => rfl
          | both impossible operation => exact PEmpty.elim impossible
      · intro direction direction' hDirection
        cases hDirection
        rcases direction with ⟨⟨operation, trivialDirection⟩, contract⟩
        cases trivialDirection
        cases operation with
        | left impossible => exact PEmpty.elim impossible
        | right operation => rfl
        | both impossible operation => exact PEmpty.elim impossible

private theorem verifiedBehavior_parallel_zero_left_presented
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (right : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedRight : Display.M (Display.responder S) right) :
    Display.M.transport
        ((parallelZeroLeftVerifiedPresentationHom S).behavior_eq
          (PUnit.unit, right) (PUnit.unit, displayedRight))
        (verifiedBehavior
          (Display.parallelSum
            (Display.zero : Display (0 : PFunctor.{uA₂, uB})) S)
          (Responder.reindex
            (PFunctor.Handler.ofLens
              (PFunctor.Lens.zeroParallelSum P :
                PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P))
            (Responder.terminal (P := P)))
          (Display.M (Display.responder S))
          (Responder.reindexCoalgebra
            (Display.parallelSum
              (Display.zero : Display (0 : PFunctor.{uA₂, uB})) S) S
            (PFunctor.Handler.ofLens
              (PFunctor.Lens.zeroParallelSum P :
                PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P))
            (Display.Lens.zeroParallelSum S).toHandler
            (Responder.terminal (P := P))
            (Display.Coalgebra.terminal (Display.responder S)))
          right displayedRight) =
      verifiedBehavior
        (Display.parallelSum
          (Display.zero : Display (0 : PFunctor.{uA₂, uB})) S)
        (Responder.parallel
          (Responder.zero : Responder PUnit.{1}
            (0 : PFunctor.{uA₂, uB}))
          (Responder.terminal (P := P)))
        (fun state => PUnit × Display.M (Display.responder S) state.2)
        (parallelCoalgebra
          (Responder.zero : Responder PUnit.{1}
            (0 : PFunctor.{uA₂, uB}))
          (Responder.terminal (P := P))
          (fun _ => PUnit) (Display.M (Display.responder S))
          zeroDisplayedCoalgebra
          (Display.Coalgebra.terminal (Display.responder S)))
        (PUnit.unit, right) (PUnit.unit, displayedRight) := by
  exact (parallelZeroLeftVerifiedPresentationHom S).verifiedBehavior_naturality
    (PUnit.unit, right) (PUnit.unit, displayedRight)

/-- Presentation change from the raw empty responder on the left to the
terminal empty behavior used by `parallelVerifiedBehavior`. -/
private def parallelZeroLeftPresentationHom
    (S : Display.{uA₁, uB, uC₁, uD₁} P) :
    VerifiedPresentationHom
      (Display.parallelSum
        (Display.zero : Display (0 : PFunctor.{uA₂, uB})) S)
      (Responder.parallel
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB}))
        (Responder.terminal (P := P)))
      (fun state => PUnit × Display.M (Display.responder S) state.2)
      (parallelCoalgebra
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB}))
        (Responder.terminal (P := P))
        (fun _ => PUnit) (Display.M (Display.responder S))
        zeroDisplayedCoalgebra
        (Display.Coalgebra.terminal (Display.responder S)))
      (Responder.parallel
        (Responder.terminal (P := (0 : PFunctor.{uA₂, uB})))
        (Responder.terminal (P := P)))
      (fun state =>
        Display.M
          (Display.responder
            (Display.zero : Display (0 : PFunctor.{uA₂, uB}))) state.1 ×
        Display.M (Display.responder S) state.2)
      (parallelCoalgebra
        (Responder.terminal (P := (0 : PFunctor.{uA₂, uB})))
        (Responder.terminal (P := P))
        (Display.M
          (Display.responder
            (Display.zero : Display (0 : PFunctor.{uA₂, uB}))))
        (Display.M (Display.responder S))
        (Display.Coalgebra.terminal
          (Display.responder
            (Display.zero : Display (0 : PFunctor.{uA₂, uB}))))
        (Display.Coalgebra.terminal (Display.responder S))) where
  toState state :=
    ((Responder.zero : Responder PUnit.{1}
      (0 : PFunctor.{uA₂, uB})).behavior state.1, state.2)
  toWitness _ witness := (zeroVerifiedBehavior, witness.2)
  map_step := by
    intro state witness
    rcases state with ⟨emptyState, right⟩
    rcases emptyState with ⟨⟩
    rcases witness with ⟨emptyWitness, displayedRight⟩
    rcases emptyWitness with ⟨⟩
    have hBase := behavior_eq_of_responderMap
      (Responder.parallel
        (Responder.terminal (P := (0 : PFunctor.{uA₂, uB})))
        (Responder.terminal (P := P)))
      (Responder.parallel
        (Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB}))
        (Responder.terminal (P := P)))
      (fun state =>
        ((Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB})).behavior state.1, state.2))
      (by
        intro state operation
        cases operation with
        | left impossible => exact PEmpty.elim impossible
        | right operation => rfl
        | both impossible operation => exact PEmpty.elim impossible)
      (by
        intro state operation
        cases operation with
        | left impossible => exact PEmpty.elim impossible
        | right operation => rfl
        | both impossible operation => exact PEmpty.elim impossible)
      (PUnit.unit, right)
    dsimp [verifiedTotalStep, VerifiedPresentationHom.totalMap]
    apply verifiedTotalStepObj_ext _ _ _ hBase
    · apply Function.hfunext rfl
      intro operation operation' hOperation
      cases hOperation
      apply Function.hfunext rfl
      intro contract contract' hContract
      cases hContract
      cases operation with
      | left impossible => exact PEmpty.elim impossible
      | right operation => rfl
      | both impossible operation => exact PEmpty.elim impossible
    · apply Function.hfunext
      · apply congrArg
          (Display.mStep (Display.responder
            (Display.parallelSum
              (Display.zero : Display
                (0 : PFunctor.{uA₂, uB})) S))).sigmaPFunctor.B
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
          | left impossible => exact PEmpty.elim impossible
          | right operation => rfl
          | both impossible operation => exact PEmpty.elim impossible
      · intro direction direction' hDirection
        cases hDirection
        rcases direction with ⟨⟨operation, trivialDirection⟩, contract⟩
        cases trivialDirection
        cases operation with
        | left impossible => exact PEmpty.elim impossible
        | right operation => rfl
        | both impossible operation => exact PEmpty.elim impossible

private theorem verifiedBehavior_parallel_zero_left_presentation
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (right : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedRight : Display.M (Display.responder S) right) :
    Display.M.transport
        ((parallelZeroLeftPresentationHom S).behavior_eq
          (PUnit.unit, right) (PUnit.unit, displayedRight))
        (parallelVerifiedBehavior
          (Display.zero : Display (0 : PFunctor.{uA₂, uB})) S
          ((Responder.zero : Responder PUnit.{1}
            (0 : PFunctor.{uA₂, uB})).behavior PUnit.unit)
          zeroVerifiedBehavior right displayedRight) =
      verifiedBehavior
        (Display.parallelSum
          (Display.zero : Display (0 : PFunctor.{uA₂, uB})) S)
        (Responder.parallel
          (Responder.zero : Responder PUnit.{1}
            (0 : PFunctor.{uA₂, uB}))
          (Responder.terminal (P := P)))
        (fun state => PUnit × Display.M (Display.responder S) state.2)
        (parallelCoalgebra
          (Responder.zero : Responder PUnit.{1}
            (0 : PFunctor.{uA₂, uB}))
          (Responder.terminal (P := P))
          (fun _ => PUnit) (Display.M (Display.responder S))
          zeroDisplayedCoalgebra
          (Display.Coalgebra.terminal (Display.responder S)))
        (PUnit.unit, right) (PUnit.unit, displayedRight) := by
  exact (parallelZeroLeftPresentationHom S).verifiedBehavior_naturality
      (PUnit.unit, right) (PUnit.unit, displayedRight)


/-- Verified parallel behavior is symmetric after the single canonical
transport along the ordinary braiding law. -/
theorem mapVerifiedBehavior_parallel_comm
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (T : Display.{uA₂, uB, uC₂, uD₂} Q)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left)
    (right : PFunctor.M (Q ⊸ X.{uA₂, uB}))
    (displayedRight : Display.M (Display.responder T) right) :
    Display.M.transport (mapBehavior_parallel_comm left right)
        (mapVerifiedBehavior (Display.Lens.parallelSumComm S T)
          (parallelBehavior right left)
          (parallelVerifiedBehavior T S right displayedRight
            left displayedLeft)) =
      parallelVerifiedBehavior S T left displayedLeft right displayedRight := by
  let swapped := Responder.parallel (Responder.terminal (P := Q))
    (Responder.terminal (P := P))
  let swappedWitness := fun state :
      PFunctor.M (Q ⊸ X.{uA₂, uB}) ×
        PFunctor.M (P ⊸ X.{uA₁, uB}) =>
    Display.M (Display.responder T) state.1 ×
      Display.M (Display.responder S) state.2
  let displayedSwapped := parallelCoalgebra
    (Responder.terminal (P := Q)) (Responder.terminal (P := P))
    (Display.M (Display.responder T))
    (Display.M (Display.responder S))
    (Display.Coalgebra.terminal (Display.responder T))
    (Display.Coalgebra.terminal (Display.responder S))
  let sourceDisplayed := parallelVerifiedBehavior T S right displayedRight
    left displayedLeft
  let mappedDisplayed := mapVerifiedBehavior
    (Display.Lens.parallelSumComm S T)
    (parallelBehavior right left) sourceDisplayed
  let rawMapped := verifiedBehavior (Display.parallelSum S T)
    (Responder.reindex
      (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumComm P Q)) swapped)
    swappedWitness
    (Responder.reindexCoalgebra (Display.parallelSum S T)
      (Display.parallelSum T S)
      (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumComm P Q))
      (Display.Lens.parallelSumComm S T).toHandler
      swapped displayedSwapped)
    (right, left) (displayedRight, displayedLeft)
  let presentationEq := reindexBehavior_behavior
    (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumComm P Q))
    swapped (right, left)
  have hPresentation :
      Display.M.transport presentationEq mappedDisplayed = rawMapped := by
    exact reindexVerifiedBehavior_verifiedBehavior
      (PFunctor.Handler.ofLens (PFunctor.Lens.parallelSumComm P Q))
      (Display.Lens.parallelSumComm S T).toHandler
      swapped swappedWitness displayedSwapped
      (right, left) (displayedRight, displayedLeft)
  let rawEq := (parallelCommVerifiedPresentationHom S T).behavior_eq
    (left, right) (displayedLeft, displayedRight)
  have hRaw : Display.M.transport rawEq rawMapped =
      parallelVerifiedBehavior S T left displayedLeft right displayedRight := by
    exact verifiedBehavior_parallel_comm_presented S T
      left displayedLeft right displayedRight
  have hChain :
      Display.M.transport (presentationEq.trans rawEq) mappedDisplayed =
        parallelVerifiedBehavior S T left displayedLeft right displayedRight := by
    calc
      Display.M.transport (presentationEq.trans rawEq) mappedDisplayed =
          Display.M.transport rawEq
            (Display.M.transport presentationEq mappedDisplayed) :=
        (Display.M.transport_trans presentationEq rawEq mappedDisplayed).symm
      _ = Display.M.transport rawEq rawMapped :=
        congrArg (Display.M.transport rawEq) hPresentation
      _ = _ := hRaw
  exact (Display.M.transport_proof_irrel
    (mapBehavior_parallel_comm left right)
    (presentationEq.trans rawEq) mappedDisplayed).trans hChain

/-- The empty displayed interface is a right unit for verified state-free
parallel behavior.  The statement exposes only the canonical ordinary
right-unitor equality; the proof factors through the raw empty-responder
presentation and discharges both presentation changes internally. -/
theorem mapVerifiedBehavior_parallel_zero_right
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (left : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedLeft : Display.M (Display.responder S) left) :
    Display.M.transport (mapBehavior_parallel_zero_right left)
        (mapVerifiedBehavior (Display.Lens.parallelSumZero S)
          left displayedLeft) =
      parallelVerifiedBehavior S
        (Display.zero : Display.{uA₂, uB, uC₂, uD₂}
          (0 : PFunctor.{uA₂, uB}))
        left displayedLeft
        ((Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB})).behavior PUnit.unit)
        zeroVerifiedBehavior := by
  let empty := (Responder.zero : Responder PUnit.{1}
    (0 : PFunctor.{uA₂, uB}))
  let raw := Responder.parallel (Responder.terminal (P := P)) empty
  let rawWitness := fun state :
      PFunctor.M (P ⊸ X.{uA₁, uB}) × PUnit =>
    Display.M (Display.responder S) state.1 × PUnit
  let displayedRaw := parallelCoalgebra
    (Responder.terminal (P := P)) empty
    (Display.M (Display.responder S)) (fun _ => PUnit)
    (Display.Coalgebra.terminal (Display.responder S))
    zeroDisplayedCoalgebra
  let mappedDisplayed := mapVerifiedBehavior
    (Display.Lens.parallelSumZero S) left displayedLeft
  let rawMapped := verifiedBehavior
    (Display.parallelSum S
      (Display.zero : Display.{uA₂, uB, uC₂, uD₂}
        (0 : PFunctor.{uA₂, uB})))
    (Responder.reindex
      (PFunctor.Handler.ofLens
        (PFunctor.Lens.parallelSumZero P :
          PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P))
      (Responder.terminal (P := P)))
    (Display.M (Display.responder S))
    (Responder.reindexCoalgebra
      (Display.parallelSum S
        (Display.zero : Display.{uA₂, uB, uC₂, uD₂}
          (0 : PFunctor.{uA₂, uB}))) S
      (PFunctor.Handler.ofLens
        (PFunctor.Lens.parallelSumZero P :
          PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P))
      (Display.Lens.parallelSumZero S).toHandler
      (Responder.terminal (P := P))
      (Display.Coalgebra.terminal (Display.responder S)))
    left displayedLeft
  let rawDisplayed := verifiedBehavior
    (Display.parallelSum S
      (Display.zero : Display.{uA₂, uB, uC₂, uD₂}
        (0 : PFunctor.{uA₂, uB})))
    raw rawWitness displayedRaw
    (left, PUnit.unit) (displayedLeft, PUnit.unit)
  let publicDisplayed := parallelVerifiedBehavior S
    (Display.zero : Display.{uA₂, uB, uC₂, uD₂}
      (0 : PFunctor.{uA₂, uB}))
    left displayedLeft (empty.behavior PUnit.unit) zeroVerifiedBehavior
  let presentationEq :
      mapBehavior
          (PFunctor.Lens.parallelSumZero P :
            PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P)
          left =
        (Responder.reindex
          (PFunctor.Handler.ofLens
            (PFunctor.Lens.parallelSumZero P :
              PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P))
          (Responder.terminal (P := P))).behavior left := by
    simpa only [mapBehavior, terminal_behavior] using
      reindexBehavior_behavior
        (PFunctor.Handler.ofLens
          (PFunctor.Lens.parallelSumZero P :
            PFunctor.Lens (P ∥ (0 : PFunctor.{uA₂, uB})) P))
        (Responder.terminal (P := P)) left
  have hPresentation :
      Display.M.transport presentationEq mappedDisplayed = rawMapped := by
    change Display.M.transport presentationEq mappedDisplayed =
      mappedDisplayed
    exact (Display.M.transport_proof_irrel presentationEq rfl
      mappedDisplayed).trans (Display.M.transport_rfl mappedDisplayed)
  let rawEq :=
    (parallelZeroRightVerifiedPresentationHom.{uA₁, uA₂, uB, uC₁, uD₁,
      uC₂, uD₂}
      S).behavior_eq
    (left, PUnit.unit) (displayedLeft, PUnit.unit)
  have hRaw : Display.M.transport rawEq rawMapped = rawDisplayed := by
    exact verifiedBehavior_parallel_zero_right_presented.{uA₁, uA₂, uB,
      uC₁, uD₁, uC₂, uD₂, 0, 0} S left displayedLeft
  let terminalEq :=
    (parallelZeroRightPresentationHom.{uA₁, uA₂, uB,
      uC₁, uD₁, uC₂, uD₂} S).behavior_eq
      (left, PUnit.unit) (displayedLeft, PUnit.unit)
  have hTerminal :
      Display.M.transport terminalEq publicDisplayed = rawDisplayed := by
    exact verifiedBehavior_parallel_zero_right_presentation.{uA₁, uA₂,
      uB, uC₁, uD₁, uC₂, uD₂, 0, 0} S left displayedLeft
  have hRawToPublic :
      Display.M.transport terminalEq.symm rawDisplayed = publicDisplayed := by
    calc
      Display.M.transport terminalEq.symm rawDisplayed =
          Display.M.transport terminalEq.symm
            (Display.M.transport terminalEq publicDisplayed) :=
        congrArg (Display.M.transport terminalEq.symm) hTerminal.symm
      _ = publicDisplayed :=
        Display.M.transport_symm_transport terminalEq publicDisplayed
  have hChain :
      Display.M.transport
          ((presentationEq.trans rawEq).trans terminalEq.symm)
          mappedDisplayed = publicDisplayed := by
    calc
      Display.M.transport
          ((presentationEq.trans rawEq).trans terminalEq.symm)
          mappedDisplayed =
          Display.M.transport terminalEq.symm
            (Display.M.transport (presentationEq.trans rawEq)
              mappedDisplayed) :=
        (Display.M.transport_trans (presentationEq.trans rawEq)
          terminalEq.symm mappedDisplayed).symm
      _ = Display.M.transport terminalEq.symm
          (Display.M.transport rawEq
            (Display.M.transport presentationEq mappedDisplayed)) :=
        congrArg (Display.M.transport terminalEq.symm)
          (Display.M.transport_trans presentationEq rawEq
            mappedDisplayed).symm
      _ = Display.M.transport terminalEq.symm
          (Display.M.transport rawEq rawMapped) :=
        congrArg (fun displayed =>
          Display.M.transport terminalEq.symm
            (Display.M.transport rawEq displayed)) hPresentation
      _ = Display.M.transport terminalEq.symm rawDisplayed :=
        congrArg (Display.M.transport terminalEq.symm) hRaw
      _ = publicDisplayed := hRawToPublic
  exact (Display.M.transport_proof_irrel
    (mapBehavior_parallel_zero_right left)
    ((presentationEq.trans rawEq).trans terminalEq.symm)
    mappedDisplayed).trans hChain

/-- The empty displayed interface is a left unit for verified state-free
parallel behavior. -/
theorem mapVerifiedBehavior_parallel_zero_left
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    (right : PFunctor.M (P ⊸ X.{uA₁, uB}))
    (displayedRight : Display.M (Display.responder S) right) :
    Display.M.transport (mapBehavior_parallel_zero_left right)
        (mapVerifiedBehavior (Display.Lens.zeroParallelSum S)
          right displayedRight) =
      parallelVerifiedBehavior
        (Display.zero : Display.{uA₂, uB, uC₂, uD₂}
          (0 : PFunctor.{uA₂, uB})) S
        ((Responder.zero : Responder PUnit.{1}
          (0 : PFunctor.{uA₂, uB})).behavior PUnit.unit)
        zeroVerifiedBehavior right displayedRight := by
  let empty := (Responder.zero : Responder PUnit.{1}
    (0 : PFunctor.{uA₂, uB}))
  let raw := Responder.parallel empty (Responder.terminal (P := P))
  let rawWitness := fun state :
      PUnit × PFunctor.M (P ⊸ X.{uA₁, uB}) =>
    PUnit × Display.M (Display.responder S) state.2
  let displayedRaw := parallelCoalgebra empty
    (Responder.terminal (P := P))
    (fun _ => PUnit) (Display.M (Display.responder S))
    zeroDisplayedCoalgebra
    (Display.Coalgebra.terminal (Display.responder S))
  let mappedDisplayed := mapVerifiedBehavior
    (Display.Lens.zeroParallelSum S) right displayedRight
  let rawMapped := verifiedBehavior
    (Display.parallelSum
      (Display.zero : Display.{uA₂, uB, uC₂, uD₂}
        (0 : PFunctor.{uA₂, uB})) S)
    (Responder.reindex
      (PFunctor.Handler.ofLens
        (PFunctor.Lens.zeroParallelSum P :
          PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P))
      (Responder.terminal (P := P)))
    (Display.M (Display.responder S))
    (Responder.reindexCoalgebra
      (Display.parallelSum
        (Display.zero : Display.{uA₂, uB, uC₂, uD₂}
          (0 : PFunctor.{uA₂, uB})) S) S
      (PFunctor.Handler.ofLens
        (PFunctor.Lens.zeroParallelSum P :
          PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P))
      (Display.Lens.zeroParallelSum S).toHandler
      (Responder.terminal (P := P))
      (Display.Coalgebra.terminal (Display.responder S)))
    right displayedRight
  let rawDisplayed := verifiedBehavior
    (Display.parallelSum
      (Display.zero : Display.{uA₂, uB, uC₂, uD₂}
        (0 : PFunctor.{uA₂, uB})) S)
    raw rawWitness displayedRaw
    (PUnit.unit, right) (PUnit.unit, displayedRight)
  let publicDisplayed := parallelVerifiedBehavior
    (Display.zero : Display.{uA₂, uB, uC₂, uD₂}
      (0 : PFunctor.{uA₂, uB})) S
    (empty.behavior PUnit.unit) zeroVerifiedBehavior right displayedRight
  let presentationEq :
      mapBehavior
          (PFunctor.Lens.zeroParallelSum P :
            PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P)
          right =
        (Responder.reindex
          (PFunctor.Handler.ofLens
            (PFunctor.Lens.zeroParallelSum P :
              PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P))
          (Responder.terminal (P := P))).behavior right := by
    simpa only [mapBehavior, terminal_behavior] using
      reindexBehavior_behavior
        (PFunctor.Handler.ofLens
          (PFunctor.Lens.zeroParallelSum P :
            PFunctor.Lens ((0 : PFunctor.{uA₂, uB}) ∥ P) P))
        (Responder.terminal (P := P)) right
  have hPresentation :
      Display.M.transport presentationEq mappedDisplayed = rawMapped := by
    change Display.M.transport presentationEq mappedDisplayed =
      mappedDisplayed
    exact (Display.M.transport_proof_irrel presentationEq rfl
      mappedDisplayed).trans (Display.M.transport_rfl mappedDisplayed)
  let rawEq :=
    (parallelZeroLeftVerifiedPresentationHom.{uA₁, uA₂, uB, uC₁, uD₁,
      uC₂, uD₂} S).behavior_eq
      (PUnit.unit, right) (PUnit.unit, displayedRight)
  have hRaw : Display.M.transport rawEq rawMapped = rawDisplayed := by
    exact verifiedBehavior_parallel_zero_left_presented.{uA₁, uA₂, uB,
      uC₁, uD₁, uC₂, uD₂, 0, 0} S right displayedRight
  let terminalEq :=
    (parallelZeroLeftPresentationHom.{uA₁, uA₂, uB,
      uC₁, uD₁, uC₂, uD₂} S).behavior_eq
      (PUnit.unit, right) (PUnit.unit, displayedRight)
  have hTerminal :
      Display.M.transport terminalEq publicDisplayed = rawDisplayed := by
    exact verifiedBehavior_parallel_zero_left_presentation.{uA₁, uA₂,
      uB, uC₁, uD₁, uC₂, uD₂, 0, 0} S right displayedRight
  have hRawToPublic :
      Display.M.transport terminalEq.symm rawDisplayed = publicDisplayed := by
    calc
      Display.M.transport terminalEq.symm rawDisplayed =
          Display.M.transport terminalEq.symm
            (Display.M.transport terminalEq publicDisplayed) :=
        congrArg (Display.M.transport terminalEq.symm) hTerminal.symm
      _ = publicDisplayed :=
        Display.M.transport_symm_transport terminalEq publicDisplayed
  have hChain :
      Display.M.transport
          ((presentationEq.trans rawEq).trans terminalEq.symm)
          mappedDisplayed = publicDisplayed := by
    calc
      Display.M.transport
          ((presentationEq.trans rawEq).trans terminalEq.symm)
          mappedDisplayed =
          Display.M.transport terminalEq.symm
            (Display.M.transport (presentationEq.trans rawEq)
              mappedDisplayed) :=
        (Display.M.transport_trans (presentationEq.trans rawEq)
          terminalEq.symm mappedDisplayed).symm
      _ = Display.M.transport terminalEq.symm
          (Display.M.transport rawEq
            (Display.M.transport presentationEq mappedDisplayed)) :=
        congrArg (Display.M.transport terminalEq.symm)
          (Display.M.transport_trans presentationEq rawEq
            mappedDisplayed).symm
      _ = Display.M.transport terminalEq.symm
          (Display.M.transport rawEq rawMapped) :=
        congrArg (fun displayed =>
          Display.M.transport terminalEq.symm
            (Display.M.transport rawEq displayed)) hPresentation
      _ = Display.M.transport terminalEq.symm rawDisplayed :=
        congrArg (Display.M.transport terminalEq.symm) hRaw
      _ = publicDisplayed := hRawToPublic
  exact (Display.M.transport_proof_irrel
    (mapBehavior_parallel_zero_left right)
    ((presentationEq.trans rawEq).trans terminalEq.symm)
    mappedDisplayed).trans hChain

end Responder
end PFunctor
