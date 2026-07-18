/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Lens
public import PolyFun.PFunctor.Dynamical.Responder.VerifiedPresentation

/-!
# Reindexing state-free responder behavior by polynomial lenses

Polynomial lenses embed as one-operation free handlers. This module specializes
ordinary and verified state-free handler reindexing to that one-step layer,
with exact postcondition and continuation equations.
-/

@[expose] public section

universe uA₁ uA₂ uA₃ uB₁ uB₂ uB₃ uC₁ uD₁ uC₂ uD₂ uC₃ uD₃

namespace PFunctor
namespace Responder

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}

theorem runFree_ofLens {State : Type uA₃}
    (R : Responder State Q) (f : PFunctor.Lens P Q)
    (state : State) (operation : P.A) :
    R.runFree (PFunctor.Handler.ofLens f operation) state =
      (f.toFunB operation (R.answer state (f.toFunA operation)),
        R.next state (f.toFunA operation)) :=
  rfl

/-- Executing the displayed handler induced by a displayed lens performs one
target observation and maps its postcondition evidence back through the
displayed lens. -/
@[simp] theorem runFreeDisplayed_ofLens
    {S : Display.{uA₁, uB₁, uC₁, uD₁} P}
    {T : Display.{uA₂, uB₂, uC₂, uD₂} Q}
    {f : PFunctor.Lens P Q}
    (df : Display.Lens S T f)
    (behavior : PFunctor.M (Q ⊸ X.{uA₂, uB₂}))
    (displayedBehavior : Display.M (Display.responder T) behavior)
    (operation : P.A) (contract : S.position operation) :
    runFreeDisplayed T (Responder.terminal (P := Q))
        (Display.Coalgebra.terminal (Display.responder T))
        (df.toHandler operation contract)
        behavior displayedBehavior =
      ⟨df.toDirection operation contract
          ((Responder.terminal (P := Q)).answer behavior
            (f.toFunA operation))
          (appD T displayedBehavior (f.toFunA operation)
            (df.toPosition operation contract)).1,
        (appD T displayedBehavior (f.toFunA operation)
          (df.toPosition operation contract)).2⟩ := by
  rfl

/-- Reindex a state-free behavior along a one-step polynomial lens. -/
def mapBehavior (f : PFunctor.Lens P Q)
    (behavior : PFunctor.M (Q ⊸ X.{uA₂, uB₂})) :
    PFunctor.M (P ⊸ X.{uA₁, uB₁}) :=
  reindexBehavior (PFunctor.Handler.ofLens f) behavior

@[simp] theorem mapBehavior_id
    (behavior : PFunctor.M (P ⊸ X.{uA₁, uB₁})) :
    mapBehavior (PFunctor.Lens.id P) behavior = behavior := by
  unfold mapBehavior
  rw [PFunctor.Handler.ofLens_id, reindexBehavior_id]

/-- One-step behavior reindexing respects lens composition. -/
theorem mapBehavior_comp
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
    {R : PFunctor.{uA₃, uB₃}}
    (first : PFunctor.Lens P Q) (second : PFunctor.Lens Q R)
    (behavior : PFunctor.M (R ⊸ X.{uA₃, uB₃})) :
    mapBehavior first (mapBehavior second behavior) =
      mapBehavior (second ∘ₗ first) behavior := by
  unfold mapBehavior
  rw [reindexBehavior_comp, ← PFunctor.Handler.ofLens_comp]

/-- Reindex verified state-free behavior along a displayed polynomial lens. -/
def mapVerifiedBehavior
    {S : Display.{uA₁, uB₁, uC₁, uD₁} P}
    {T : Display.{uA₂, uB₂, uC₂, uD₂} Q}
    {f : PFunctor.Lens P Q}
    (df : Display.Lens S T f)
    (behavior : PFunctor.M (Q ⊸ X.{uA₂, uB₂}))
    (displayedBehavior : Display.M (Display.responder T) behavior) :
    Display.M (Display.responder S) (mapBehavior f behavior) :=
  reindexVerifiedBehavior S T (PFunctor.Handler.ofLens f)
    (df.toHandler) behavior displayedBehavior

/-- Reindexing verified behavior commutes with transport of the underlying
ordinary behavior. -/
theorem mapVerifiedBehavior_transport
    {R : PFunctor.{uA₂, uB₂}}
    {S : Display.{uA₁, uB₁, uC₁, uD₁} P}
    {T : Display.{uA₂, uB₂, uC₂, uD₂} R}
    {f : PFunctor.Lens P R} (df : Display.Lens S T f)
    {first second : PFunctor.M (R ⊸ X.{uA₂, uB₂})}
    (h : first = second) (displayed : Display.M (Display.responder T) first) :
    Display.M.transport (congrArg (mapBehavior f) h)
        (mapVerifiedBehavior df first displayed) =
      mapVerifiedBehavior df second (Display.M.transport h displayed) := by
  cases h
  rw [Display.M.transport_rfl, Display.M.transport_rfl]

/-- Verified one-step behavior reindexing preserves the identity lens, after
the canonical equality of the underlying ordinary behaviors. -/
@[simp] theorem mapVerifiedBehavior_id
    {S : Display.{uA₁, uB₁, uC₁, uD₁} P}
    (behavior : PFunctor.M (P ⊸ X.{uA₁, uB₁}))
    (displayedBehavior : Display.M (Display.responder S) behavior) :
    Display.M.transport (mapBehavior_id behavior)
        (mapVerifiedBehavior (Display.Lens.id S)
          behavior displayedBehavior) =
      displayedBehavior :=
  reindexVerifiedBehavior_id S behavior displayedBehavior

/-- Verified one-step behavior reindexing respects lens composition, with a
single transport along the ordinary behavior-composition law. -/
theorem mapVerifiedBehavior_comp
    {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
    {R : PFunctor.{uA₃, uB₃}}
    {S : Display.{uA₁, uB₁, uC₁, uD₁} P}
    {T : Display.{uA₂, uB₁, uC₂, uD₂} Q}
    {U : Display.{uA₃, uB₃, uC₃, uD₃} R}
    {firstBase : PFunctor.Lens P Q}
    {secondBase : PFunctor.Lens Q R}
    (first : Display.Lens S T firstBase)
    (second : Display.Lens T U secondBase)
    (behavior : PFunctor.M (R ⊸ X.{uA₃, uB₃}))
    (displayedBehavior : Display.M (Display.responder U) behavior) :
    Display.M.transport (mapBehavior_comp firstBase secondBase behavior)
        (mapVerifiedBehavior first (mapBehavior secondBase behavior)
          (mapVerifiedBehavior second behavior displayedBehavior)) =
      mapVerifiedBehavior (Display.Lens.comp second first)
        behavior displayedBehavior := by
  let firstHandler := PFunctor.Handler.ofLens firstBase
  let secondHandler := PFunctor.Handler.ofLens secondBase
  let compositeHandler := PFunctor.Handler.ofLens (secondBase ∘ₗ firstBase)
  let kleisliHandler := secondHandler.comp firstHandler
  let handlerEq : compositeHandler = kleisliHandler :=
    PFunctor.Handler.ofLens_comp secondBase firstBase
  let nestedBehavior := reindexBehavior firstHandler
    (reindexBehavior secondHandler behavior)
  let compositeBehavior := reindexBehavior compositeHandler behavior
  let kleisliBehavior := reindexBehavior kleisliHandler behavior
  let nestedEq : nestedBehavior = kleisliBehavior :=
    reindexBehavior_comp secondHandler firstHandler behavior
  let handlerBehaviorEq : compositeBehavior = kleisliBehavior :=
    reindexBehavior_congr handlerEq behavior
  let desiredEq : nestedBehavior = compositeBehavior :=
    nestedEq.trans handlerBehaviorEq.symm
  rw [Display.M.transport_proof_irrel
    (mapBehavior_comp firstBase secondBase behavior) desiredEq]
  rw [← Display.M.transport_trans]
  change Display.M.transport handlerBehaviorEq.symm
      (Display.M.transport nestedEq
        (reindexVerifiedBehavior S T firstHandler first.toHandler
          (reindexBehavior secondHandler behavior)
          (reindexVerifiedBehavior T U secondHandler second.toHandler
            behavior displayedBehavior))) = _
  rw [reindexVerifiedBehavior_comp S T U
    secondHandler second.toHandler firstHandler first.toHandler
    behavior displayedBehavior]
  exact reindexVerifiedBehavior_congr S U handlerEq.symm
    (second.toHandler.comp first.toHandler)
    (Display.Lens.comp second first).toHandler
    (Display.Lens.toHandler_comp_symm second first)
    behavior displayedBehavior

theorem appD_mapVerifiedBehavior_post
    {S : Display.{uA₁, uB₁, uC₁, uD₁} P}
    {T : Display.{uA₂, uB₂, uC₂, uD₂} Q}
    {f : PFunctor.Lens P Q}
    (df : Display.Lens S T f)
    (behavior : PFunctor.M (Q ⊸ X.{uA₂, uB₂}))
    (displayedBehavior : Display.M (Display.responder T) behavior)
    (operation : P.A) (contract : S.position operation) :
    (appD S (mapVerifiedBehavior df behavior displayedBehavior)
      operation contract).1 =
      df.toDirection operation contract
        ((Responder.terminal (P := Q)).answer behavior
          (f.toFunA operation))
        (appD T displayedBehavior (f.toFunA operation)
          (df.toPosition operation contract)).1 := by
  exact (appD_reindexVerifiedBehavior_post S T
    (PFunctor.Handler.ofLens f) (df.toHandler)
    behavior displayedBehavior operation contract).trans
      (congrArg Prod.fst
        (runFreeDisplayed_ofLens df behavior displayedBehavior
          operation contract))

theorem appD_mapVerifiedBehavior_next
    {S : Display.{uA₁, uB₁, uC₁, uD₁} P}
    {T : Display.{uA₂, uB₂, uC₂, uD₂} Q}
    {f : PFunctor.Lens P Q}
    (df : Display.Lens S T f)
    (behavior : PFunctor.M (Q ⊸ X.{uA₂, uB₂}))
    (displayedBehavior : Display.M (Display.responder T) behavior)
    (operation : P.A) (contract : S.position operation) :
    Display.M.transport
        (behavior_child
          (Responder.reindex (PFunctor.Handler.ofLens f)
            (Responder.terminal (P := Q))) behavior operation)
        (appD S (mapVerifiedBehavior df behavior displayedBehavior)
          operation contract).2 =
      mapVerifiedBehavior df
        ((Responder.terminal (P := Q)).runFree
          (PFunctor.Handler.ofLens f operation) behavior).2
        (appD T displayedBehavior (f.toFunA operation)
          (df.toPosition operation contract)).2 := by
  have h := appD_reindexVerifiedBehavior_next S T
    (PFunctor.Handler.ofLens f) (df.toHandler)
    behavior displayedBehavior operation contract
  rw [runFreeDisplayed_ofLens] at h
  unfold mapVerifiedBehavior mapBehavior
  exact h

end Responder
end PFunctor
