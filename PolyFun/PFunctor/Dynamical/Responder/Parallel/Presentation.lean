/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder.Presentation
public import PolyFun.PFunctor.Dynamical.Responder.Parallel.Behavior

/-!
# Parallel composition of displayed responder presentations

Displayed presentation homomorphisms compose componentwise under lockstep
parallel. This proof-relevant bifunctoriality is distinct from unrestricted
parallel composition of free handlers, which would require a Kleisli
interchange law.
-/

@[expose] public section

universe uA₁ uA₂ uA₃ uB uC₁ uD₁ uC₂ uD₂ uC₃ uD₃ uLift

namespace PFunctor
namespace Responder

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}

private theorem ulift_heq
    {A B : Type uC₁} {a : A} {b : B}
    (h : HEq a b) :
    HEq (ULift.up.{uLift, uC₁} a) (ULift.up.{uLift, uC₁} b) := by
  cases h
  rfl

private theorem prod_heq
    {A B : Type uC₁} {C D : Type uD₁}
    {a : A} {b : B} {c : C} {d : D}
    (h₁ : HEq a b) (h₂ : HEq c d) : HEq (a, c) (b, d) := by
  cases h₁
  cases h₂
  rfl

universe uS₁ uS₂ uT₁ uT₂ uI₁ uI₂ uJ₁ uJ₂ uK₁ uK₂ uL₁ uL₂

namespace PresentationHom

/-- Componentwise parallel composition of displayed presentation
homomorphisms. Unlike arbitrary free-handler parallel composition, this is
available without an interchange hypothesis: lockstep parallel combines the
two one-step coalgebra squares branchwise. -/
def parallel
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {SourceState₁ : Type uS₁} {SourceState₂ : Type uS₂}
    {TargetState₁ : Type uT₁} {TargetState₂ : Type uT₂}
    {source₁ : Responder SourceState₁ P}
    {source₂ : Responder SourceState₂ Q}
    {target₁ : Responder TargetState₁ P}
    {target₂ : Responder TargetState₂ Q}
    {SourceWitness₁ : SourceState₁ → Type uI₁}
    {SourceWitness₂ : SourceState₂ → Type uI₂}
    {TargetWitness₁ : TargetState₁ → Type uJ₁}
    {TargetWitness₂ : TargetState₂ → Type uJ₂}
    {displayedSource₁ : Display.Coalgebra (Display.responder S)
      source₁.out SourceWitness₁}
    {displayedSource₂ : Display.Coalgebra (Display.responder T)
      source₂.out SourceWitness₂}
    {displayedTarget₁ : Display.Coalgebra (Display.responder S)
      target₁.out TargetWitness₁}
    {displayedTarget₂ : Display.Coalgebra (Display.responder T)
      target₂.out TargetWitness₂}
    (f : PresentationHom S source₁ SourceWitness₁ displayedSource₁
      target₁ TargetWitness₁ displayedTarget₁)
    (g : PresentationHom T source₂ SourceWitness₂ displayedSource₂
      target₂ TargetWitness₂ displayedTarget₂) :
    PresentationHom (Display.parallelSum S T)
      (Responder.parallel source₁ source₂)
      (fun state => SourceWitness₁ state.1 × SourceWitness₂ state.2)
      (parallelCoalgebra source₁ source₂ SourceWitness₁ SourceWitness₂
        displayedSource₁ displayedSource₂)
      (Responder.parallel target₁ target₂)
      (fun state => TargetWitness₁ state.1 × TargetWitness₂ state.2)
      (parallelCoalgebra target₁ target₂ TargetWitness₁ TargetWitness₂
        displayedTarget₁ displayedTarget₂) where
  toState state := (f.toState state.1, g.toState state.2)
  toWitness _ witness :=
    (f.toWitness _ witness.1, g.toWitness _ witness.2)
  map_step := by
    intro state witness
    have hf := f.map_step state.1 witness.1
    have hg := g.map_step state.2 witness.2
    dsimp [displayedTotalStep, totalMap] at hf hg ⊢
    apply Sigma.ext_iff.mpr
    constructor
    · apply Sigma.ext_iff.mpr
      constructor
      · calc
          _ = parallelBehavior
              (target₁.behavior (f.toState state.1))
              (target₂.behavior (g.toState state.2)) :=
            parallel_behavior _ _ _
          _ = parallelBehavior
              (source₁.behavior state.1) (source₂.behavior state.2) := by
            rw [f.behavior_eq state.1 witness.1,
              g.behavior_eq state.2 witness.2]
          _ = _ := (parallel_behavior _ _ _).symm
      · apply Function.hfunext rfl
        intro operation operation' hOperation
        cases hOperation
        apply Function.hfunext rfl
        intro contract contract' hContract
        cases hContract
        cases operation with
        | left operation =>
            apply ulift_heq
            exact congr_arg_heq
              (fun step => step.1.2 operation contract.down) hf
        | right operation =>
            apply ulift_heq
            exact congr_arg_heq
              (fun step => step.1.2 operation contract.down) hg
        | both leftOperation rightOperation =>
            apply prod_heq
            · exact congr_arg_heq
                (fun step => step.1.2 leftOperation contract.1) hf
            · exact congr_arg_heq
                (fun step => step.1.2 rightOperation contract.2) hg
    · apply Function.hfunext
      · apply congrArg
          (Display.mStep (Display.responder
            (Display.parallelSum S T))).sigmaPFunctor.B
        apply Sigma.ext_iff.mpr
        constructor
        · calc
            _ = parallelBehavior
                (target₁.behavior (f.toState state.1))
                (target₂.behavior (g.toState state.2)) :=
              parallel_behavior _ _ _
            _ = parallelBehavior
                (source₁.behavior state.1) (source₂.behavior state.2) := by
              rw [f.behavior_eq state.1 witness.1,
                g.behavior_eq state.2 witness.2]
            _ = _ := (parallel_behavior _ _ _).symm
        · apply Function.hfunext rfl
          intro operation operation' hOperation
          cases hOperation
          apply Function.hfunext rfl
          intro contract contract' hContract
          cases hContract
          cases operation with
          | left operation =>
              apply ulift_heq
              exact congr_arg_heq
                (fun step => step.1.2 operation contract.down) hf
          | right operation =>
              apply ulift_heq
              exact congr_arg_heq
                (fun step => step.1.2 operation contract.down) hg
          | both leftOperation rightOperation =>
              apply prod_heq
              · exact congr_arg_heq
                  (fun step => step.1.2 leftOperation contract.1) hf
              · exact congr_arg_heq
                  (fun step => step.1.2 rightOperation contract.2) hg
      · intro direction direction' hDirection
        cases hDirection
        rcases direction with ⟨⟨operation, trivialDirection⟩, contract⟩
        cases trivialDirection
        cases operation with
        | left operation =>
            have hLeft := congr_arg_heq
              (fun step => step.2
                ⟨⟨operation, PUnit.unit⟩, contract.down⟩) hf
            exact heq_of_eq (congrArg
              (fun child : Σ next, TargetWitness₁ next =>
                (⟨(child.1, g.toState state.2),
                  (child.2, g.toWitness state.2 witness.2)⟩ :
                  Σ next, TargetWitness₁ next.1 ×
                    TargetWitness₂ next.2)) (eq_of_heq hLeft))
        | right operation =>
            have hRight := congr_arg_heq
              (fun step => step.2
                ⟨⟨operation, PUnit.unit⟩, contract.down⟩) hg
            exact heq_of_eq (congrArg
              (fun child : Σ next, TargetWitness₂ next =>
                (⟨(f.toState state.1, child.1),
                  (f.toWitness state.1 witness.1, child.2)⟩ :
                  Σ next, TargetWitness₁ next.1 ×
                    TargetWitness₂ next.2)) (eq_of_heq hRight))
        | both leftOperation rightOperation =>
            have hLeft := congr_arg_heq
              (fun step => step.2
                ⟨⟨leftOperation, PUnit.unit⟩, contract.1⟩) hf
            have hRight := congr_arg_heq
              (fun step => step.2
                ⟨⟨rightOperation, PUnit.unit⟩, contract.2⟩) hg
            exact heq_of_eq (congrArg₂
              (fun (leftChild : Σ next, TargetWitness₁ next)
                  (rightChild : Σ next, TargetWitness₂ next) =>
                (⟨(leftChild.1, rightChild.1),
                  (leftChild.2, rightChild.2)⟩ :
                  Σ next, TargetWitness₁ next.1 ×
                    TargetWitness₂ next.2))
              (eq_of_heq hLeft) (eq_of_heq hRight))

@[simp] theorem parallel_toState
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {SourceState₁ : Type uS₁} {SourceState₂ : Type uS₂}
    {TargetState₁ : Type uT₁} {TargetState₂ : Type uT₂}
    {source₁ : Responder SourceState₁ P} {source₂ : Responder SourceState₂ Q}
    {target₁ : Responder TargetState₁ P} {target₂ : Responder TargetState₂ Q}
    {SourceWitness₁ : SourceState₁ → Type uI₁}
    {SourceWitness₂ : SourceState₂ → Type uI₂}
    {TargetWitness₁ : TargetState₁ → Type uJ₁}
    {TargetWitness₂ : TargetState₂ → Type uJ₂}
    {dS₁ : Display.Coalgebra (Display.responder S) source₁.out SourceWitness₁}
    {dS₂ : Display.Coalgebra (Display.responder T) source₂.out SourceWitness₂}
    {dT₁ : Display.Coalgebra (Display.responder S) target₁.out TargetWitness₁}
    {dT₂ : Display.Coalgebra (Display.responder T) target₂.out TargetWitness₂}
    (f : PresentationHom S source₁ SourceWitness₁ dS₁ target₁ TargetWitness₁ dT₁)
    (g : PresentationHom T source₂ SourceWitness₂ dS₂ target₂ TargetWitness₂ dT₂)
    (state : SourceState₁ × SourceState₂) :
    (f.parallel g).toState state = (f.toState state.1, g.toState state.2) := rfl

@[simp] theorem parallel_toWitness
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {SourceState₁ : Type uS₁} {SourceState₂ : Type uS₂}
    {TargetState₁ : Type uT₁} {TargetState₂ : Type uT₂}
    {source₁ : Responder SourceState₁ P} {source₂ : Responder SourceState₂ Q}
    {target₁ : Responder TargetState₁ P} {target₂ : Responder TargetState₂ Q}
    {SourceWitness₁ : SourceState₁ → Type uI₁}
    {SourceWitness₂ : SourceState₂ → Type uI₂}
    {TargetWitness₁ : TargetState₁ → Type uJ₁}
    {TargetWitness₂ : TargetState₂ → Type uJ₂}
    {dS₁ : Display.Coalgebra (Display.responder S) source₁.out SourceWitness₁}
    {dS₂ : Display.Coalgebra (Display.responder T) source₂.out SourceWitness₂}
    {dT₁ : Display.Coalgebra (Display.responder S) target₁.out TargetWitness₁}
    {dT₂ : Display.Coalgebra (Display.responder T) target₂.out TargetWitness₂}
    (f : PresentationHom S source₁ SourceWitness₁ dS₁ target₁ TargetWitness₁ dT₁)
    (g : PresentationHom T source₂ SourceWitness₂ dS₂ target₂ TargetWitness₂ dT₂)
    (state : SourceState₁ × SourceState₂)
    (witness : SourceWitness₁ state.1 × SourceWitness₂ state.2) :
    (f.parallel g).toWitness state witness =
      (f.toWitness state.1 witness.1, g.toWitness state.2 witness.2) := rfl

/-- Componentwise parallel preserves identity presentation homomorphisms. -/
@[simp] theorem parallel_id
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {State₁ : Type uS₁} {State₂ : Type uS₂}
    {source₁ : Responder State₁ P} {source₂ : Responder State₂ Q}
    {Witness₁ : State₁ → Type uI₁}
    {Witness₂ : State₂ → Type uI₂}
    {displayed₁ : Display.Coalgebra (Display.responder S)
      source₁.out Witness₁}
    {displayed₂ : Display.Coalgebra (Display.responder T)
      source₂.out Witness₂} :
    (PresentationHom.id (S := S) (source := source₁)
      (SourceWitness := Witness₁) (displayedSource := displayed₁)).parallel
      (PresentationHom.id (S := T) (source := source₂)
        (SourceWitness := Witness₂) (displayedSource := displayed₂)) =
      PresentationHom.id := by
  apply PresentationHom.ext
  · rfl
  · rfl

/-- Interchange for componentwise parallel and presentation composition.
This is the bifunctoriality law for lockstep parallel. -/
theorem parallel_comp
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    {SourceState₁ : Type uS₁} {SourceState₂ : Type uS₂}
    {MiddleState₁ : Type uT₁} {MiddleState₂ : Type uT₂}
    {FinalState₁ : Type uK₁} {FinalState₂ : Type uK₂}
    {source₁ : Responder SourceState₁ P}
    {source₂ : Responder SourceState₂ Q}
    {middle₁ : Responder MiddleState₁ P}
    {middle₂ : Responder MiddleState₂ Q}
    {final₁ : Responder FinalState₁ P}
    {final₂ : Responder FinalState₂ Q}
    {SourceWitness₁ : SourceState₁ → Type uI₁}
    {SourceWitness₂ : SourceState₂ → Type uI₂}
    {MiddleWitness₁ : MiddleState₁ → Type uJ₁}
    {MiddleWitness₂ : MiddleState₂ → Type uJ₂}
    {FinalWitness₁ : FinalState₁ → Type uL₁}
    {FinalWitness₂ : FinalState₂ → Type uL₂}
    {displayedSource₁ : Display.Coalgebra (Display.responder S)
      source₁.out SourceWitness₁}
    {displayedSource₂ : Display.Coalgebra (Display.responder T)
      source₂.out SourceWitness₂}
    {displayedMiddle₁ : Display.Coalgebra (Display.responder S)
      middle₁.out MiddleWitness₁}
    {displayedMiddle₂ : Display.Coalgebra (Display.responder T)
      middle₂.out MiddleWitness₂}
    {displayedFinal₁ : Display.Coalgebra (Display.responder S)
      final₁.out FinalWitness₁}
    {displayedFinal₂ : Display.Coalgebra (Display.responder T)
      final₂.out FinalWitness₂}
    (first₁ : PresentationHom S source₁ SourceWitness₁
      displayedSource₁ middle₁ MiddleWitness₁ displayedMiddle₁)
    (first₂ : PresentationHom T source₂ SourceWitness₂
      displayedSource₂ middle₂ MiddleWitness₂ displayedMiddle₂)
    (second₁ : PresentationHom S middle₁ MiddleWitness₁
      displayedMiddle₁ final₁ FinalWitness₁ displayedFinal₁)
    (second₂ : PresentationHom T middle₂ MiddleWitness₂
      displayedMiddle₂ final₂ FinalWitness₂ displayedFinal₂) :
    (second₁.parallel second₂).comp (first₁.parallel first₂) =
      (second₁.comp first₁).parallel (second₂.comp first₂) := by
  apply PresentationHom.ext
  · rfl
  · rfl

end PresentationHom

end Responder
end PFunctor
