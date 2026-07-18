/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder.Behavior

/-!
# Proof-relevant responder presentations

A `VerifiedPresentationHom` preserves the totalized one-step semantics of a
responder together with its dependent invariant witness. This module owns the
generic identity, composition, terminal-semantics, and verified-reindexing
principles; lens-specific specializations live in `Responder.Lens`.
-/

@[expose] public section

universe uA₁ uA₂ uA₃ uB uC₁ uD₁ uC₂ uD₂ uC₃ uD₃ uC₄ uD₄ uC₅ uD₅

namespace PFunctor
namespace Responder

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}

private theorem heq_funext
    {A A' : Sort uA₃} {B : A → Sort uC₃} {B' : A' → Sort uC₃}
    {f : (a : A) → B a} {f' : (a : A') → B' a}
    (hA : A = A')
    (h : ∀ a a', HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  cases hA
  have hB : B = B' := by
    funext a
    exact type_eq_of_heq (h a a HEq.rfl)
  cases hB
  apply heq_of_eq
  funext a
  exact eq_of_heq (h a a HEq.rfl)


/-- One proof-relevant responder step on the total state-and-witness
presentation. -/
def verifiedTotalStep
    {RPoly : PFunctor.{uA₃, uB}}
    (S : Display.{uA₃, uB, uC₃, uD₃} RPoly)
    {State : Type uC₂} (R : Responder State RPoly)
    (I : State → Type uD₂)
    (displayedR : Display.Coalgebra (Display.responder S) R.out I) :
    (Σ state, I state) →
      (Display.mStep (Display.responder S)).sigmaPFunctor.Obj
        (Σ state, I state)
  | ⟨state, witness⟩ =>
      let obligation := (Display.responderCoalgebraEquiv S R I)
        displayedR state witness
      ⟨⟨R.behavior state, fun query precondition =>
          (obligation query precondition).1⟩,
        fun direction => match direction with
          | ⟨⟨query, trivialDirection⟩, precondition⟩ => by
              cases trivialDirection
              exact ⟨R.next state query,
                (obligation query precondition).2⟩⟩

/-- Sigma-erasing a verified behavior is the ordinary behavior of its total
state-and-witness presentation. -/
theorem toM_verifiedBehavior_eq_corec
    {RPoly : PFunctor.{uA₃, uB}}
    (S : Display.{uA₃, uB, uC₃, uD₃} RPoly)
    {State : Type uC₂} (R : Responder State RPoly)
    (I : State → Type uD₂)
    (displayedR : Display.Coalgebra (Display.responder S) R.out I)
    (state : State) (witness : I state) :
    (verifiedBehavior S R I displayedR state witness).toM =
      PFunctor.M.corec (verifiedTotalStep S R I displayedR)
        ⟨state, witness⟩ := by
  simp only [verifiedBehavior, Display.Coalgebra.toM, Display.M.corec,
    IPFunctor.IM.toM_corec]
  let presentedTotalStep := IPFunctor.IM.totalStep
    (fun tree state =>
      (Display.M.stepEquiv (Display.Coalgebra.Presented R I) tree).symm
        (Display.Coalgebra.presentedStep R I displayedR tree state))
  let relation := fun
      (presented : Σ tree, Display.Coalgebra.Presented R I tree)
      (direct : Σ state, I state) =>
    presented.2.1 = direct.1 ∧ HEq presented.2.2.2 direct.2
  apply PFunctor.M.corec_eq_corec presentedTotalStep
    (verifiedTotalStep S R I displayedR) relation
  · exact ⟨rfl, heq_of_eq rfl⟩
  · rintro ⟨tree, ⟨current, ⟨⟨hCurrent⟩, currentWitness⟩⟩⟩
      ⟨direct, directWitness⟩ ⟨hState, hWitness⟩
    cases hState
    cases hWitness
    cases hCurrent
    dsimp [presentedTotalStep, verifiedTotalStep,
      IPFunctor.IM.totalStep, Display.Coalgebra.presentedStep,
      Display.M.stepEquiv]
    refine ⟨_, _, _, rfl, rfl, ?_⟩
    intro direction
    rcases direction with ⟨⟨query, trivialDirection⟩, precondition⟩
    cases trivialDirection
    exact ⟨rfl, heq_of_eq rfl⟩

/-- A homomorphism between proof-relevant responder presentations. The state
and witness maps remain split so the latter visibly respects its dependent
state index; an arbitrary homomorphism of total sigma coalgebras would erase
that useful presentation structure. The sole law says that mapping a source
state and witness commutes with the complete totalized
verified step.  Because answers, postconditions, next states, and next
witnesses are packaged together, the law requires neither `HEq` nor exposed
casts. -/
structure VerifiedPresentationHom
    {RPoly : PFunctor.{uA₃, uB}}
    (S : Display.{uA₃, uB, uC₃, uD₃} RPoly)
    {SourceState : Type uC₁} (source : Responder SourceState RPoly)
    (SourceWitness : SourceState → Type uD₁)
    (displayedSource : Display.Coalgebra (Display.responder S)
      source.out SourceWitness)
    {TargetState : Type uC₂} (target : Responder TargetState RPoly)
    (TargetWitness : TargetState → Type uD₂)
    (displayedTarget : Display.Coalgebra (Display.responder S)
      target.out TargetWitness) where
  /-- Map the underlying responder state. -/
  toState : SourceState → TargetState
  /-- Map its dependent witness into the fiber over the mapped state. -/
  toWitness : (state : SourceState) →
    SourceWitness state → TargetWitness (toState state)
  map_step : ∀ state witness,
    verifiedTotalStep S target TargetWitness displayedTarget
        ⟨toState state, toWitness state witness⟩ =
      (Display.mStep (Display.responder S)).sigmaPFunctor.map
        (fun stateAndWitness =>
          ⟨toState stateAndWitness.1,
            toWitness stateAndWitness.1 stateAndWitness.2⟩)
        (verifiedTotalStep S source SourceWitness displayedSource
          ⟨state, witness⟩)

namespace VerifiedPresentationHom

variable
    {RPoly : PFunctor.{uA₃, uB}}
    {S : Display.{uA₃, uB, uC₃, uD₃} RPoly}
    {SourceState : Type uC₁} {source : Responder SourceState RPoly}
    {SourceWitness : SourceState → Type uD₁}
    {displayedSource : Display.Coalgebra (Display.responder S)
      source.out SourceWitness}
    {TargetState : Type uC₂} {target : Responder TargetState RPoly}
    {TargetWitness : TargetState → Type uD₂}
    {displayedTarget : Display.Coalgebra (Display.responder S)
      target.out TargetWitness}

/-- The induced map on total state-and-witness sigma types. -/
def totalMap
    (f : VerifiedPresentationHom S source SourceWitness displayedSource
      target TargetWitness displayedTarget) :
    (Σ state, SourceWitness state) →
      (Σ state, TargetWitness state)
  | ⟨state, witness⟩ => ⟨f.toState state, f.toWitness state witness⟩

/-- Transport a dependent witness map along equality of its state map. -/
def transportToWitness
    {State₁ : Type uC₁} {Witness₁ : State₁ → Type uD₁}
    {State₂ : Type uC₂} {Witness₂ : State₂ → Type uD₂}
    {toState₁ toState₂ : State₁ → State₂}
    (h : toState₁ = toState₂) :
    ((state : State₁) → Witness₁ state → Witness₂ (toState₁ state)) →
      ((state : State₁) → Witness₁ state → Witness₂ (toState₂ state)) :=
  h ▸ _root_.id

/-- Presentation homomorphisms are determined by their state and dependent
witness maps; preservation proofs are propositionally irrelevant. -/
@[ext (iff := false)] theorem ext
    (f g : VerifiedPresentationHom S source SourceWitness displayedSource
      target TargetWitness displayedTarget)
    (hState : f.toState = g.toState)
    (hWitness : transportToWitness hState f.toWitness = g.toWitness) :
    f = g := by
  cases f with
  | mk fState fWitness fStep =>
      cases g with
      | mk gState gWitness gStep =>
          dsimp at hState hWitness
          subst gState
          simp only [transportToWitness] at hWitness
          subst gWitness
          rfl

/-- Identity homomorphism of a verified responder presentation. -/
def id : VerifiedPresentationHom S source SourceWitness displayedSource
    source SourceWitness displayedSource where
  toState := _root_.id
  toWitness := fun _ => _root_.id
  map_step := by
    intro state witness
    rfl

/-- Composition of verified presentation homomorphisms. -/
def comp
    {MiddleState : Type uC₂} {middle : Responder MiddleState RPoly}
    {MiddleWitness : MiddleState → Type uD₂}
    {displayedMiddle : Display.Coalgebra (Display.responder S)
      middle.out MiddleWitness}
    {FinalState : Type uC₄} {final : Responder FinalState RPoly}
    {FinalWitness : FinalState → Type uD₄}
    {displayedFinal : Display.Coalgebra (Display.responder S)
      final.out FinalWitness}
    (second : VerifiedPresentationHom S middle MiddleWitness
      displayedMiddle final FinalWitness displayedFinal)
    (first : VerifiedPresentationHom S source SourceWitness displayedSource
      middle MiddleWitness displayedMiddle) :
    VerifiedPresentationHom S source SourceWitness displayedSource
      final FinalWitness displayedFinal where
  toState state := second.toState (first.toState state)
  toWitness state witness :=
    second.toWitness (first.toState state) (first.toWitness state witness)
  map_step := by
    intro state witness
    rw [second.map_step, first.map_step]
    rfl

@[simp] theorem id_toState (state : SourceState) :
    (id : VerifiedPresentationHom S source SourceWitness displayedSource
      source SourceWitness displayedSource).toState state = state :=
  rfl

@[simp] theorem id_toWitness (state : SourceState)
    (witness : SourceWitness state) :
    (id : VerifiedPresentationHom S source SourceWitness displayedSource
      source SourceWitness displayedSource).toWitness state witness = witness :=
  rfl

@[simp] theorem comp_toState
    {MiddleState : Type uC₂} {middle : Responder MiddleState RPoly}
    {MiddleWitness : MiddleState → Type uD₂}
    {displayedMiddle : Display.Coalgebra (Display.responder S)
      middle.out MiddleWitness}
    {FinalState : Type uC₄} {final : Responder FinalState RPoly}
    {FinalWitness : FinalState → Type uD₄}
    {displayedFinal : Display.Coalgebra (Display.responder S)
      final.out FinalWitness}
    (second : VerifiedPresentationHom S middle MiddleWitness
      displayedMiddle final FinalWitness displayedFinal)
    (first : VerifiedPresentationHom S source SourceWitness displayedSource
      middle MiddleWitness displayedMiddle) (state : SourceState) :
    (second.comp first).toState state =
      second.toState (first.toState state) :=
  rfl

@[simp] theorem comp_toWitness
    {MiddleState : Type uC₂} {middle : Responder MiddleState RPoly}
    {MiddleWitness : MiddleState → Type uD₂}
    {displayedMiddle : Display.Coalgebra (Display.responder S)
      middle.out MiddleWitness}
    {FinalState : Type uC₄} {final : Responder FinalState RPoly}
    {FinalWitness : FinalState → Type uD₄}
    {displayedFinal : Display.Coalgebra (Display.responder S)
      final.out FinalWitness}
    (second : VerifiedPresentationHom S middle MiddleWitness
      displayedMiddle final FinalWitness displayedFinal)
    (first : VerifiedPresentationHom S source SourceWitness displayedSource
      middle MiddleWitness displayedMiddle)
    (state : SourceState) (witness : SourceWitness state) :
    (second.comp first).toWitness state witness =
      second.toWitness (first.toState state)
        (first.toWitness state witness) :=
  rfl

@[simp] theorem id_comp
    (f : VerifiedPresentationHom S source SourceWitness displayedSource
      target TargetWitness displayedTarget) :
    id.comp f = f := by
  apply ext
  · rfl
  · rfl

@[simp] theorem comp_id
    (f : VerifiedPresentationHom S source SourceWitness displayedSource
      target TargetWitness displayedTarget) :
    f.comp id = f := by
  apply ext
  · rfl
  · rfl

theorem comp_assoc
    {MiddleState : Type uC₂} {middle : Responder MiddleState RPoly}
    {MiddleWitness : MiddleState → Type uD₂}
    {displayedMiddle : Display.Coalgebra (Display.responder S)
      middle.out MiddleWitness}
    {NextState : Type uC₄} {next : Responder NextState RPoly}
    {NextWitness : NextState → Type uD₄}
    {displayedNext : Display.Coalgebra (Display.responder S)
      next.out NextWitness}
    {FinalState : Type uC₅} {final : Responder FinalState RPoly}
    {FinalWitness : FinalState → Type uD₅}
    {displayedFinal : Display.Coalgebra (Display.responder S)
      final.out FinalWitness}
    (third : VerifiedPresentationHom S next NextWitness displayedNext
      final FinalWitness displayedFinal)
    (second : VerifiedPresentationHom S middle MiddleWitness
      displayedMiddle next NextWitness displayedNext)
    (first : VerifiedPresentationHom S source SourceWitness displayedSource
      middle MiddleWitness displayedMiddle) :
    (third.comp second).comp first = third.comp (second.comp first) := by
  apply ext
  · rfl
  · rfl

/-- Map any verified responder presentation to its terminal state-free
semantics. This is the reusable boundary between state-presented and
state-free verified behavior. -/
def toTerminal
    (S : Display.{uA₁, uB, uC₁, uD₁} P)
    {State : Type uC₂} (R : Responder State P)
    (I : State → Type uD₂)
    (displayedR : Display.Coalgebra (Display.responder S) R.out I) :
    VerifiedPresentationHom S R I displayedR
      (Responder.terminal (P := P))
      (Display.M (Display.responder S))
      (Display.Coalgebra.terminal (Display.responder S)) where
  toState state := R.behavior state
  toWitness state witness :=
    verifiedBehavior S R I displayedR state witness
  map_step := by
    intro state witness
    have hBase :
        (Responder.terminal (P := P)).behavior (R.behavior state) =
          R.behavior state := by simp
    dsimp [verifiedTotalStep, VerifiedPresentationHom.totalMap]
    apply Sigma.ext_iff.mpr
    constructor
    · apply Sigma.ext_iff.mpr
      constructor
      · exact hBase
      · apply heq_funext rfl
        intro query query' hQuery
        cases hQuery
        apply heq_funext rfl
        intro precondition precondition' hPrecondition
        cases hPrecondition
        let targetResult := (Responder.terminal (P := P)).runFree
          ((Handler.id P) query) (R.behavior state)
        let sourceResult := R.runFree ((Handler.id P) query) state
        let presentedResult : P.B query × PFunctor.M (P ⊸ X.{uA₁, uB}) :=
          ⟨sourceResult.1, R.behavior sourceResult.2⟩
        let targetEvidence := runFreeDisplayed S
          (Responder.terminal (P := P))
          (Display.Coalgebra.terminal (Display.responder S))
          ((Display.Handler.id S) query precondition) (R.behavior state)
          (verifiedBehavior S R I displayedR state witness)
        let sourceEvidence := runFreeDisplayed S R displayedR
          ((Display.Handler.id S) query precondition) state witness
        let mappedEvidence : S.direction query precondition
              presentedResult.1 ×
            Display.M (Display.responder S) presentedResult.2 :=
          ⟨sourceEvidence.1,
            verifiedBehavior S R I displayedR sourceResult.2
              sourceEvidence.2⟩
        let presentationEq :=
          runFree_terminal R ((Handler.id P) query) state
        let Evidence := fun result : P.B query ×
            PFunctor.M (P ⊸ X.{uA₁, uB}) =>
          S.direction query precondition result.1 ×
            Display.M (Display.responder S) result.2
        have hEvidence :
            transportRunEvidence (S.direction query precondition)
                (Display.M (Display.responder S)) presentationEq
                targetEvidence = mappedEvidence := by
          exact runFreeDisplayed_verifiedBehavior S R I displayedR
            ((Handler.id P) query) ((Display.Handler.id S) query precondition)
            state witness
        have hSigma :
            (⟨targetResult, targetEvidence⟩ : Σ result, Evidence result) =
              ⟨presentedResult, mappedEvidence⟩ := by
          apply Sigma.ext presentationEq
          exact (transportRunEvidence_heq _ _ presentationEq
            targetEvidence).symm.trans (heq_of_eq hEvidence)
        exact congr_arg_heq
          (fun result : Σ result, Evidence result => result.2.1) hSigma
    · apply heq_funext
      · apply congrArg
          (Display.mStep (Display.responder S)).sigmaPFunctor.B
        apply Sigma.ext_iff.mpr
        constructor
        · exact hBase
        · apply heq_funext rfl
          intro query query' hQuery
          cases hQuery
          apply heq_funext rfl
          intro precondition precondition' hPrecondition
          cases hPrecondition
          let targetResult := (Responder.terminal (P := P)).runFree
            ((Handler.id P) query) (R.behavior state)
          let sourceResult := R.runFree ((Handler.id P) query) state
          let presentedResult : P.B query ×
              PFunctor.M (P ⊸ X.{uA₁, uB}) :=
            ⟨sourceResult.1, R.behavior sourceResult.2⟩
          let targetEvidence := runFreeDisplayed S
            (Responder.terminal (P := P))
            (Display.Coalgebra.terminal (Display.responder S))
            ((Display.Handler.id S) query precondition) (R.behavior state)
            (verifiedBehavior S R I displayedR state witness)
          let sourceEvidence := runFreeDisplayed S R displayedR
            ((Display.Handler.id S) query precondition) state witness
          let mappedEvidence : S.direction query precondition
                presentedResult.1 ×
              Display.M (Display.responder S) presentedResult.2 :=
            ⟨sourceEvidence.1,
              verifiedBehavior S R I displayedR sourceResult.2
                sourceEvidence.2⟩
          let presentationEq :=
            runFree_terminal R ((Handler.id P) query) state
          let Evidence := fun result : P.B query ×
              PFunctor.M (P ⊸ X.{uA₁, uB}) =>
            S.direction query precondition result.1 ×
              Display.M (Display.responder S) result.2
          have hEvidence :
              transportRunEvidence (S.direction query precondition)
                  (Display.M (Display.responder S)) presentationEq
                  targetEvidence = mappedEvidence := by
            exact runFreeDisplayed_verifiedBehavior S R I displayedR
              ((Handler.id P) query) ((Display.Handler.id S) query precondition)
              state witness
          have hSigma :
              (⟨targetResult, targetEvidence⟩ : Σ result, Evidence result) =
                ⟨presentedResult, mappedEvidence⟩ := by
            apply Sigma.ext presentationEq
            exact (transportRunEvidence_heq _ _ presentationEq
              targetEvidence).symm.trans (heq_of_eq hEvidence)
          exact congr_arg_heq
            (fun result : Σ result, Evidence result => result.2.1) hSigma
      · intro direction direction' hDirection
        cases hDirection
        rcases direction with ⟨⟨query, trivialDirection⟩, precondition⟩
        cases trivialDirection
        let targetResult := (Responder.terminal (P := P)).runFree
          ((Handler.id P) query) (R.behavior state)
        let sourceResult := R.runFree ((Handler.id P) query) state
        let presentedResult : P.B query × PFunctor.M (P ⊸ X.{uA₁, uB}) :=
          ⟨sourceResult.1, R.behavior sourceResult.2⟩
        let targetEvidence := runFreeDisplayed S
          (Responder.terminal (P := P))
          (Display.Coalgebra.terminal (Display.responder S))
          ((Display.Handler.id S) query precondition) (R.behavior state)
          (verifiedBehavior S R I displayedR state witness)
        let sourceEvidence := runFreeDisplayed S R displayedR
          ((Display.Handler.id S) query precondition) state witness
        let mappedEvidence : S.direction query precondition
              presentedResult.1 ×
            Display.M (Display.responder S) presentedResult.2 :=
          ⟨sourceEvidence.1,
            verifiedBehavior S R I displayedR sourceResult.2
              sourceEvidence.2⟩
        let presentationEq :=
          runFree_terminal R ((Handler.id P) query) state
        let Evidence := fun result : P.B query ×
            PFunctor.M (P ⊸ X.{uA₁, uB}) =>
          S.direction query precondition result.1 ×
            Display.M (Display.responder S) result.2
        have hEvidence :
            transportRunEvidence (S.direction query precondition)
                (Display.M (Display.responder S)) presentationEq
                targetEvidence = mappedEvidence := by
          exact runFreeDisplayed_verifiedBehavior S R I displayedR
            ((Handler.id P) query) ((Display.Handler.id S) query precondition)
            state witness
        have hSigma :
            (⟨targetResult, targetEvidence⟩ : Σ result, Evidence result) =
              ⟨presentedResult, mappedEvidence⟩ := by
          apply Sigma.ext presentationEq
          exact (transportRunEvidence_heq _ _ presentationEq
            targetEvidence).symm.trans (heq_of_eq hEvidence)
        exact congr_arg_heq
          (fun result : Σ result, Evidence result =>
            (⟨result.1.2, result.2.2⟩ :
              Σ behavior, Display.M (Display.responder S) behavior)) hSigma

/-- The base behavior equality carried by a verified presentation
homomorphism. -/
theorem behavior_eq
    (f : VerifiedPresentationHom S source SourceWitness displayedSource
      target TargetWitness displayedTarget)
    (state : SourceState) (witness : SourceWitness state) :
    target.behavior (f.toState state) = source.behavior state :=
  congrArg (fun node => node.1.1) (f.map_step state witness)

/-- Verified terminal semantics is natural under a verified presentation
homomorphism. -/
theorem verifiedBehavior_naturality
    (f : VerifiedPresentationHom S source SourceWitness displayedSource
      target TargetWitness displayedTarget)
    (state : SourceState) (witness : SourceWitness state) :
    Display.M.transport (f.behavior_eq state witness)
        (verifiedBehavior S target TargetWitness displayedTarget
          (f.toState state) (f.toWitness state witness)) =
      verifiedBehavior S source SourceWitness displayedSource
        state witness := by
  apply IPFunctor.IM.ext
  rw [Display.M.toM_transport]
  rw [toM_verifiedBehavior_eq_corec,
    toM_verifiedBehavior_eq_corec]
  let relation := fun
      (targetState : Σ state, TargetWitness state)
      (sourceState : Σ state, SourceWitness state) =>
    targetState = f.totalMap sourceState
  apply PFunctor.M.corec_eq_corec
    (verifiedTotalStep S target TargetWitness displayedTarget)
    (verifiedTotalStep S source SourceWitness displayedSource)
    relation
  · rfl
  · intro targetState sourceState hState
    subst targetState
    rcases sourceState with ⟨current, currentWitness⟩
    dsimp [totalMap]
    rw [f.map_step]
    rcases hStep : verifiedTotalStep S source SourceWitness
      displayedSource ⟨current, currentWitness⟩ with
      ⟨shape, children⟩
    refine ⟨shape, _, children, rfl, rfl, ?_⟩
    intro direction
    rfl

end VerifiedPresentationHom

/-- Presenting a reindexed verified responder through terminal state-free
semantics is a verified presentation homomorphism. -/
def reindexVerifiedPresentationHom
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    (f : PFunctor.Handler (PFunctor.FreeM Q) P)
    (df : Display.Handler S T f)
    {State : Type uC₃} (R : Responder State Q)
    (I : State → Type uD₃)
    (displayedR : Display.Coalgebra (Display.responder T) R.out I) :
    VerifiedPresentationHom S
      (Responder.reindex f R) I
      (Responder.reindexCoalgebra S T f df R displayedR)
      (Responder.reindex f (Responder.terminal (P := Q)))
      (Display.M (Display.responder T))
      (Responder.reindexCoalgebra S T f df
        (Responder.terminal (P := Q))
        (Display.Coalgebra.terminal (Display.responder T))) where
  toState state := R.behavior state
  toWitness state witness := verifiedBehavior T R I displayedR state witness
  map_step := by
    intro state witness
    have hBase :
        (Responder.reindex f (Responder.terminal (P := Q))).behavior
            (R.behavior state) =
          (Responder.reindex f R).behavior state := by
      calc
        _ = reindexBehavior f (R.behavior state) := by
          rw [← reindexBehavior_behavior]
          simp
        _ = _ := reindexBehavior_behavior f R state
    dsimp [verifiedTotalStep, VerifiedPresentationHom.totalMap]
    apply Sigma.ext_iff.mpr
    constructor
    · apply Sigma.ext_iff.mpr
      constructor
      · exact hBase
      · apply heq_funext rfl
        intro query query' hQuery
        cases hQuery
        apply heq_funext rfl
        intro precondition precondition' hPrecondition
        cases hPrecondition
        let targetResult := (Responder.terminal (P := Q)).runFree
          (f query) (R.behavior state)
        let sourceResult := R.runFree (f query) state
        let presentedResult : P.B query ×
            PFunctor.M (Q ⊸ X.{uA₂, uB}) :=
          ⟨sourceResult.1, R.behavior sourceResult.2⟩
        let targetEvidence := runFreeDisplayed T
          (Responder.terminal (P := Q))
          (Display.Coalgebra.terminal (Display.responder T))
          (df query precondition) (R.behavior state)
          (verifiedBehavior T R I displayedR state witness)
        let sourceEvidence := runFreeDisplayed T R displayedR
          (df query precondition) state witness
        let mappedEvidence :
            S.direction query precondition presentedResult.1 ×
              Display.M (Display.responder T) presentedResult.2 :=
          ⟨sourceEvidence.1,
            verifiedBehavior T R I displayedR sourceResult.2
              sourceEvidence.2⟩
        let presentationEq := runFree_terminal R (f query) state
        let Evidence := fun result : P.B query ×
            PFunctor.M (Q ⊸ X.{uA₂, uB}) =>
          S.direction query precondition result.1 ×
            Display.M (Display.responder T) result.2
        have hEvidence :
            transportRunEvidence (S.direction query precondition)
                (Display.M (Display.responder T)) presentationEq
                targetEvidence = mappedEvidence := by
          exact runFreeDisplayed_verifiedBehavior T R I displayedR
            (f query) (df query precondition) state witness
        have hSigma :
            (⟨targetResult, targetEvidence⟩ : Σ result, Evidence result) =
              ⟨presentedResult, mappedEvidence⟩ := by
          apply Sigma.ext presentationEq
          exact (transportRunEvidence_heq _ _ presentationEq
            targetEvidence).symm.trans (heq_of_eq hEvidence)
        exact congr_arg_heq
          (fun result : Σ result, Evidence result => result.2.1) hSigma
    · apply heq_funext
      · apply congrArg
          (Display.mStep (Display.responder S)).sigmaPFunctor.B
        apply Sigma.ext_iff.mpr
        constructor
        · exact hBase
        · apply heq_funext rfl
          intro query query' hQuery
          cases hQuery
          apply heq_funext rfl
          intro precondition precondition' hPrecondition
          cases hPrecondition
          let targetResult := (Responder.terminal (P := Q)).runFree
            (f query) (R.behavior state)
          let sourceResult := R.runFree (f query) state
          let presentedResult : P.B query ×
              PFunctor.M (Q ⊸ X.{uA₂, uB}) :=
            ⟨sourceResult.1, R.behavior sourceResult.2⟩
          let targetEvidence := runFreeDisplayed T
            (Responder.terminal (P := Q))
            (Display.Coalgebra.terminal (Display.responder T))
            (df query precondition) (R.behavior state)
            (verifiedBehavior T R I displayedR state witness)
          let sourceEvidence := runFreeDisplayed T R displayedR
            (df query precondition) state witness
          let mappedEvidence :
              S.direction query precondition presentedResult.1 ×
                Display.M (Display.responder T) presentedResult.2 :=
            ⟨sourceEvidence.1,
              verifiedBehavior T R I displayedR sourceResult.2
                sourceEvidence.2⟩
          let presentationEq := runFree_terminal R (f query) state
          let Evidence := fun result : P.B query ×
              PFunctor.M (Q ⊸ X.{uA₂, uB}) =>
            S.direction query precondition result.1 ×
              Display.M (Display.responder T) result.2
          have hEvidence :
              transportRunEvidence (S.direction query precondition)
                  (Display.M (Display.responder T)) presentationEq
                  targetEvidence = mappedEvidence := by
            exact runFreeDisplayed_verifiedBehavior T R I displayedR
              (f query) (df query precondition) state witness
          have hSigma :
              (⟨targetResult, targetEvidence⟩ : Σ result, Evidence result) =
                ⟨presentedResult, mappedEvidence⟩ := by
            apply Sigma.ext presentationEq
            exact (transportRunEvidence_heq _ _ presentationEq
              targetEvidence).symm.trans (heq_of_eq hEvidence)
          exact congr_arg_heq
            (fun result : Σ result, Evidence result => result.2.1) hSigma
      · intro direction direction' hDirection
        cases hDirection
        rcases direction with ⟨⟨query, trivialDirection⟩, precondition⟩
        cases trivialDirection
        let targetResult := (Responder.terminal (P := Q)).runFree
          (f query) (R.behavior state)
        let sourceResult := R.runFree (f query) state
        let presentedResult : P.B query ×
            PFunctor.M (Q ⊸ X.{uA₂, uB}) :=
          ⟨sourceResult.1, R.behavior sourceResult.2⟩
        let targetEvidence := runFreeDisplayed T
          (Responder.terminal (P := Q))
          (Display.Coalgebra.terminal (Display.responder T))
          (df query precondition) (R.behavior state)
          (verifiedBehavior T R I displayedR state witness)
        let sourceEvidence := runFreeDisplayed T R displayedR
          (df query precondition) state witness
        let mappedEvidence :
            S.direction query precondition presentedResult.1 ×
              Display.M (Display.responder T) presentedResult.2 :=
          ⟨sourceEvidence.1,
            verifiedBehavior T R I displayedR sourceResult.2
              sourceEvidence.2⟩
        let presentationEq := runFree_terminal R (f query) state
        let Evidence := fun result : P.B query ×
            PFunctor.M (Q ⊸ X.{uA₂, uB}) =>
          S.direction query precondition result.1 ×
            Display.M (Display.responder T) result.2
        have hEvidence :
            transportRunEvidence (S.direction query precondition)
                (Display.M (Display.responder T)) presentationEq
                targetEvidence = mappedEvidence := by
          exact runFreeDisplayed_verifiedBehavior T R I displayedR
            (f query) (df query precondition) state witness
        have hSigma :
            (⟨targetResult, targetEvidence⟩ : Σ result, Evidence result) =
              ⟨presentedResult, mappedEvidence⟩ := by
          apply Sigma.ext presentationEq
          exact (transportRunEvidence_heq _ _ presentationEq
            targetEvidence).symm.trans (heq_of_eq hEvidence)
        exact congr_arg_heq
          (fun result : Σ result, Evidence result =>
            (⟨result.1.2, result.2.2⟩ :
              Σ behavior, Display.M (Display.responder T) behavior)) hSigma

/-- State-free verified reindexing agrees with reindexing the presenting
verified responder, after the ordinary presentation equality. -/
theorem reindexVerifiedBehavior_verifiedBehavior
    {S : Display.{uA₁, uB, uC₁, uD₁} P}
    {T : Display.{uA₂, uB, uC₂, uD₂} Q}
    (f : PFunctor.Handler (PFunctor.FreeM Q) P)
    (df : Display.Handler S T f)
    {State : Type uC₃} (R : Responder State Q)
    (I : State → Type uD₃)
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    (state : State) (witness : I state) :
    Display.M.transport (reindexBehavior_behavior f R state)
        (reindexVerifiedBehavior S T f df (R.behavior state)
          (verifiedBehavior T R I displayedR state witness)) =
      verifiedBehavior S (Responder.reindex f R) I
        (Responder.reindexCoalgebra S T f df R displayedR)
        state witness := by
  have h := (reindexVerifiedPresentationHom f df R I displayedR).verifiedBehavior_naturality
    state witness
  change Display.M.transport _
      (reindexVerifiedBehavior S T f df (R.behavior state)
        (verifiedBehavior T R I displayedR state witness)) = _ at h
  exact (Display.M.transport_proof_irrel
    ((reindexVerifiedPresentationHom f df R I displayedR).behavior_eq state witness)
    (reindexBehavior_behavior f R state)
    (reindexVerifiedBehavior S T f df (R.behavior state)
      (verifiedBehavior T R I displayedR state witness))).symm.trans h

end Responder
end PFunctor
