/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.M
public import PolyFun.PFunctor.Dynamical.Responder.Reindex
public import PolyFun.PFunctor.Dynamical.Trajectory

/-!
# State-free responder behavior

An ordinary state-free responder behavior for `P` is already the terminal
coalgebra `M (P ⊸ X)`; no paper-specific `Mealy` alias is introduced.  Given a
proof-relevant responder coalgebra, `Display.Coalgebra.toM` maps a state and
its current witness into the greatest displayed fixed point over that ordinary
behavior:

```text
Display.M (Display.responder S) (R.behavior state).
```

The displayed fixed point is not a `Function.Fiber` of a forgetful M-map.
There is only a covariant chart from the total responder display to the base
responder polynomial: a bare query cannot supply the precondition witness
needed by the displayed child.  `Display.M` retains that genuine branching
instead of postulating a nonexistent lens.

Structural state-free reindexing keeps the source and target interface
universes independent. Only its categorical composition laws retain the
homogeneous source/intermediate response-universe constraint of
`FreeM.liftM`.
-/

@[expose] public section

universe uA uA' uA'' uB uB' uC uD uC' uD' uC'' uD'' uE uF uS

namespace PFunctor

namespace M

variable {P : PFunctor.{uA, uB}}

/-- The terminal `P`-coalgebra as a dynamical system whose states are
state-free behaviors. -/
def terminalSystem : DynSystem (PFunctor.M P) P :=
  (fun tree => tree.head) ⇆ (fun tree => tree.children)

@[simp]
theorem terminalSystem_out (tree : PFunctor.M P) :
    terminalSystem.out tree = PFunctor.M.dest tree :=
  rfl

@[simp]
theorem terminalSystem_behavior (tree : PFunctor.M P) :
    terminalSystem.behavior tree = tree :=
  PFunctor.M.corec_dest tree

end M

namespace Display
namespace Coalgebra

variable {P : PFunctor.{uA, uB}}
variable {S : Display.{uA, uB, uC, uD} P}
variable {State : Type uS}

/-- States presenting a fixed ordinary behavior, together with their current
displayed witness.  This is the indexed seed family used to quotient a state
presentation through terminal displayed semantics. -/
def Presented (system : DynSystem State P) (F : State → Type uF)
    (tree : PFunctor.M P) : Type (max uS uF) :=
  Σ state : State, PLift (system.behavior state = tree) × F state

/-- One displayed step on behavior-indexed presentation states. -/
def presentedStep (system : DynSystem State P) (F : State → Type uF)
    (displayed : Display.Coalgebra S system.out F)
    (tree : PFunctor.M P) :
    Presented system F tree →
      S.Obj (Presented system F) (PFunctor.M.dest tree)
  | ⟨state, ⟨behaviorEq⟩, witness⟩ => by
      subst tree
      rw [DynSystem.dest_behavior]
      exact
          ⟨(displayed state witness).1, fun direction displayedDirection =>
          ⟨system.update state direction, ⟨rfl⟩,
            (displayed state witness).2 direction displayedDirection⟩⟩

/-- Map a proof-relevant state presentation into its state-free displayed
behavior.  Distinct or unreachable presentation states are intentionally
identified when they generate the same coinductive evidence. -/
def toM (system : DynSystem State P) (F : State → Type uF)
    (displayed : Display.Coalgebra S system.out F)
    (state : State) (witness : F state) :
    Display.M S (system.behavior state) :=
  Display.M.corec (Presented system F)
    (presentedStep system F displayed) (system.behavior state)
    ⟨state, ⟨rfl⟩, witness⟩

/-- The first unfolding of state-free displayed semantics. -/
theorem dest_toM (system : DynSystem State P) (F : State → Type uF)
    (displayed : Display.Coalgebra S system.out F)
    (state : State) (witness : F state) :
    Display.M.dest (toM system F displayed state witness) =
      Display.Obj.map
        (fun tree presentation =>
          Display.M.corec (Presented system F)
            (presentedStep system F displayed) tree presentation)
        (PFunctor.M.dest (system.behavior state))
        (presentedStep system F displayed (system.behavior state)
          ⟨state, ⟨rfl⟩, witness⟩) :=
  Display.M.dest_corec _ _ _ _

/-- The destructor is the canonical displayed coalgebra on terminal behavior
states. -/
def terminal (S : Display.{uA, uB, uC, uD} P) :
    Display.Coalgebra S (PFunctor.M.terminalSystem (P := P)).out
      (Display.M S) :=
  fun _ displayedTree => Display.M.dest displayedTree

end Coalgebra
end Display

namespace Responder

variable {P : PFunctor.{uA, uB}}
variable {Q : PFunctor.{uA', uB'}}
variable {State : Type uS}

/-- The canonical responder whose states are state-free responder behaviors. -/
def terminal : Responder (PFunctor.M (P ⊸ X.{uA, uB})) P :=
  PFunctor.M.terminalSystem

@[simp]
theorem terminal_behavior (tree : PFunctor.M (P ⊸ X.{uA, uB})) :
    terminal.behavior tree = tree :=
  PFunctor.M.terminalSystem_behavior tree

/-- The child of a presented responder behavior after a query is the behavior
of the presented responder's next state. -/
theorem behavior_child (R : Responder State P)
    (state : State) (query : P.A) :
    PFunctor.M.children (R.behavior state) ⟨query, PUnit.unit⟩ =
      R.behavior (R.next state query) := by
  change
    (PFunctor.M.dest (R.behavior state)).2 ⟨query, PUnit.unit⟩ = _
  rw [DynSystem.dest_behavior]
  rfl

@[simp]
theorem terminal_answer_behavior (R : Responder State P)
    (state : State) (query : P.A) :
    (terminal (P := P)).answer (R.behavior state) query =
      R.answer state query := by
  change
    ((PFunctor.M.dest (R.behavior state)).1).toFunB query PUnit.unit = _
  rw [DynSystem.dest_behavior]
  rfl

@[simp]
theorem terminal_next_behavior (R : Responder State P)
    (state : State) (query : P.A) :
    (terminal (P := P)).next (R.behavior state) query =
      R.behavior (R.next state query) := by
  change
    (PFunctor.M.dest (R.behavior state)).2 ⟨query, PUnit.unit⟩ = _
  rw [DynSystem.dest_behavior]
  rfl

/-- Executing a finite program on terminal state-free behavior preserves the
ordinary result and replaces the final presentation state by its behavior. -/
theorem runFree_terminal (R : Responder State Q)
    {E : Type uE} (program : FreeM Q E) (state : State) :
    (terminal (P := Q)).runFree program (R.behavior state) =
      let result := R.runFree program state
      ⟨result.1, R.behavior result.2⟩ := by
  induction program generalizing state with
  | pure value => rfl
  | lift_bind query next ih =>
      change
        (terminal (P := Q)).runFree
            (next ((terminal (P := Q)).answer (R.behavior state) query))
            ((terminal (P := Q)).next (R.behavior state) query) = _
      rw [terminal_answer_behavior, terminal_next_behavior]
      exact ih (R.answer state query) (R.next state query)

/-! ## Coinductive displayed response -/

/-- Destructor equivalence for one displayed responder observation.

This is the intrinsic form of Aberlé's coinductive `DepMealy.appD`: a query and
precondition witness produce postcondition data and a verified continuation
over the selected ordinary behavior child. -/
def respondDisplayedEquiv
    (S : Display.{uA, uB, uC, uD} P)
    (behavior : PFunctor.M (P ⊸ X.{uA, uB})) :
    Display.M (Display.responder S) behavior ≃
      ((query : P.A) → (precondition : S.position query) →
        S.direction query precondition
            (behavior.head.toFunB query PUnit.unit) ×
          Display.M (Display.responder S)
            (behavior.children ⟨query, PUnit.unit⟩)) where
  toFun displayedBehavior := fun query precondition =>
    ⟨displayedBehavior.head query precondition,
      displayedBehavior.child ⟨query, PUnit.unit⟩ precondition⟩
  invFun obligation := Display.M.mk
    ⟨fun query precondition => (obligation query precondition).1, fun
      | ⟨query, PUnit.unit⟩, precondition =>
          (obligation query precondition).2⟩
  left_inv displayedBehavior := by
    rw [← Display.M.dest_inj]
    rfl
  right_inv obligation := by
    funext query precondition
    rfl

/-- Apply one coinductive verified responder step. -/
def respondDisplayed
    (S : Display.{uA, uB, uC, uD} P)
    {behavior : PFunctor.M (P ⊸ X.{uA, uB})}
    (displayedBehavior : Display.M (Display.responder S) behavior)
    (query : P.A) (precondition : S.position query) :=
  respondDisplayedEquiv S behavior displayedBehavior query precondition

@[simp]
theorem respondDisplayed_post
    (S : Display.{uA, uB, uC, uD} P)
    {behavior : PFunctor.M (P ⊸ X.{uA, uB})}
    (displayedBehavior : Display.M (Display.responder S) behavior)
    (query : P.A) (precondition : S.position query) :
    (respondDisplayed S displayedBehavior query precondition).1 =
      displayedBehavior.head query precondition :=
  rfl

@[simp]
theorem respondDisplayed_next
    (S : Display.{uA, uB, uC, uD} P)
    {behavior : PFunctor.M (P ⊸ X.{uA, uB})}
    (displayedBehavior : Display.M (Display.responder S) behavior)
    (query : P.A) (precondition : S.position query) :
    (respondDisplayed S displayedBehavior query precondition).2 =
      displayedBehavior.child ⟨query, PUnit.unit⟩ precondition :=
  rfl

/-- Transporting a displayed behavior transports its complete dependent
`respondDisplayed` observation. This function-level form avoids exposing casts
in the postcondition and continuation projections separately. -/
theorem respondDisplayedEquiv_transport
    (S : Display.{uA, uB, uC, uD} P)
    {left right : PFunctor.M (P ⊸ X.{uA, uB})}
    (h : left = right)
    (displayedBehavior : Display.M (Display.responder S) left) :
    respondDisplayedEquiv S right (Display.M.transport h displayedBehavior) =
      h ▸ respondDisplayedEquiv S left displayedBehavior := by
  cases h
  rfl

/-- A cast-free, observation-shaped bisimulation for verified responder
behaviors. Related values return the same evidence for every query and
precondition and have related answer-selected continuations. -/
def IsDisplayedResponseBisimulation
    (S : Display.{uA, uB, uC, uD} P)
    (R : (behavior : PFunctor.M (P ⊸ X.{uA, uB})) →
      Display.M (Display.responder S) behavior →
      Display.M (Display.responder S) behavior → Prop) : Prop :=
  ∀ behavior left right, R behavior left right →
    ∀ query precondition,
      (respondDisplayed S left query precondition).1 =
          (respondDisplayed S right query precondition).1 ∧
        R (behavior.children ⟨query, PUnit.unit⟩)
          (respondDisplayed S left query precondition).2
          (respondDisplayed S right query precondition).2

/-- Observation-shaped responder bisimulation implies equality. -/
theorem respondDisplayed_bisim
    (S : Display.{uA, uB, uC, uD} P)
    (R : (behavior : PFunctor.M (P ⊸ X.{uA, uB})) →
      Display.M (Display.responder S) behavior →
      Display.M (Display.responder S) behavior → Prop)
    (hR : IsDisplayedResponseBisimulation S R)
    {behavior : PFunctor.M (P ⊸ X.{uA, uB})}
    {left right : Display.M (Display.responder S) behavior}
    (h : R behavior left right) : left = right := by
  apply Display.M.bisim R
  · intro current currentLeft currentRight hCurrent
    have hHead : currentLeft.head = currentRight.head := by
      funext query precondition
      exact (hR current currentLeft currentRight hCurrent
        query precondition).1
    refine
      ⟨currentLeft.head, currentLeft.child, currentRight.child,
        rfl, ?_, ?_⟩
    · rw [hHead]
      rfl
    · intro direction precondition
      rcases direction with ⟨query, trivialDirection⟩
      cases trivialDirection
      exact (hR current currentLeft currentRight hCurrent
        query precondition).2
  · exact h

/-- State-free proof-relevant behavior presented by a verified responder
state and its current invariant witness. -/
def verifiedBehavior
    (S : Display.{uA, uB, uC, uD} P)
    (R : Responder State P) (I : State → Type uF)
    (displayedR : Display.Coalgebra (Display.responder S) R.out I)
    (state : State) (witness : I state) :
    Display.M (Display.responder S) (R.behavior state) :=
  Display.Coalgebra.toM R I displayedR state witness

/-- The postcondition component of state-free `respondDisplayed` is exactly the
local displayed responder-coalgebra obligation. -/
theorem respondDisplayed_verifiedBehavior_post
    (S : Display.{uA, uB, uC, uD} P)
    (R : Responder State P) (I : State → Type uF)
    (displayedR : Display.Coalgebra (Display.responder S) R.out I)
    (state : State) (witness : I state)
    (query : P.A) (precondition : S.position query) :
    (respondDisplayed S (verifiedBehavior S R I displayedR state witness)
      query precondition).1 =
      ((Display.responderCoalgebraEquiv S R I) displayedR
        state witness query precondition).1 := by
  have h := congrArg Sigma.fst
    (Display.Coalgebra.dest_toM R I displayedR state witness)
  exact congrFun (congrFun h query) precondition

/-- The continuation component of state-free `respondDisplayed`, transported
along the ordinary behavior-child equation, is the verified behavior generated
from the locally preserved next-state witness. -/
theorem respondDisplayed_verifiedBehavior_next
    (S : Display.{uA, uB, uC, uD} P)
    (R : Responder State P) (I : State → Type uF)
    (displayedR : Display.Coalgebra (Display.responder S) R.out I)
    (state : State) (witness : I state)
    (query : P.A) (precondition : S.position query) :
    Display.M.transport (behavior_child R state query)
        (respondDisplayed S (verifiedBehavior S R I displayedR state witness)
          query precondition).2 =
      verifiedBehavior S R I displayedR (R.next state query)
        ((Display.responderCoalgebraEquiv S R I) displayedR
          state witness query precondition).2 := by
  have h := Display.Coalgebra.dest_toM R I displayedR state witness
  have hChild := congrArg
    (fun node => node.2 ⟨query, PUnit.unit⟩ precondition) h
  change
    Display.M.transport (behavior_child R state query)
        ((Display.M.dest
          (Display.Coalgebra.toM R I displayedR state witness)).2
            ⟨query, PUnit.unit⟩ precondition) = _
  rw [hChild]
  cases behavior_child R state query
  rfl

/-- Executing a displayed finite program against a state-free behavior
presented by a verified responder agrees with executing it against the
presenting responder, and presents the resulting final witness again. -/
theorem runFreeDisplayed_verifiedBehavior
    (S : Display.{uA, uB, uC, uD} P)
    (R : Responder State P) (I : State → Type uF)
    (displayedR : Display.Coalgebra (Display.responder S) R.out I)
    {E : Type uE} {F : E → Type uC'}
    (program : FreeM P E)
    (displayedProgram :
      FreeM.Displayed (S.toDisplayedAlgebra F) program)
    (state : State) (witness : I state) :
    transportRunEvidence F (Display.M (Display.responder S))
        (runFree_terminal R program state)
        (runFreeDisplayed S (Responder.terminal (P := P))
          (Display.Coalgebra.terminal (Display.responder S))
          displayedProgram (R.behavior state)
          (verifiedBehavior S R I displayedR state witness)) =
      let result := R.runFree program state
      let evidence :=
        runFreeDisplayed S R displayedR displayedProgram state witness
      ⟨evidence.1,
        verifiedBehavior S R I displayedR result.2 evidence.2⟩ := by
  induction program generalizing state with
  | pure value =>
      cases displayedProgram
      rfl
  | lift_bind query next ih =>
      rcases displayedProgram with ⟨precondition, displayedNext⟩
      let evidence :=
        (Display.responderCoalgebraEquiv S R I) displayedR
          state witness query precondition
      have hPost := respondDisplayed_verifiedBehavior_post S R I displayedR
        state witness query precondition
      have hNext := respondDisplayed_verifiedBehavior_next S R I displayedR
        state witness query precondition
      change transportRunEvidence F (Display.M (Display.responder S))
          (runFree_terminal R (FreeM.liftBind query next) state)
          (runFreeDisplayed S (Responder.terminal (P := P))
            (Display.Coalgebra.terminal (Display.responder S))
            (displayedNext (R.answer state query)
              (respondDisplayed S (verifiedBehavior S R I displayedR state witness)
                query precondition).1)
            ((Responder.terminal (P := P)).next (R.behavior state) query)
            (respondDisplayed S (verifiedBehavior S R I displayedR state witness)
              query precondition).2) = _
      rw [hPost]
      change transportRunEvidence F (Display.M (Display.responder S)) _
          (runFreeDisplayed S (Responder.terminal (P := P))
            (Display.Coalgebra.terminal (Display.responder S))
            (displayedNext (R.answer state query) evidence.1)
            (R.behavior (R.next state query))
            (Display.M.transport (behavior_child R state query)
              (respondDisplayed S (verifiedBehavior S R I displayedR state witness)
                query precondition).2)) = _
      rw [hNext]
      exact ih (R.answer state query)
        (displayedNext (R.answer state query) evidence.1)
        (R.next state query) evidence.2

/-- Reindex a state-free responder behavior by using it as the state of the
terminal responder and applying ordinary responder reindexing. -/
def reindexBehavior (f : Handler (FreeM Q) P)
    (behavior : PFunctor.M (Q ⊸ X.{uA', uB'})) :
    PFunctor.M (P ⊸ X.{uA, uB}) :=
  (Responder.reindex f (Responder.terminal (P := Q))).behavior behavior

/-- The state-free reindexing of a presented behavior agrees with reindexing
the presenting responder first. -/
theorem reindexBehavior_behavior (f : Handler (FreeM Q) P)
    (R : Responder State Q) (state : State) :
    reindexBehavior f (R.behavior state) =
      (Responder.reindex f R).behavior state := by
  let presented : State → PFunctor.M (P ⊸ X.{uA, uB}) :=
    fun state => reindexBehavior f (R.behavior state)
  have hOut : ∀ state,
      PFunctor.M.dest (presented state) =
        (P ⊸ X.{uA, uB}).map presented
          ((Responder.reindex f R).out state) := by
    intro current
    rw [show presented current =
      (Responder.reindex f (Responder.terminal (P := Q))).behavior
        (R.behavior current) by rfl]
    rw [DynSystem.dest_behavior]
    apply Sigma.ext
    · apply Lens.ext
      case h₁ =>
        intro trivialDirection
        exact Subsingleton.elim _ _
      case h₂ =>
        intro query
        funext trivialDirection
        cases trivialDirection
        exact congrArg Prod.fst
          (runFree_terminal R (f query) current)
    · apply heq_of_eq
      funext direction
      rcases direction with ⟨query, trivialDirection⟩
      cases trivialDirection
      exact congrArg
        (fun result =>
          (Responder.reindex f (Responder.terminal (P := Q))).behavior
            result.2)
        (runFree_terminal R (f query) current)
  exact congrFun
    (DynSystem.behavior_unique (Responder.reindex f R) presented hOut) state

@[simp]
theorem reindexBehavior_id
    (behavior : PFunctor.M (P ⊸ X.{uA, uB})) :
    reindexBehavior (Handler.id P) behavior = behavior := by
  calc
    reindexBehavior (Handler.id P) behavior =
        (Responder.reindex (Handler.id P)
          (Responder.terminal (P := P))).behavior behavior := by
      simpa only [terminal_behavior] using
        (reindexBehavior_behavior (Handler.id P)
          (Responder.terminal (P := P)) behavior)
    _ = behavior := by rw [Responder.reindex_id, terminal_behavior]

/-- State-free responder reindexing is contravariantly functorial in the
same categorical composition order as state-presented reindexing. -/
theorem reindexBehavior_comp
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
    {RPoly : PFunctor.{uA'', uB'}}
    (second : Handler (FreeM RPoly) Q)
    (first : Handler (FreeM Q) P)
    (behavior : PFunctor.M (RPoly ⊸ X.{uA'', uB'})) :
    reindexBehavior first (reindexBehavior second behavior) =
      reindexBehavior (second.comp first) behavior := by
  calc
    reindexBehavior first (reindexBehavior second behavior) =
        reindexBehavior first
          ((Responder.reindex second
            (Responder.terminal (P := RPoly))).behavior behavior) := rfl
    _ = (Responder.reindex first
          (Responder.reindex second
            (Responder.terminal (P := RPoly)))).behavior behavior :=
      reindexBehavior_behavior first
        (Responder.reindex second (Responder.terminal (P := RPoly))) behavior
    _ = reindexBehavior (second.comp first) behavior := by
      rw [Responder.reindex_comp]
      rfl

/-- Reindex state-free proof-relevant responder behavior through a displayed
free handler.  The construction is the state-free semantics of G3's
`reindexCoalgebra`, evaluated at the canonical terminal responder. -/
def reindexVerifiedBehavior
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : Handler (FreeM Q) P)
    (displayedF : Display.Handler S T f)
    (behavior : PFunctor.M (Q ⊸ X.{uA', uB'}))
    (displayedBehavior : Display.M (Display.responder T) behavior) :
    Display.M (Display.responder S) (reindexBehavior f behavior) :=
  verifiedBehavior S
    (Responder.reindex f (Responder.terminal (P := Q)))
    (Display.M (Display.responder T))
    (Responder.reindexCoalgebra S T f displayedF
      (Responder.terminal (P := Q))
      (Display.Coalgebra.terminal (Display.responder T)))
    behavior displayedBehavior

/-- The postcondition returned by one state-free verified reindexing step is
exactly the postcondition produced by executing the displayed handler program
against the target displayed behavior. -/
theorem respondDisplayed_reindexVerifiedBehavior_post
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : Handler (FreeM Q) P)
    (displayedF : Display.Handler S T f)
    (behavior : PFunctor.M (Q ⊸ X.{uA', uB'}))
    (displayedBehavior : Display.M (Display.responder T) behavior)
    (query : P.A) (precondition : S.position query) :
    (respondDisplayed S
      (reindexVerifiedBehavior S T f displayedF behavior displayedBehavior)
      query precondition).1 =
      (runFreeDisplayed T (Responder.terminal (P := Q))
        (Display.Coalgebra.terminal (Display.responder T))
        (displayedF query precondition) behavior displayedBehavior).1 := by
  change
    (respondDisplayed S
      (verifiedBehavior S
        (Responder.reindex f (Responder.terminal (P := Q)))
        (Display.M (Display.responder T))
        (Responder.reindexCoalgebra S T f displayedF
          (Responder.terminal (P := Q))
          (Display.Coalgebra.terminal (Display.responder T)))
        behavior displayedBehavior) query precondition).1 = _
  rw [respondDisplayed_verifiedBehavior_post]
  rfl

/-- The continuation returned by one state-free verified reindexing step is
the recursively reindexed target continuation produced by displayed program
execution, after the canonical ordinary behavior-child transport. -/
theorem respondDisplayed_reindexVerifiedBehavior_next
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : Handler (FreeM Q) P)
    (displayedF : Display.Handler S T f)
    (behavior : PFunctor.M (Q ⊸ X.{uA', uB'}))
    (displayedBehavior : Display.M (Display.responder T) behavior)
    (query : P.A) (precondition : S.position query) :
    let result := (Responder.terminal (P := Q)).runFree (f query) behavior
    let displayedResult :=
      runFreeDisplayed T (Responder.terminal (P := Q))
        (Display.Coalgebra.terminal (Display.responder T))
        (displayedF query precondition) behavior displayedBehavior
    Display.M.transport
        (behavior_child
          (Responder.reindex f (Responder.terminal (P := Q))) behavior query)
        (respondDisplayed S
          (reindexVerifiedBehavior S T f displayedF behavior displayedBehavior)
          query precondition).2 =
      reindexVerifiedBehavior S T f displayedF result.2 displayedResult.2 := by
  exact respondDisplayed_verifiedBehavior_next S
    (Responder.reindex f (Responder.terminal (P := Q)))
    (Display.M (Display.responder T))
    (Responder.reindexCoalgebra S T f displayedF
      (Responder.terminal (P := Q))
      (Display.Coalgebra.terminal (Display.responder T)))
    behavior displayedBehavior query precondition

/-- State-free verified behavior reindexing preserves identity handlers,
after the canonical equality of the underlying ordinary behaviors. -/
theorem reindexVerifiedBehavior_id
    (S : Display.{uA, uB, uC, uD} P)
    (behavior : PFunctor.M (P ⊸ X.{uA, uB}))
    (displayedBehavior : Display.M (Display.responder S) behavior) :
    Display.M.transport (reindexBehavior_id behavior)
        (reindexVerifiedBehavior S S (Handler.id P)
          (Display.Handler.id S) behavior displayedBehavior) =
      displayedBehavior := by
  apply IPFunctor.IM.ext
  rw [Display.M.toM_transport]
  let R := fun
      (left right : PFunctor.M
        (Display.mStep (Display.responder S)).sigmaPFunctor) =>
    ∃ current displayed,
      left = (reindexVerifiedBehavior S S (Handler.id P)
        (Display.Handler.id S) current displayed).toM ∧
      right = displayed.toM
  apply PFunctor.M.bisim R
  · intro left right h
    rcases h with ⟨current, displayed, rfl, rfl⟩
    let reindexed := reindexVerifiedBehavior S S (Handler.id P)
      (Display.Handler.id S) current displayed
    have hShape :
        (⟨reindexBehavior (Handler.id P) current, reindexed.head⟩ :
          Σ tree, (Display.responder S).position tree.head) =
        ⟨current, displayed.head⟩ := by
      apply Sigma.ext (reindexBehavior_id current)
      apply heq_of_eq
      funext query precondition
      change
        (respondDisplayed S reindexed query precondition).1 =
          (respondDisplayed S displayed query precondition).1
      rw [respondDisplayed_reindexVerifiedBehavior_post]
      rfl
    let hDirection :
        (Display.mStep (Display.responder S)).B
            (reindexBehavior (Handler.id P) current) reindexed.head =
          (Display.mStep (Display.responder S)).B current displayed.head :=
      congrArg (Display.mStep (Display.responder S)).sigmaPFunctor.B hShape
    have hDirection_rfl : hDirection = rfl := Subsingleton.elim _ _
    let leftChildren :
        (Display.mStep (Display.responder S)).B current displayed.head →
          PFunctor.M
            (Display.mStep (Display.responder S)).sigmaPFunctor :=
      fun direction =>
        (IPFunctor.IM.dest reindexed).2 (hDirection.symm ▸ direction) |>.toM
    refine ⟨⟨current, displayed.head⟩, leftChildren,
      (fun direction =>
        (displayed.child direction.1 direction.2).toM), ?_, ?_, ?_⟩
    · rw [IPFunctor.IM.toM_dest]
      change
        (⟨⟨reindexBehavior (Handler.id P) current, reindexed.head⟩,
            fun direction => ((IPFunctor.IM.dest reindexed).2 direction).toM⟩ :
          (Display.mStep (Display.responder S)).sigmaPFunctor.Obj
            (PFunctor.M
              (Display.mStep (Display.responder S)).sigmaPFunctor)) = _
      apply Sigma.ext hShape
      apply heq_of_eq
      funext direction
      unfold leftChildren
      rw [hDirection_rfl]
    · rw [IPFunctor.IM.toM_dest]
      rfl
    · intro direction
      rcases direction with ⟨⟨query, trivialDirection⟩, precondition⟩
      cases trivialDirection
      let result := (Responder.terminal (P := P)).runFree
        (Handler.id P query) current
      let displayedResult := runFreeDisplayed S
        (Responder.terminal (P := P))
        (Display.Coalgebra.terminal (Display.responder S))
        (Display.Handler.id S query precondition) current displayed
      refine ⟨result.2, displayedResult.2, ?_, ?_⟩
      · have hNext := respondDisplayed_reindexVerifiedBehavior_next S S
          (Handler.id P) (Display.Handler.id S) current displayed
          query precondition
        have hToM := congrArg IPFunctor.IM.toM hNext
        unfold leftChildren
        rw [hDirection_rfl]
        change
          (respondDisplayed S reindexed query precondition).2.toM = _
        simpa only [Display.M.toM_transport] using hToM
      · have hObligation := reindexCoalgebra_id_obligation S
          (Responder.terminal (P := P))
          (Display.Coalgebra.terminal (Display.responder S))
          current displayed query precondition
        exact congrArg IPFunctor.IM.toM (congrArg Prod.snd hObligation)
  · exact ⟨behavior, displayedBehavior, rfl, rfl⟩

/-- Successive state-free verified behavior reindexing agrees with reindexing
by the displayed Kleisli composite, after the canonical equality of the
underlying ordinary behaviors. -/
theorem reindexVerifiedBehavior_comp
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
    {RPoly : PFunctor.{uA'', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Q)
    (U : Display.{uA'', uB', uC'', uD''} RPoly)
    (second : Handler (FreeM RPoly) Q)
    (dsecond : Display.Handler T U second)
    (first : Handler (FreeM Q) P)
    (dfirst : Display.Handler S T first)
    (behavior : PFunctor.M (RPoly ⊸ X.{uA'', uB'}))
    (displayedBehavior : Display.M (Display.responder U) behavior) :
    Display.M.transport (reindexBehavior_comp second first behavior)
        (reindexVerifiedBehavior S T first dfirst
          (reindexBehavior second behavior)
          (reindexVerifiedBehavior T U second dsecond
            behavior displayedBehavior)) =
      reindexVerifiedBehavior S U (second.comp first)
        (dsecond.comp dfirst) behavior displayedBehavior := by
  apply IPFunctor.IM.ext
  rw [Display.M.toM_transport]
  let R := fun
      (left right : PFunctor.M
        (Display.mStep (Display.responder S)).sigmaPFunctor) =>
    ∃ current displayed,
      left = (reindexVerifiedBehavior S T first dfirst
        (reindexBehavior second current)
        (reindexVerifiedBehavior T U second dsecond current displayed)).toM ∧
      right = (reindexVerifiedBehavior S U (second.comp first)
        (dsecond.comp dfirst) current displayed).toM
  apply PFunctor.M.bisim R
  · intro left right h
    rcases h with ⟨current, displayed, rfl, rfl⟩
    let middle := reindexVerifiedBehavior T U second dsecond
      current displayed
    let sequential := reindexVerifiedBehavior S T first dfirst
      (reindexBehavior second current) middle
    let composite := reindexVerifiedBehavior S U (second.comp first)
      (dsecond.comp dfirst) current displayed
    have hShape :
        (⟨reindexBehavior first (reindexBehavior second current),
            sequential.head⟩ :
          Σ tree, (Display.responder S).position tree.head) =
        ⟨reindexBehavior (second.comp first) current,
          composite.head⟩ := by
      apply Sigma.ext (reindexBehavior_comp second first current)
      apply Function.hfunext rfl
      intro query query' hQuery
      cases hQuery
      apply Function.hfunext rfl
      intro precondition precondition' hPrecondition
      cases hPrecondition
      let terminalR := Responder.terminal (P := RPoly)
      let terminalD := Display.Coalgebra.terminal (Display.responder U)
      let leftObligation :=
        (Display.responderCoalgebraEquiv S
          (Responder.reindex first (Responder.reindex second terminalR))
          (Display.M (Display.responder U)))
          (Responder.reindexCoalgebra S T first dfirst
            (Responder.reindex second terminalR)
            (Responder.reindexCoalgebra T U second dsecond terminalR terminalD))
          current displayed query precondition
      let rightObligation :=
        (Display.responderCoalgebraEquiv S
          (Responder.reindex (second.comp first) terminalR)
          (Display.M (Display.responder U)))
          (Responder.reindexCoalgebra S U (second.comp first)
            (dsecond.comp dfirst) terminalR terminalD)
          current displayed query precondition
      let runEq := runFree_reindex second terminalR (first query) current
      have hObligation :
          transportRunEvidence (S.direction query precondition)
              (Display.M (Display.responder U)) runEq leftObligation =
            rightObligation := reindexCoalgebra_comp_obligation S T U
        first dfirst second dsecond (Responder.terminal (P := RPoly))
        (Display.Coalgebra.terminal (Display.responder U))
        current displayed query precondition
      let leftResult := (Responder.reindex second terminalR).runFree
        (first query) current
      let rightResult := terminalR.runFree ((first query).liftM second) current
      let Evidence := fun result :
          P.B query × PFunctor.M (RPoly ⊸ X.{uA'', uB'}) =>
        S.direction query precondition result.1 ×
          Display.M (Display.responder U) result.2
      have hSigma :
          (⟨leftResult, leftObligation⟩ : Σ result, Evidence result) =
            ⟨rightResult, rightObligation⟩ := by
        apply Sigma.ext runEq
        exact (transportRunEvidence_heq _ _ runEq leftObligation).symm.trans
          (heq_of_eq hObligation)
      have hPost : leftObligation.1 ≍ rightObligation.1 :=
        congr_arg_heq (fun result : Σ result, Evidence result =>
          result.2.1) hSigma
      let secondR := Responder.reindex second terminalR
      let secondD := Responder.reindexCoalgebra T U second dsecond
        terminalR terminalD
      let outerResult := (Responder.terminal (P := Q)).runFree
        (first query) (reindexBehavior second current)
      let stateRun := secondR.runFree (first query) current
      let presentedResult :
          P.B query × PFunctor.M (Q ⊸ X.{uA', uB}) :=
        ⟨stateRun.1, secondR.behavior stateRun.2⟩
      let outerEvidence := runFreeDisplayed T
        (Responder.terminal (P := Q))
        (Display.Coalgebra.terminal (Display.responder T))
        (dfirst query precondition) (reindexBehavior second current) middle
      let mappedStateEvidence :
          S.direction query precondition presentedResult.1 ×
            Display.M (Display.responder T)
              presentedResult.2 :=
        ⟨leftObligation.1,
          verifiedBehavior T secondR (Display.M (Display.responder U))
            secondD stateRun.2 leftObligation.2⟩
      let presentationEq := runFree_terminal secondR (first query) current
      have hPresentation :
          transportRunEvidence (S.direction query precondition)
              (Display.M (Display.responder T)) presentationEq outerEvidence =
            mappedStateEvidence := by
        have h := runFreeDisplayed_verifiedBehavior T secondR
          (Display.M (Display.responder U)) secondD
          (first query) (dfirst query precondition) current displayed
        change transportRunEvidence _ _ presentationEq outerEvidence = _ at h
        change transportRunEvidence _ _ presentationEq outerEvidence =
          mappedStateEvidence
        exact h
      let PresentationEvidence := fun result :
          P.B query × PFunctor.M (Q ⊸ X.{uA', uB}) =>
        S.direction query precondition result.1 ×
          Display.M (Display.responder T) result.2
      have hPresentationSigma :
          (⟨outerResult, outerEvidence⟩ :
            Σ result, PresentationEvidence result) =
          ⟨presentedResult, mappedStateEvidence⟩ := by
        apply Sigma.ext presentationEq
        exact
          (transportRunEvidence_heq _ _ presentationEq outerEvidence).symm.trans
            (heq_of_eq hPresentation)
      have hOuterPost : outerEvidence.1 ≍ leftObligation.1 :=
        congr_arg_heq
          (fun result : Σ result, PresentationEvidence result => result.2.1)
          hPresentationSigma
      have hLeft :
          (respondDisplayed S sequential query precondition).1 = outerEvidence.1 := by
        exact respondDisplayed_reindexVerifiedBehavior_post S T first dfirst
          (reindexBehavior second current) middle query precondition
      have hRight :
          (respondDisplayed S composite query precondition).1 = rightObligation.1 := by
        have h := respondDisplayed_reindexVerifiedBehavior_post S U
          (second.comp first) (dsecond.comp dfirst)
          current displayed query precondition
        change (respondDisplayed S composite query precondition).1 = _ at h
        change _ = rightObligation.1
        exact h
      exact (heq_of_eq hLeft).trans
        (hOuterPost.trans (hPost.trans (heq_of_eq hRight.symm)))
    let hDirection :
        (Display.mStep (Display.responder S)).B
            (reindexBehavior first (reindexBehavior second current))
            sequential.head =
          (Display.mStep (Display.responder S)).B
            (reindexBehavior (second.comp first) current) composite.head :=
      congrArg (Display.mStep (Display.responder S)).sigmaPFunctor.B hShape
    have hDirection_rfl : hDirection = rfl := Subsingleton.elim _ _
    let leftChildren :
        (Display.mStep (Display.responder S)).B
            (reindexBehavior (second.comp first) current) composite.head →
          PFunctor.M
            (Display.mStep (Display.responder S)).sigmaPFunctor :=
      fun direction =>
        (IPFunctor.IM.dest sequential).2 (hDirection.symm ▸ direction) |>.toM
    refine
      ⟨⟨reindexBehavior (second.comp first) current, composite.head⟩,
        leftChildren,
        (fun direction =>
          ((IPFunctor.IM.dest composite).2 direction).toM), ?_, ?_, ?_⟩
    · rw [IPFunctor.IM.toM_dest]
      change
        (⟨⟨reindexBehavior first (reindexBehavior second current),
              sequential.head⟩,
            fun direction =>
              ((IPFunctor.IM.dest sequential).2 direction).toM⟩ :
          (Display.mStep (Display.responder S)).sigmaPFunctor.Obj
            (PFunctor.M
              (Display.mStep (Display.responder S)).sigmaPFunctor)) = _
      apply Sigma.ext hShape
      apply heq_of_eq
      funext direction
      unfold leftChildren
      rw [hDirection_rfl]
    · rw [IPFunctor.IM.toM_dest]
      rfl
    · intro direction
      rcases direction with ⟨⟨query, trivialDirection⟩, precondition⟩
      cases trivialDirection
      let terminalR := Responder.terminal (P := RPoly)
      let terminalD := Display.Coalgebra.terminal (Display.responder U)
      let secondR := Responder.reindex second terminalR
      let secondD := Responder.reindexCoalgebra T U second dsecond
        terminalR terminalD
      let outerResult := (Responder.terminal (P := Q)).runFree
        (first query) (reindexBehavior second current)
      let outerEvidence := runFreeDisplayed T
        (Responder.terminal (P := Q))
        (Display.Coalgebra.terminal (Display.responder T))
        (dfirst query precondition) (reindexBehavior second current) middle
      let stateRun := secondR.runFree (first query) current
      let stateEvidence := runFreeDisplayed T secondR secondD
        (dfirst query precondition) current displayed
      let presentedResult :
          P.B query × PFunctor.M (Q ⊸ X.{uA', uB}) :=
        ⟨stateRun.1, secondR.behavior stateRun.2⟩
      let mappedStateEvidence :
          S.direction query precondition presentedResult.1 ×
            Display.M (Display.responder T) presentedResult.2 :=
        ⟨stateEvidence.1,
          verifiedBehavior T secondR (Display.M (Display.responder U))
            secondD stateRun.2 stateEvidence.2⟩
      let presentationEq := runFree_terminal secondR (first query) current
      let PresentationEvidence := fun result :
          P.B query × PFunctor.M (Q ⊸ X.{uA', uB}) =>
        S.direction query precondition result.1 ×
          Display.M (Display.responder T) result.2
      have hPresentation :
          transportRunEvidence (S.direction query precondition)
              (Display.M (Display.responder T)) presentationEq outerEvidence =
            mappedStateEvidence := by
        have h := runFreeDisplayed_verifiedBehavior T secondR
          (Display.M (Display.responder U)) secondD
          (first query) (dfirst query precondition) current displayed
        change transportRunEvidence _ _ presentationEq outerEvidence = _ at h
        exact h
      have hPresentationSigma :
          (⟨outerResult, outerEvidence⟩ :
            Σ result, PresentationEvidence result) =
          ⟨presentedResult, mappedStateEvidence⟩ := by
        apply Sigma.ext presentationEq
        exact
          (transportRunEvidence_heq _ _ presentationEq outerEvidence).symm.trans
            (heq_of_eq hPresentation)
      let compositeResult :=
        terminalR.runFree ((first query).liftM second) current
      let compositeEvidence := runFreeDisplayed U terminalR terminalD
        (T.liftM U (first query) (dfirst query precondition) second dsecond)
        current displayed
      let runEq := runFree_reindex second terminalR (first query) current
      let StateEvidence := fun result :
          P.B query × PFunctor.M (RPoly ⊸ X.{uA'', uB'}) =>
        S.direction query precondition result.1 ×
          Display.M (Display.responder U) result.2
      have hState :
          transportRunEvidence (S.direction query precondition)
              (Display.M (Display.responder U)) runEq stateEvidence =
            compositeEvidence :=
        reindexCoalgebra_comp_obligation S T U first dfirst second dsecond
          terminalR terminalD current displayed query precondition
      have hStateSigma :
          (⟨stateRun, stateEvidence⟩ : Σ result, StateEvidence result) =
            ⟨compositeResult, compositeEvidence⟩ := by
        apply Sigma.ext runEq
        exact (transportRunEvidence_heq _ _ runEq stateEvidence).symm.trans
          (heq_of_eq hState)
      let continueOuter := fun
          result : Σ result, PresentationEvidence result =>
        (reindexVerifiedBehavior S T first dfirst result.1.2 result.2.2).toM
      let continueNested := fun
          result : Σ result, StateEvidence result =>
        (reindexVerifiedBehavior S T first dfirst
          (reindexBehavior second result.1.2)
          (reindexVerifiedBehavior T U second dsecond
            result.1.2 result.2.2)).toM
      have hPresented := congrArg continueOuter hPresentationSigma
      have hComposed := congrArg continueNested hStateSigma
      refine ⟨compositeResult.2, compositeEvidence.2, ?_, ?_⟩
      · unfold leftChildren
        rw [hDirection_rfl]
        change (respondDisplayed S sequential query precondition).2.toM = _
        have hOuterNext := respondDisplayed_reindexVerifiedBehavior_next S T first dfirst
          (reindexBehavior second current) middle query precondition
        have hOuterToM := congrArg IPFunctor.IM.toM hOuterNext
        calc
          (respondDisplayed S sequential query precondition).2.toM =
              (reindexVerifiedBehavior S T first dfirst
                outerResult.2 outerEvidence.2).toM := by
            simpa only [Display.M.toM_transport] using hOuterToM
          _ = (reindexVerifiedBehavior S T first dfirst
                (reindexBehavior second stateRun.2)
                (reindexVerifiedBehavior T U second dsecond
                  stateRun.2 stateEvidence.2)).toM := hPresented
          _ = (reindexVerifiedBehavior S T first dfirst
                (reindexBehavior second compositeResult.2)
                (reindexVerifiedBehavior T U second dsecond
                  compositeResult.2 compositeEvidence.2)).toM := hComposed
      · have hCompositeNext := respondDisplayed_reindexVerifiedBehavior_next S U
          (second.comp first) (dsecond.comp dfirst)
          current displayed query precondition
        have hCompositeToM := congrArg IPFunctor.IM.toM hCompositeNext
        change (respondDisplayed S composite query precondition).2.toM = _
        simpa [Display.M.toM_transport, compositeResult, compositeEvidence,
          composite, terminalR, terminalD] using hCompositeToM
  · exact ⟨behavior, displayedBehavior, rfl, rfl⟩

end Responder
end PFunctor
