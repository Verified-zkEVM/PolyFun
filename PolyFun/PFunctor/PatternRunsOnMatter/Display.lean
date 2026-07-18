/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Category
public import PolyFun.PFunctor.Dynamical.Responder.Behavior
public import PolyFun.PFunctor.PatternRunsOnMatter.Applications

/-!
# Displayed execution as evaluated pattern running on matter

This file identifies the responder semantics used by polynomial displays with
the existing Pattern-Runs-on-Matter action.  A free handler is first encoded
as a lens into `FreeP`; its finite program runs against the responder system;
the synchronized nodes are evaluated through the internal hom; and the
resulting `FreeP X` tree is collapsed along its unique path.

The evaluation step is essential.  Raw `FreeP.runOnSystem` only constructs
the Xi synchronization tree and retains paired pattern/matter nodes.  The
comparison below therefore uses `FreeP.runAgainstSystem`, which composes that
action with `FreeP.evaluation`.

For proof-relevant displays, the same equality transports the evidence
produced by `Responder.runFreeDisplayed`.  This does not identify displayed
witnesses by proof irrelevance: it changes only their ordinary execution
index and retains the complete `Type`-valued evidence.
-/

@[expose] public section

universe uA uA' uB uB' uC uD uE uF uS uV

namespace PFunctor

namespace Responder

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
variable {State : Type uS}

/-- The evaluated Pattern-Runs-on-Matter object obtained by running one free
program against a responder state.  Its payload records the returned value
and the responder state reached at the selected complete path. -/
def runAgainstProgramObj {E : Type uV}
    (R : Responder State Q) (program : FreeM Q E) (state : State) :
    (FreeP X.{uA', uB'}).Obj (E × State) :=
  Lens.mapObj (FreeP.runAgainstSystem Q X.{uA', uB'} R)
    ⟨((FreeP.encode program).1, state), fun direction =>
      ((FreeP.encode program).2 direction.1, direction.2)⟩

/-- Decoding `runAgainstProgramObj` is exactly `DynSystem.runPattern`
followed by internal-hom evaluation. -/
theorem decode_runAgainstProgramObj {E : Type uV}
    (R : Responder State Q) (program : FreeM Q E) (state : State) :
    FreeP.decode (runAgainstProgramObj R program state) =
      (R.runPattern program state).mapLens
        (FreeP.evaluation Q X.{uA', uB'}) := by
  unfold runAgainstProgramObj FreeP.runAgainstSystem
  rw [Lens.mapObj_comp, FreeP.decode_map]
  rfl

/-- Evaluation and unique-path collapse of `runPattern` is structural
responder execution. -/
theorem collapseUnit_runPattern {E : Type uV}
    (R : Responder State Q) (program : FreeM Q E) (state : State) :
    FreeM.collapseUnit
        ((R.runPattern program state).mapLens
          (FreeP.evaluation Q X.{uA', uB'})) =
      R.runFree program state := by
  induction program generalizing state with
  | pure value =>
      rw [DynSystem.runPattern_pure]
      rfl
  | lift_bind query next ih =>
      change FreeM.collapseUnit
          ((R.runPattern (.liftBind query next) state).mapLens
            (FreeP.evaluation Q X.{uA', uB'})) =
        R.runFree (.liftBind query next) state
      rw [DynSystem.runPattern_liftBind]
      change FreeM.collapseUnit
          (FreeM.liftBind PUnit.unit (fun _ =>
            (R.runPattern (next (R.answer state query))
              (R.next state query)).mapLens
                (FreeP.evaluation Q X.{uA', uB'}))) = _
      change FreeM.collapseUnit
        ((R.runPattern (next (R.answer state query))
          (R.next state query)).mapLens
            (FreeP.evaluation Q X.{uA', uB'})) = _
      exact ih (R.answer state query) (R.next state query)

/-- The result payload of the complete evaluated pattern action. -/
def runAgainstResult {E : Type uV}
    (R : Responder State Q) (program : FreeM Q E) (state : State) :
    E × State :=
  (Lens.mapObj FreeP.collapseUnit
    (runAgainstProgramObj R program state)).2 PUnit.unit

/-- The evaluated Pattern-Runs-on-Matter result is exactly `runFree`,
including both the returned value and the reached responder state. -/
theorem runAgainstResult_eq_runFree {E : Type uV}
    (R : Responder State Q) (program : FreeM Q E) (state : State) :
    runAgainstResult R program state = R.runFree program state := by
  unfold runAgainstResult
  rw [FreeP.collapseUnit_mapObj, decode_runAgainstProgramObj,
    collapseUnit_runPattern]

/-- Reconstruct responder reindexing categorically: encode the handler as a
free-polynomial lens, run it against the responder, evaluate synchronized
nodes, and collapse the resulting free `X`-tree.

This comparison is stated in the homogeneous interface-universe fragment
because `Responder State P` and `Responder State Q` instantiate their terminal
identity polynomials in the universes of `P` and `Q`, while the final
`FreeP.collapseUnit` expects one fixed instantiation of `X`. The structural
handler/lens equivalence and target-only evaluated APIs above do not require
this restriction. -/
def reindexViaRunAgainst
    {P Q : PFunctor.{uA, uB}}
    (f : Handler (FreeM Q) P) (R : Responder State Q) :
    Responder State P :=
  Lens.curry
    (FreeP.collapseUnit ∘ₗ
      (FreeP.runAgainstSystem Q X.{uA, uB} R ∘ₗ
        ((Handler.toFreeLens f ⊗ₗ Lens.id (selfMonomial State)) ∘ₗ
          (Lens.Equiv.tensorComm (selfMonomial State) P).toLens)))

/-- The categorical Pattern-Runs-on-Matter reconstruction is the existing
contravariant responder reindexing operation. -/
theorem reindexViaRunAgainst_eq_reindex
    {P Q : PFunctor.{uA, uB}}
    (f : Handler (FreeM Q) P) (R : Responder State Q) :
    reindexViaRunAgainst f R = reindex f R := by
  apply Responder.ext
  · intro state query
    unfold Responder.answer DynSystem.expose reindexViaRunAgainst reindex
      Responder.mk' Lens.curry Lens.comp Lens.tensorMap
      Lens.Equiv.tensorComm Handler.toFreeLens FreeP.collapseUnit
      sectionLens Lens.toLinear Lens.id
    change Prod.fst (runAgainstResult R (f query) state) =
      Prod.fst (R.runFree (f query) state)
    exact congrArg Prod.fst (runAgainstResult_eq_runFree R (f query) state)
  · intro state query
    unfold Responder.next DynSystem.update reindexViaRunAgainst reindex
      Responder.mk' Lens.curry Lens.comp Lens.tensorMap
      Lens.Equiv.tensorComm Handler.toFreeLens FreeP.collapseUnit Lens.id
    change Prod.snd (runAgainstResult R (f query) state) =
      Prod.snd (R.runFree (f query) state)
    exact congrArg Prod.snd (runAgainstResult_eq_runFree R (f query) state)

/-- State-free responder reindexing is the behavior generated by the same
evaluated Pattern-Runs-on-Matter reconstruction. -/
theorem reindexBehavior_eq_runAgainst
    {P Q : PFunctor.{uA, uB}}
    (f : Handler (FreeM Q) P)
    (behavior : PFunctor.M (Q ⊸ X.{uA, uB})) :
    reindexBehavior f behavior =
      (reindexViaRunAgainst f (Responder.terminal (P := Q))).behavior
        behavior := by
  rw [reindexViaRunAgainst_eq_reindex]
  rfl

section Displayed

variable (T : Display.{uA', uB', uC, uD} Q)

/-- Transport displayed execution evidence from the ordinary `runFree`
index to the extensionally equal evaluated Pattern-Runs-on-Matter result. -/
def runAgainstDisplayed
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    {E : Type uV} {F : E → Type uE}
    {program : FreeM Q E}
    (displayedProgram :
      FreeM.Displayed (T.toDisplayedAlgebra F) program)
    (state : State) (witness : I state) :
    F (runAgainstResult R program state).1 ×
      I (runAgainstResult R program state).2 :=
  transportRunEvidence F I
    (runAgainstResult_eq_runFree R program state).symm
    (runFreeDisplayed T R displayedR displayedProgram state witness)

/-- Transporting the Pattern-Runs-on-Matter evidence back along the semantic
identification recovers `runFreeDisplayed` exactly. -/
theorem runAgainstDisplayed_eq_runFreeDisplayed
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    {E : Type uV} {F : E → Type uE}
    {program : FreeM Q E}
    (displayedProgram :
      FreeM.Displayed (T.toDisplayedAlgebra F) program)
    (state : State) (witness : I state) :
    transportRunEvidence F I
        (runAgainstResult_eq_runFree R program state)
        (runAgainstDisplayed T R displayedR displayedProgram state witness) =
      runFreeDisplayed T R displayedR displayedProgram state witness := by
  unfold runAgainstDisplayed
  rw [transportRunEvidence_trans]
  rw [transportRunEvidence_proof_irrel F I
    ((runAgainstResult_eq_runFree R program state).symm.trans
      (runAgainstResult_eq_runFree R program state)) rfl]
  rfl

/-- A displayed reindexing step is the evidence produced by
`runFreeDisplayed`, transported along the ordinary equality with evaluated
Pattern Runs on Matter.  This does not construct a separate displayed Xi
action: it retains both the answer-dependent postcondition and the
reached-state invariant while changing only their ordinary result index. -/
theorem runAgainstDisplayed_eq_reindexCoalgebra
    (S : Display.{uA, uB, uC, uD} P)
    (f : Handler (FreeM Q) P)
    (displayedF : Display.Handler S T f)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    (state : State) (witness : I state)
    (query : P.A) (contract : S.position query) :
    runAgainstDisplayed T R displayedR (displayedF query contract)
        state witness =
      transportRunEvidence (S.direction query contract) I
        (runAgainstResult_eq_runFree R (f query) state).symm
        ((Display.responderCoalgebraEquiv S (reindex f R) I)
          (reindexCoalgebra S T f displayedF R displayedR)
          state witness query contract) :=
  rfl

/-- The postcondition exposed by state-free verified reindexing is the
postcondition obtained from evaluated Pattern Runs on Matter. -/
theorem respondDisplayed_reindexVerifiedBehavior_post_runAgainst
    (S : Display.{uA, uB, uC, uD} P)
    (f : Handler (FreeM Q) P)
    (displayedF : Display.Handler S T f)
    (behavior : PFunctor.M (Q ⊸ X.{uA', uB'}))
    (displayedBehavior : Display.M (Display.responder T) behavior)
    (query : P.A) (contract : S.position query) :
    (respondDisplayed S
      (reindexVerifiedBehavior S T f displayedF behavior displayedBehavior)
      query contract).1 =
      (transportRunEvidence (S.direction query contract)
        (Display.M (Display.responder T))
        (runAgainstResult_eq_runFree
          (Responder.terminal (P := Q)) (f query) behavior)
        (runAgainstDisplayed T (Responder.terminal (P := Q))
          (Display.Coalgebra.terminal (Display.responder T))
          (displayedF query contract) behavior displayedBehavior)).1 := by
  rw [respondDisplayed_reindexVerifiedBehavior_post]
  rw [runAgainstDisplayed_eq_runFreeDisplayed]

/-- The continuation exposed by state-free verified reindexing is recursively
reindexed from the target continuation carried by evaluated Pattern Runs on
Matter.  The ordinary result transport is explicit; the proof-relevant
continuation itself is not truncated or identified by proof irrelevance. -/
theorem respondDisplayed_reindexVerifiedBehavior_next_runAgainst
    (S : Display.{uA, uB, uC, uD} P)
    (f : Handler (FreeM Q) P)
    (displayedF : Display.Handler S T f)
    (behavior : PFunctor.M (Q ⊸ X.{uA', uB'}))
    (displayedBehavior : Display.M (Display.responder T) behavior)
    (query : P.A) (contract : S.position query) :
    let result := (Responder.terminal (P := Q)).runFree (f query) behavior
    let displayedResult :=
      transportRunEvidence (S.direction query contract)
        (Display.M (Display.responder T))
        (runAgainstResult_eq_runFree
          (Responder.terminal (P := Q)) (f query) behavior)
        (runAgainstDisplayed T (Responder.terminal (P := Q))
          (Display.Coalgebra.terminal (Display.responder T))
          (displayedF query contract) behavior displayedBehavior)
    Display.M.transport
        (behavior_child
          (reindex f (Responder.terminal (P := Q))) behavior query)
        (respondDisplayed S
          (reindexVerifiedBehavior S T f displayedF behavior
            displayedBehavior) query contract).2 =
      reindexVerifiedBehavior S T f displayedF
        result.2 displayedResult.2 := by
  let alternativeEvidence :=
    runAgainstDisplayed T (Responder.terminal (P := Q))
      (Display.Coalgebra.terminal (Display.responder T))
      (displayedF query contract) behavior displayedBehavior
  have hEvidence :
      transportRunEvidence (S.direction query contract)
          (Display.M (Display.responder T))
          (runAgainstResult_eq_runFree
            (Responder.terminal (P := Q)) (f query) behavior)
          alternativeEvidence =
        runFreeDisplayed T (Responder.terminal (P := Q))
          (Display.Coalgebra.terminal (Display.responder T))
          (displayedF query contract) behavior displayedBehavior :=
    runAgainstDisplayed_eq_runFreeDisplayed T
      (Responder.terminal (P := Q))
      (Display.Coalgebra.terminal (Display.responder T))
      (displayedF query contract) behavior displayedBehavior
  rw [show
    transportRunEvidence (S.direction query contract)
        (Display.M (Display.responder T))
        (runAgainstResult_eq_runFree
          (Responder.terminal (P := Q)) (f query) behavior)
        (runAgainstDisplayed T (Responder.terminal (P := Q))
          (Display.Coalgebra.terminal (Display.responder T))
          (displayedF query contract) behavior displayedBehavior) =
      runFreeDisplayed T (Responder.terminal (P := Q))
        (Display.Coalgebra.terminal (Display.responder T))
        (displayedF query contract) behavior displayedBehavior by
      exact hEvidence]
  exact respondDisplayed_reindexVerifiedBehavior_next S T f displayedF
    behavior displayedBehavior query contract

end Displayed

end Responder
end PFunctor
