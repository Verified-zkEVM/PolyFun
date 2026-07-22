/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Handler
public import PolyFun.PFunctor.Dynamical.Responder.Display
public import PolyFun.PFunctor.Handler.Stateful

/-!
# Reindexing responders along free handlers

A free handler `f : PFunctor.Handler (FreeM Q) P` implements each query of
`P` as a finite `Q`-program. Running that program against a `Q`-responder gives
a `P`-responder with the same state space. `Responder.reindex` packages this
contravariant action, while `runFreeDisplayed` executes a displayed free tree
against a proof-relevant responder coalgebra.

These are the state-presented PolyFun forms of `run-mealy`, `prog→mealy`,
`run-mealyD`, and `prog→mealyD` in Aberlé's *Compositional Program Verification
with Polynomial Functors in Dependent Type Theory* ([Abe26] in
`REFERENCES.md`). No new Mealy or dependent-machine record is introduced.

Responder execution is defined by structural recursion, so its state and leaf
universes are independent of the interface-direction universe.  This matters
for terminal-coalgebra states such as `M (Q ⊸ X)`, whose universe also contains
the interface-position universe.  The existing `Responder.equivStateHandler`
bridge remains available in the homogeneous fragment where state and response
types share a universe; it is not used to restrict the core execution API.

The same structural boundary keeps the source and target response universes
independent for `reindex`, `runFreeDisplayed`, and `reindexCoalgebra`.
Theorems that explicitly call `FreeM.liftM` or compose handlers retain its
homogeneous source/intermediate response-universe constraint.
-/

@[expose] public section

universe uA uA' uA'' uB uB' uC uD uC' uD' uC'' uD'' uE uF uG uS uV uW

namespace PFunctor
namespace Responder

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
variable {RPoly : PFunctor.{uA'', uB}} {State : Type uS}

/-- Execute a finite free program against a responder, returning its value and
final responder state. -/
def runFree (R : Responder State Q) {E : Type uV}
    (program : FreeM Q E) (state : State) : E × State :=
  match program with
  | .pure value => (value, state)
  | .liftBind query next =>
      runFree (E := E) R (next (R.answer state query)) (R.next state query)

@[simp]
theorem runFree_pure (R : Responder State Q) {E : Type uV}
    (value : E) (state : State) :
    R.runFree (pure value : FreeM Q E) state = (value, state) :=
  rfl

@[simp]
theorem runFree_lift (R : Responder State Q) (query : Q.A) (state : State) :
    R.runFree (FreeM.lift query) state =
      (R.answer state query, R.next state query) :=
  rfl

@[simp]
theorem runFree_liftBind (R : Responder State Q) {E : Type uV}
    (query : Q.A) (next : Q.B query → FreeM Q E) (state : State) :
    R.runFree (FreeM.bind (FreeM.lift query) next) state =
      R.runFree (E := E) (next (R.answer state query)) (R.next state query) :=
  rfl

/-- Executing a free-monad bind first executes the prefix, then continues from
its returned value and responder state. -/
theorem runFree_bind (R : Responder State Q)
    {E : Type uV} {E' : Type uW}
    (program : FreeM Q E) (next : E → FreeM Q E')
    (state : State) :
    R.runFree (program.bind next) state =
      let result := R.runFree program state
      R.runFree (next result.1) result.2 := by
  induction program generalizing state with
  | pure value => rfl
  | lift_bind query rest ih =>
      exact ih (R.answer state query) (R.next state query)

/-! In the homogeneous fragment, structural execution agrees with the existing
Kleisli--Mealy bridge.  The bridge is a comparison theorem, not a universe
restriction on `runFree`. -/

theorem runFree_eq_liftM
    {Q : PFunctor.{uA', uB}} {State : Type uB}
    (R : Responder State Q) {E : Type uB}
    (program : FreeM Q E) (state : State) :
    R.runFree program state = program.liftM R.toStateHandler state := by
  induction program generalizing state with
  | pure value => rfl
  | lift_bind query next ih =>
      exact ih (R.answer state query) (R.next state query)

/-- Structural responder execution is the pure specialization of effectful
stateful-handler execution. -/
theorem runFree_eq_statefulRun
    {Q : PFunctor.{uA', uB}} {State : Type uB}
    (R : Responder State Q) {E : Type uB}
    (program : FreeM Q E) (state : State) :
    R.runFree program state = R.toStateHandler.run program state :=
  R.runFree_eq_liftM program state

/-- Transport dependent result and state evidence along equality of execution
results. This names the equality plumbing used by displayed execution laws. -/
def transportRunEvidence {E : Type uV}
    (F : E → Type uE) (I : State → Type uF)
    {x y : E × State} (h : x = y) :
    F x.1 × I x.2 → F y.1 × I y.2 :=
  h ▸ id

@[simp]
theorem transportRunEvidence_rfl {E : Type uV}
    (F : E → Type uE) (I : State → Type uF)
    (x : E × State) (evidence : F x.1 × I x.2) :
    transportRunEvidence F I (x := x) rfl evidence = evidence :=
  rfl

/-- Transported run evidence is independent of the chosen proof of a fixed
execution equality. -/
theorem transportRunEvidence_proof_irrel {E : Type uV}
    (F : E → Type uE) (I : State → Type uF)
    {x y : E × State} (h h' : x = y)
    (evidence : F x.1 × I x.2) :
    transportRunEvidence F I h evidence =
      transportRunEvidence F I h' evidence := by
  cases h
  rfl

/-- Successive transports of run evidence compose. -/
theorem transportRunEvidence_trans {E : Type uV}
    (F : E → Type uE) (I : State → Type uF)
    {x y z : E × State} (h : x = y) (h' : y = z)
    (evidence : F x.1 × I x.2) :
    transportRunEvidence F I h'
        (transportRunEvidence F I h evidence) =
      transportRunEvidence F I (h.trans h') evidence := by
  cases h
  cases h'
  rfl

/-- Transport of run evidence along an equality is injective. -/
theorem transportRunEvidence_injective {E : Type uV}
    (F : E → Type uE) (I : State → Type uF)
    {x y : E × State} (h : x = y) :
    Function.Injective (transportRunEvidence F I h) := by
  cases h
  exact Function.injective_id

/-- Transported run evidence is heterogeneously equal to the original
evidence.  This is the cast-free elimination rule used when comparing
displayed executions whose ordinary result pairs are propositionally equal. -/
theorem transportRunEvidence_heq {E : Type uV}
    (F : E → Type uE) (I : State → Type uF)
    {x y : E × State} (h : x = y)
    (evidence : F x.1 × I x.2) :
    transportRunEvidence F I h evidence ≍ evidence := by
  cases h
  rfl

/-- Reindex a responder contravariantly along a free handler. -/
def reindex (f : Handler (FreeM Q) P) (R : Responder State Q) :
    Responder State P :=
  mk' (fun state query => (R.runFree (f query) state).1)
    (fun state query => (R.runFree (f query) state).2)

@[simp]
theorem toStateHandler_reindex
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    {State : Type uB}
    (f : Handler (FreeM Q) P)
    (R : Responder State Q) :
    (reindex f R).toStateHandler = fun query state => R.runFree (f query) state :=
  rfl

@[simp]
theorem answer_reindex (f : Handler (FreeM Q) P)
    (R : Responder State Q) (state : State) (query : P.A) :
    (reindex f R).answer state query = (R.runFree (f query) state).1 :=
  rfl

@[simp]
theorem next_reindex (f : Handler (FreeM Q) P)
    (R : Responder State Q) (state : State) (query : P.A) :
    (reindex f R).next state query = (R.runFree (f query) state).2 :=
  rfl

/-- Executing against a reindexed responder is execution after interpreting
the program by the reindexing handler. -/
theorem runFree_reindex (f : Handler (FreeM Q) P)
    (R : Responder State Q) {E : Type uB}
    (program : FreeM P E) (state : State) :
    (reindex f R).runFree program state =
      R.runFree (program.liftM f) state := by
  induction program generalizing state with
  | pure value => rfl
  | lift_bind query next ih =>
      change
        (reindex f R).runFree
            (next (R.runFree (f query) state).1)
            (R.runFree (f query) state).2 =
          R.runFree
            ((f query).bind fun answer => (next answer).liftM f) state
      rw [runFree_bind]
      exact ih (R.runFree (f query) state).1
        (R.runFree (f query) state).2

@[simp]
theorem reindex_id (R : Responder State P) :
    reindex (Handler.id P) R = R := by
  apply Responder.ext
  · intro state query
    rfl
  · intro state query
    rfl

/-- Responder reindexing is contravariantly functorial in categorical
free-handler composition order. -/
theorem reindex_comp
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
    {RPoly : PFunctor.{uA'', uB'}}
    (second : Handler (FreeM RPoly) Q)
    (first : Handler (FreeM Q) P)
    (R : Responder State RPoly) :
    reindex first (reindex second R) = reindex (second.comp first) R := by
  apply Responder.ext
  · intro state query
    exact congrArg Prod.fst (runFree_reindex second R (first query) state)
  · intro state query
    exact congrArg Prod.snd (runFree_reindex second R (first query) state)

section Displayed

/-- Execute a displayed free tree against a proof-relevant responder
coalgebra. The result contains evidence for the returned value and preserved
evidence at the final responder state. -/
def runFreeDisplayed
    (T : Display.{uA', uB', uC', uD'} Q)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    {E : Type uV} {F : E → Type uE}
    {program : FreeM Q E}
    (displayedProgram :
      FreeM.Displayed (T.toDisplayedAlgebra F) program)
    (state : State) (witness : I state) :
    F (R.runFree program state).1 × I (R.runFree program state).2 :=
  match program, displayedProgram with
  | .pure _, displayedValue => ⟨displayedValue.down, witness⟩
  | .liftBind query _, ⟨contract, displayedNext⟩ =>
      let stepEvidence :=
        (Display.responderCoalgebraEquiv T R I) displayedR
          state witness query contract
      runFreeDisplayed T R displayedR
        (displayedNext (R.answer state query) stepEvidence.1)
        (R.next state query) stepEvidence.2

@[simp]
theorem runFreeDisplayed_pure
    (T : Display.{uA', uB', uC', uD'} Q)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    {E : Type uV} {F : E → Type uE}
    (value : E) (displayedValue : ULift.{max uC' uB' uD'} (F value))
    (state : State) (witness : I state) :
    runFreeDisplayed T R displayedR (program := FreeM.pure value)
      displayedValue state witness = ⟨displayedValue.down, witness⟩ :=
  rfl

@[simp]
theorem runFreeDisplayed_liftBind
    (T : Display.{uA', uB', uC', uD'} Q)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    {E : Type uV} {F : E → Type uE}
    (query : Q.A) (next : Q.B query → FreeM Q E)
    (contract : T.position query)
    (displayedNext : (answer : Q.B query) → T.direction query contract answer →
      FreeM.Displayed (T.toDisplayedAlgebra F) (next answer))
    (state : State) (witness : I state) :
    runFreeDisplayed T R displayedR
        (program := FreeM.liftBind query next) ⟨contract, displayedNext⟩
        state witness =
      let stepEvidence :=
        (Display.responderCoalgebraEquiv T R I) displayedR
          state witness query contract
      runFreeDisplayed T R displayedR
        (displayedNext (R.answer state query) stepEvidence.1)
        (R.next state query) stepEvidence.2 :=
  rfl

/-- Displayed execution respects dependent free-monad substitution. After
transport along `runFree_bind`, execution proceeds with the returned value,
result evidence, final state, and preserved state evidence. -/
theorem runFreeDisplayed_bind
    (T : Display.{uA', uB', uC', uD'} Q)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    {E : Type uV} {E' : Type uW}
    {F : E → Type uE} {G : E' → Type uG}
    (program : FreeM Q E)
    (displayedProgram : FreeM.Displayed (T.toDisplayedAlgebra F) program)
    (next : E → FreeM Q E')
    (displayedNext : (value : E) → F value →
      FreeM.Displayed (T.toDisplayedAlgebra G) (next value))
    (state : State) (witness : I state) :
    transportRunEvidence G I (runFree_bind R program next state)
        (runFreeDisplayed T R displayedR
          (T.bind program displayedProgram next displayedNext) state witness) =
      let result := R.runFree program state
      let evidence :=
        runFreeDisplayed T R displayedR displayedProgram state witness
      runFreeDisplayed T R displayedR
        (displayedNext result.1 evidence.1) result.2 evidence.2 := by
  induction program generalizing state with
  | pure value =>
      cases displayedProgram
      rfl
  | lift_bind query rest ih =>
      rcases displayedProgram with ⟨contract, displayedChildren⟩
      simp only [FreeM.pure_bind] at displayedChildren
      let stepEvidence :=
        (Display.responderCoalgebraEquiv T R I) displayedR
          state witness query contract
      change transportRunEvidence G I
          (runFree_bind R (FreeM.liftBind query rest) next state)
          (runFreeDisplayed T R displayedR
            (F := G) (program := (FreeM.liftBind query rest).bind next)
            ⟨contract, fun answer evidence =>
              T.bind (rest answer) (displayedChildren answer evidence)
                next displayedNext⟩ state witness) =
        let result :=
          R.runFree (rest (R.answer state query)) (R.next state query)
        let evidence :=
          runFreeDisplayed T R displayedR
            (displayedChildren (R.answer state query) stepEvidence.1)
            (R.next state query) stepEvidence.2
        runFreeDisplayed T R displayedR
          (displayedNext result.1 evidence.1) result.2 evidence.2
      rw [transportRunEvidence_proof_irrel G I
        (runFree_bind R (FreeM.liftBind query rest) next state)
        (runFree_bind R (rest (R.answer state query)) next
          (R.next state query))]
      exact ih (R.answer state query)
        (displayedChildren (R.answer state query) stepEvidence.1)
        (R.next state query) stepEvidence.2

/-- Reindex a proof-relevant responder coalgebra along a displayed free
handler. This is the state-presented form of Aberlé's `prog→mealyD`. -/
def reindexCoalgebra
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : Handler (FreeM Q) P)
    (df : Display.Handler S T f)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I) :
    Display.Coalgebra (Display.responder S) (reindex f R).out I :=
  (Display.responderCoalgebraEquiv S (reindex f R) I).symm
    fun state witness query contract =>
      runFreeDisplayed T R displayedR (df query contract) state witness

@[simp]
theorem reindexCoalgebra_postcondition
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : Handler (FreeM Q) P)
    (df : Display.Handler S T f)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    (state : State) (witness : I state)
    (query : P.A) (contract : S.position query) :
    ((reindexCoalgebra S T f df R displayedR state witness).1
      query contract) =
        (runFreeDisplayed T R displayedR (df query contract) state witness).1 :=
  rfl

@[simp]
theorem reindexCoalgebra_next
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : Handler (FreeM Q) P)
    (df : Display.Handler S T f)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    (state : State) (witness : I state)
    (query : P.A) (contract : S.position query) :
    ((reindexCoalgebra S T f df R displayedR state witness).2
      ⟨query, PUnit.unit⟩ contract) =
        (runFreeDisplayed T R displayedR (df query contract) state witness).2 :=
  rfl

/-- Displayed execution is compatible with responder reindexing: executing a
displayed source program against the reindexed coalgebra agrees, after the
base execution transport, with first extending it by the displayed handler and
then executing it against the target coalgebra. -/
theorem runFreeDisplayed_reindex
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : Handler (FreeM Q) P)
    (df : Display.Handler S T f)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    {E : Type uB} {F : E → Type uE}
    (program : FreeM P E)
    (displayedProgram : FreeM.Displayed (S.toDisplayedAlgebra F) program)
    (state : State) (witness : I state) :
    transportRunEvidence F I (runFree_reindex f R program state)
        (runFreeDisplayed S (reindex f R)
          (reindexCoalgebra S T f df R displayedR)
          displayedProgram state witness) =
      runFreeDisplayed T R displayedR
        (S.liftM T program displayedProgram f df) state witness := by
  induction program generalizing state with
  | pure value =>
      cases displayedProgram
      rw [transportRunEvidence_proof_irrel F I
        (runFree_reindex f R (FreeM.pure value) state) rfl]
      rfl
  | lift_bind query next ih =>
      rcases displayedProgram with ⟨contract, displayedNext⟩
      simp only [FreeM.pure_bind] at displayedNext
      let result := R.runFree (f query) state
      let stepEvidence :=
        runFreeDisplayed T R displayedR (df query contract) state witness
      let reindexEq :
          (reindex f R).runFree (next result.1) result.2 =
            R.runFree ((FreeM.liftBind query next).liftM f) state :=
        runFree_reindex f R (FreeM.liftBind query next) state
      let bindEq :
          R.runFree ((FreeM.liftBind query next).liftM f) state =
            R.runFree ((next result.1).liftM f) result.2 :=
        runFree_bind R (f query) (fun answer => (next answer).liftM f) state
      change transportRunEvidence F I
          reindexEq
          (runFreeDisplayed S (reindex f R)
            (reindexCoalgebra S T f df R displayedR)
            (displayedNext result.1 stepEvidence.1)
            result.2 stepEvidence.2) =
        runFreeDisplayed T R displayedR
          (T.bind (f query) (df query contract)
            (fun answer => (next answer).liftM f)
            (fun answer evidence =>
              S.liftM T (next answer) (displayedNext answer evidence) f df))
          state witness
      apply transportRunEvidence_injective F I bindEq
      rw [transportRunEvidence_trans]
      rw [transportRunEvidence_proof_irrel F I
        (reindexEq.trans bindEq)
        (runFree_reindex f R (next result.1) result.2)]
      rw [ih result.1 (displayedNext result.1 stepEvidence.1)
        result.2 stepEvidence.2]
      exact (runFreeDisplayed_bind T R displayedR
        (f query) (df query contract)
        (fun answer => (next answer).liftM f)
        (fun answer evidence =>
          S.liftM T (next answer) (displayedNext answer evidence) f df)
        state witness).symm

/-- Reindexing a displayed responder coalgebra by the identity handler
recovers its local obligation definitionally. -/
theorem reindexCoalgebra_id_obligation
    (S : Display.{uA, uB, uC, uD} P)
    (R : Responder State P)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder S) R.out I)
    (state : State) (witness : I state)
    (query : P.A) (contract : S.position query) :
    (Display.responderCoalgebraEquiv S
        (reindex (Handler.id P) R) I
        (reindexCoalgebra S S (Handler.id P) (Display.Handler.id S)
          R displayedR)
        state witness query contract) =
      (Display.responderCoalgebraEquiv S R I displayedR
        state witness query contract) :=
  rfl

/-- Successive displayed coalgebra reindexing agrees pointwise with reindexing
by the displayed Kleisli composite. The transport is exactly the base
execution law `runFree_reindex`. -/
theorem reindexCoalgebra_comp_obligation
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
    {RPoly : PFunctor.{uA'', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Q)
    (U : Display.{uA'', uB', uC'', uD''} RPoly)
    (first : Handler (FreeM Q) P)
    (dfirst : Display.Handler S T first)
    (second : Handler (FreeM RPoly) Q)
    (dsecond : Display.Handler T U second)
    (R : Responder State RPoly)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder U) R.out I)
    (state : State) (witness : I state)
    (query : P.A) (contract : S.position query) :
    transportRunEvidence (S.direction query contract) I
        (runFree_reindex second R (first query) state)
        ((Display.responderCoalgebraEquiv S
          (reindex first (reindex second R)) I)
          (reindexCoalgebra S T first dfirst (reindex second R)
            (reindexCoalgebra T U second dsecond R displayedR))
          state witness query contract) =
      (Display.responderCoalgebraEquiv S
        (reindex (second.comp first) R) I)
        (reindexCoalgebra S U (second.comp first) (dsecond.comp dfirst)
          R displayedR)
        state witness query contract :=
  runFreeDisplayed_reindex T U second dsecond R displayedR
    (first query) (dfirst query contract) state witness

end Displayed

end Responder
end PFunctor
