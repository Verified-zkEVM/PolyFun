/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.PatternRunsOnMatter.Display

/-!
Canaries for indexed M-types and state-free proof-relevant responder behavior.
Postcondition evidence depends on the actual answer, and continuation evidence
is checked after transport along the ordinary behavior-child equation.
-/

@[expose] public section

namespace PFunctor.ResponderBehaviorExample

def Interface : PFunctor where
  A := Unit
  B := fun _ => Bool

def query : Interface.A := ()

def contract : Display Interface where
  position _ := Bool
  direction _ expected answer := if expected = answer then Fin 2 else Fin 3

def directionFromNat (expected answer : Bool) (value : Nat) :
    contract.direction () expected answer := by
  simp only [contract]
  split
  · exact ⟨value % 2, Nat.mod_lt _ (by decide)⟩
  · exact ⟨value % 3, Nat.mod_lt _ (by decide)⟩

def directionVal (expected answer : Bool)
    (evidence : contract.direction () expected answer) : Nat := by
  change (if expected = answer then Fin 2 else Fin 3) at evidence
  split at evidence
  · exact evidence.val
  · exact evidence.val

def responder : Responder Bool Interface :=
  Responder.mk' (fun state _ => state) (fun state _ => !state)

def Invariant (state : Bool) := if state then Fin 2 else Fin 3

def invariantFromNat (state : Bool) (value : Nat) : Invariant state := by
  simp only [Invariant]
  split
  · exact ⟨value % 2, Nat.mod_lt _ (by decide)⟩
  · exact ⟨value % 3, Nat.mod_lt _ (by decide)⟩

def invariantVal (state : Bool) (witness : Invariant state) : Nat := by
  simp only [Invariant] at witness
  split at witness
  · exact witness.val
  · exact witness.val

def obligation :
    (state : Bool) → Invariant state →
      (query : Unit) → (precondition : Bool) →
        contract.direction query precondition
            (responder.answer state query) ×
          Invariant (responder.next state query) :=
  fun state witness _ precondition =>
    ⟨directionFromNat precondition state (invariantVal state witness),
      invariantFromNat (!state) (invariantVal state witness + 1)⟩

def verified :
    Display.Coalgebra (Display.responder contract) responder.out Invariant :=
  (Display.responderCoalgebraEquiv contract responder Invariant).symm obligation

def initialWitness : Invariant false := invariantFromNat false 1

def behavior := responder.behavior false

def verifiedBehavior :=
  Responder.verifiedBehavior contract responder Invariant verified
    false initialWitness

example : behavior.head.toFunB query PUnit.unit = false := by
  change responder.answer false query = false
  rfl

example : directionVal false false
    (Responder.respondDisplayed contract verifiedBehavior query false).1 = 1 := by
  change directionVal false false
    (Responder.respondDisplayed contract
      (Responder.verifiedBehavior contract responder Invariant verified
        false initialWitness) query false).1 = 1
  rw [Responder.respondDisplayed_verifiedBehavior_post]
  rfl

/-! Changing only the supplied precondition selects the `Fin 3` branch.  This
would not typecheck if state-free behavior erased answer-dependent evidence. -/
example : directionVal true false
    (Responder.respondDisplayed contract verifiedBehavior query true).1 = 1 := by
  change directionVal true false
    (Responder.respondDisplayed contract
      (Responder.verifiedBehavior contract responder Invariant verified
        false initialWitness) query true).1 = 1
  rw [Responder.respondDisplayed_verifiedBehavior_post]
  rfl

example :
    Display.M.transport (Responder.behavior_child responder false ())
        (Responder.respondDisplayed contract verifiedBehavior query false).2 =
      Responder.verifiedBehavior contract responder Invariant verified
        (responder.next false query)
        ((Display.responderCoalgebraEquiv contract responder Invariant)
          verified false initialWitness query false).2 := by
  change Display.M.transport
      (Responder.behavior_child responder false query)
      (Responder.respondDisplayed contract
        (Responder.verifiedBehavior contract responder Invariant verified
          false initialWitness) query false).2 = _
  exact
    Responder.respondDisplayed_verifiedBehavior_next contract responder Invariant verified
      false initialWitness query false

def oneCall : Handler (FreeM Interface) Interface :=
  fun _ => FreeM.lift query

def twoCalls : Handler (FreeM Interface) Interface :=
  fun _ => .liftBind query fun _ => FreeM.lift query

def displayedOneCall : Display.Handler contract contract oneCall :=
  fun _ precondition =>
    ⟨precondition, fun answer evidence =>
      contract.leaf (contract.direction query precondition) answer evidence⟩

def reindexedVerifiedBehavior :=
  Responder.reindexVerifiedBehavior contract contract oneCall displayedOneCall
    behavior verifiedBehavior

example : Responder.reindexBehavior oneCall behavior =
    (Responder.reindexViaRunAgainst oneCall
      (Responder.terminal (P := Interface))).behavior behavior :=
  Responder.reindexBehavior_eq_runAgainst oneCall behavior

def directDisplayedStep :=
  Responder.runFreeDisplayed contract (Responder.terminal (P := Interface))
    (Display.Coalgebra.terminal (Display.responder contract))
    (displayedOneCall query false) behavior verifiedBehavior

def runAgainstDisplayedStep :=
  Responder.transportRunEvidence (contract.direction query false)
    (Display.M (Display.responder contract))
    (Responder.runAgainstResult_eq_runFree
      (Responder.terminal (P := Interface)) (oneCall query) behavior)
    (Responder.runAgainstDisplayed contract
      (Responder.terminal (P := Interface))
      (Display.Coalgebra.terminal (Display.responder contract))
      (displayedOneCall query false) behavior verifiedBehavior)

/-! The direct displayed execution and the coinductive reindexed `respondDisplayed` side
are observed separately, so changing the semantic equation and implementation
in lockstep does not preserve both canaries. -/

example : directionVal false false directDisplayedStep.1 = 1 := by
  change directionVal false false
    (Responder.respondDisplayed contract
      (Responder.verifiedBehavior contract responder Invariant verified
        false initialWitness) query false).1 = 1
  rw [Responder.respondDisplayed_verifiedBehavior_post]
  rfl

example : directionVal false false
    (Responder.respondDisplayed contract reindexedVerifiedBehavior query false).1 = 1 := by
  change directionVal false false
    (Responder.respondDisplayed contract
      (Responder.reindexVerifiedBehavior contract contract oneCall
        displayedOneCall behavior verifiedBehavior) query false).1 = 1
  rw [Responder.respondDisplayed_reindexVerifiedBehavior_post]
  exact show directionVal false false directDisplayedStep.1 = 1 from by
    change directionVal false false
      (Responder.respondDisplayed contract
        (Responder.verifiedBehavior contract responder Invariant verified
          false initialWitness) query false).1 = 1
    rw [Responder.respondDisplayed_verifiedBehavior_post]
    rfl

/-- The state-free proof-relevant postcondition is supplied by evaluated
Pattern Runs on Matter, not merely by the raw Xi synchronization tree. -/
example :
    (Responder.respondDisplayed contract reindexedVerifiedBehavior query false).1 =
      (Responder.transportRunEvidence (contract.direction query false)
        (Display.M (Display.responder contract))
        (Responder.runAgainstResult_eq_runFree
          (Responder.terminal (P := Interface)) (oneCall query) behavior)
        (Responder.runAgainstDisplayed contract
          (Responder.terminal (P := Interface))
          (Display.Coalgebra.terminal (Display.responder contract))
          (displayedOneCall query false) behavior verifiedBehavior)).1 :=
  Responder.respondDisplayed_reindexVerifiedBehavior_post_runAgainst contract contract
    oneCall displayedOneCall behavior verifiedBehavior query false

example :
    Display.M.transport
        (Responder.behavior_child
          (Responder.reindex oneCall
            (Responder.terminal (P := Interface))) behavior query)
        (Responder.respondDisplayed contract reindexedVerifiedBehavior query false).2 =
      Responder.reindexVerifiedBehavior contract contract oneCall
        displayedOneCall
        ((Responder.terminal (P := Interface)).runFree
          (oneCall query) behavior).2 directDisplayedStep.2 := by
  exact Responder.respondDisplayed_reindexVerifiedBehavior_next contract contract
    oneCall displayedOneCall behavior verifiedBehavior query false

/-- The evaluated Pattern-Runs-on-Matter continuation bridge is exercised
directly, rather than only through its `runFreeDisplayed` predecessor. -/
example :
    Display.M.transport
        (Responder.behavior_child
          (Responder.reindex oneCall
            (Responder.terminal (P := Interface))) behavior query)
        (Responder.respondDisplayed contract reindexedVerifiedBehavior query false).2 =
      Responder.reindexVerifiedBehavior contract contract oneCall
        displayedOneCall
        ((Responder.terminal (P := Interface)).runFree
          (oneCall query) behavior).2 runAgainstDisplayedStep.2 := by
  exact
    Responder.respondDisplayed_reindexVerifiedBehavior_next_runAgainst contract contract
      oneCall displayedOneCall behavior verifiedBehavior query false

def firstRunAgainstContinuation :
    Display.M (Display.responder contract)
      (Responder.reindexBehavior oneCall
        ((Responder.terminal (P := Interface)).runFree
          (oneCall query) behavior).2) :=
  Responder.reindexVerifiedBehavior contract contract oneCall displayedOneCall
    ((Responder.terminal (P := Interface)).runFree
      (oneCall query) behavior).2 runAgainstDisplayedStep.2

/-- After the evaluated-action bridge, the successor continuation still
exposes the answer-dependent evidence of its next state. -/
example : directionVal true true
    (Responder.respondDisplayed contract firstRunAgainstContinuation query true).1 = 0 := by
  have hstep : runAgainstDisplayedStep = directDisplayedStep :=
    Responder.runAgainstDisplayed_eq_runFreeDisplayed contract
      (Responder.terminal (P := Interface))
      (Display.Coalgebra.terminal (Display.responder contract))
      (displayedOneCall query false) behavior verifiedBehavior
  change directionVal true true
    (Responder.respondDisplayed contract
      (Responder.reindexVerifiedBehavior contract contract oneCall
        displayedOneCall
        ((Responder.terminal (P := Interface)).runFree
          (oneCall query) behavior).2 runAgainstDisplayedStep.2)
      query true).1 = 0
  rw [hstep]
  rfl

def firstReindexedContinuation :
    Display.M (Display.responder contract)
      (Responder.reindexBehavior oneCall
        ((Responder.terminal (P := Interface)).runFree
          (oneCall query) behavior).2) :=
  Display.M.transport
    (Responder.behavior_child
      (Responder.reindex oneCall (Responder.terminal (P := Interface)))
      behavior query)
    (Responder.respondDisplayed contract reindexedVerifiedBehavior query false).2

/-! The continuation produced by verified reindexing is itself executed for a
second step. This catches a reindexer that returns a stale or copied original
continuation even when its one-step equation is changed in lockstep. -/
example : directionVal true true
    (Responder.respondDisplayed contract firstReindexedContinuation query true).1 = 0 := by
  change directionVal true true
    (Responder.respondDisplayed contract
      (Display.M.transport
        (Responder.behavior_child
          (Responder.reindex oneCall
            (Responder.terminal (P := Interface))) behavior query)
        (Responder.respondDisplayed contract
          (Responder.reindexVerifiedBehavior contract contract oneCall
            displayedOneCall behavior verifiedBehavior) query false).2)
      query true).1 = 0
  rw [Responder.respondDisplayed_reindexVerifiedBehavior_next]
  rfl

def firstVerifiedContinuation :
    Display.M (Display.responder contract) (responder.behavior true) :=
  Display.M.transport (Responder.behavior_child responder false query)
    (Responder.respondDisplayed contract verifiedBehavior query false).2

/-! This unfolds the continuation returned by the first `respondDisplayed` call and then
observes its next answer-dependent postcondition. It is independent of the
one-step continuation equality above. -/
example : directionVal true true
    (Responder.respondDisplayed contract firstVerifiedContinuation query true).1 = 0 := by
  change directionVal true true
    (Responder.respondDisplayed contract
      (Display.M.transport (Responder.behavior_child responder false query)
        (Responder.respondDisplayed contract
          (Responder.verifiedBehavior contract responder Invariant verified
            false initialWitness) query false).2) query true).1 = 0
  rw [Responder.respondDisplayed_verifiedBehavior_next]
  rw [Responder.respondDisplayed_verifiedBehavior_post]
  rfl

/-! Re-coinducing a verified behavior from its own destructor gives a second
presentation of the same displayed tree.  The following two canaries exercise
the generic displayed and responder-observation bisimulation interfaces
directly; their child obligations reject a copied or stale continuation. -/

def recoinducedVerifiedBehavior :
    Display.M (Display.responder contract) behavior :=
  Display.M.corec (Display.M (Display.responder contract))
    (fun _ displayed => Display.M.dest displayed) behavior verifiedBehavior

/-- Direct producer canary for `Display.M.bisim`, using the original displayed
tree and the distinct corecursive presentation generated by its destructor. -/
example : verifiedBehavior = recoinducedVerifiedBehavior := by
  let step := fun
      (current : PFunctor.M (Interface ⊸ X))
      (displayed : Display.M (Display.responder contract) current) =>
    Display.M.dest displayed
  let Rel := fun
      (current : PFunctor.M (Interface ⊸ X))
      (left right : Display.M (Display.responder contract) current) =>
    ∃ displayed,
      left = displayed ∧
        right = Display.M.corec
          (Display.M (Display.responder contract)) step current displayed
  apply Display.M.bisim Rel
  · intro current left right related
    rcases related with ⟨source, leftEq, rightEq⟩
    subst left
    subst right
    refine ⟨source.head, source.child,
      (fun direction precondition =>
        Display.M.corec (Display.M (Display.responder contract)) step _
          (source.child direction precondition)), rfl, ?_, ?_⟩
    · rw [Display.M.dest_corec]
      rfl
    · intro direction precondition
      exact ⟨source.child direction precondition, rfl, rfl⟩
  · exact ⟨verifiedBehavior, rfl, rfl⟩

/-- Direct producer canary for the responder-shaped bisimulation.  Equality of
the answer-dependent evidence and recursive selection of the matching child
are both exposed through `respondDisplayed`. -/
example : verifiedBehavior = recoinducedVerifiedBehavior := by
  let step := fun
      (current : PFunctor.M (Interface ⊸ X))
      (displayed : Display.M (Display.responder contract) current) =>
    Display.M.dest displayed
  let Rel := fun
      (current : PFunctor.M (Interface ⊸ X))
      (left right : Display.M (Display.responder contract) current) =>
    ∃ displayed,
      left = displayed ∧
        right = Display.M.corec
          (Display.M (Display.responder contract)) step current displayed
  apply Responder.respondDisplayed_bisim contract Rel
  · intro current left right related currentQuery precondition
    rcases related with ⟨source, leftEq, rightEq⟩
    subst left
    subst right
    have hDest := Display.M.dest_corec
      (Display.M (Display.responder contract)) step current source
    constructor
    · rw [Responder.respondDisplayed_post, Responder.respondDisplayed_post]
      have hHead := congrArg Sigma.fst hDest
      change
        (Display.M.corec (Display.M (Display.responder contract)) step
          current source).head = source.head at hHead
      exact congrFun (congrFun hHead.symm currentQuery) precondition
    · refine ⟨
        (Responder.respondDisplayed contract source currentQuery precondition).2,
        rfl, ?_⟩
      rw [Responder.respondDisplayed_next, Responder.respondDisplayed_next]
      exact congrArg
        (fun node => node.2 ⟨currentQuery, PUnit.unit⟩ precondition) hDest
  · exact ⟨verifiedBehavior, rfl, rfl⟩

example :
    Responder.reindexBehavior oneCall (responder.behavior false) =
      (Responder.reindex oneCall responder).behavior false :=
  Responder.reindexBehavior_behavior oneCall responder false

example :
    Responder.reindexBehavior oneCall
        (Responder.reindexBehavior oneCall behavior) =
      Responder.reindexBehavior (oneCall.comp oneCall) behavior :=
  Responder.reindexBehavior_comp oneCall oneCall behavior

example : Responder.reindexBehavior (Handler.id Interface) behavior = behavior :=
  Responder.reindexBehavior_id behavior

example :
    Display.M.transport (Responder.reindexBehavior_id behavior)
        (Responder.reindexVerifiedBehavior contract contract
          (Handler.id Interface) (Display.Handler.id contract)
          behavior verifiedBehavior) = verifiedBehavior :=
  Responder.reindexVerifiedBehavior_id contract behavior verifiedBehavior

example :
    Display.M.transport
        (Responder.reindexBehavior_comp oneCall oneCall behavior)
        (Responder.reindexVerifiedBehavior contract contract oneCall
          displayedOneCall (Responder.reindexBehavior oneCall behavior)
          reindexedVerifiedBehavior) =
      Responder.reindexVerifiedBehavior contract contract
        (oneCall.comp oneCall) (displayedOneCall.comp displayedOneCall)
        behavior verifiedBehavior :=
  Responder.reindexVerifiedBehavior_comp contract contract contract
    oneCall displayedOneCall oneCall displayedOneCall behavior verifiedBehavior

example :
    (Display.M.destEquiv (S := Display.responder contract)
      (tree := behavior)).symm
        (Display.M.dest verifiedBehavior) = verifiedBehavior :=
  Display.M.mk_dest verifiedBehavior

example :
    (Display.M.transportEquiv (S := Display.responder contract)
      (show behavior = behavior from rfl)).symm
        (Display.M.transportEquiv (S := Display.responder contract)
          (show behavior = behavior from rfl) verifiedBehavior) =
      verifiedBehavior :=
  (Display.M.transportEquiv (S := Display.responder contract)
    (show behavior = behavior from rfl)).left_inv verifiedBehavior

/-! Branch count is independently observable: one query returns the initial
answer, while the explicit two-query handler returns the answer after one
state transition. -/
example :
    (Responder.reindexBehavior oneCall behavior).head.toFunB query PUnit.unit =
      false := by
  change
    (Responder.reindexBehavior oneCall (responder.behavior false)).head.toFunB
      query PUnit.unit = false
  rw [Responder.reindexBehavior_behavior oneCall responder false]
  change (Responder.reindex oneCall responder).answer false query = false
  rfl

/-! A concrete indexed M-type alternates two distinguishable source indices.
The first child is forced into the `true` fiber and its child into `false`. -/

def IndexedToggle : IPFunctor.Endo Bool where
  A _ := Bool
  B _ _ := Unit
  src _ target _ := target

def indexedToggleStep (index : Bool) (nextIndex : Bool) :
    IndexedToggle.Obj (fun _ => Bool) index :=
  ⟨nextIndex, fun _ => !nextIndex⟩

def indexedToggleTree : IPFunctor.IM IndexedToggle false :=
  IPFunctor.IM.corec indexedToggleStep false true

def indexedToggleStepWrapped (index : Bool) (state : Bool × Unit) :
    IndexedToggle.Obj (fun _ => Bool × Unit) index :=
  ⟨state.1, fun _ => (!state.1, ())⟩

def indexedToggleTreeWrapped : IPFunctor.IM IndexedToggle false :=
  IPFunctor.IM.corec indexedToggleStepWrapped false (true, ())

def indexedToggleChild : IPFunctor.IM IndexedToggle true :=
  (IPFunctor.IM.dest indexedToggleTree).2 ()

def indexedToggleGrandchild : IPFunctor.IM IndexedToggle false :=
  (IPFunctor.IM.dest indexedToggleChild).2 ()

example : (IPFunctor.IM.dest indexedToggleTree).1 = true := by
  change
    (IPFunctor.IM.dest
      (IPFunctor.IM.corec indexedToggleStep false true)).1 = true
  rw [IPFunctor.IM.dest_corec]
  rfl

example : (IPFunctor.IM.dest indexedToggleChild).1 = false := by
  change
    (IPFunctor.IM.dest
      ((IPFunctor.IM.dest
        (IPFunctor.IM.corec indexedToggleStep false true)).2 ())).1 = false
  rw [IPFunctor.IM.dest_corec]
  change
    (IPFunctor.IM.dest
      (IPFunctor.IM.corec indexedToggleStep true false)).1 = false
  rw [IPFunctor.IM.dest_corec]
  rfl

example :
    (IPFunctor.IM.destEquiv (P := IndexedToggle) (i := false)).symm
        (IPFunctor.IM.dest indexedToggleTree) = indexedToggleTree :=
  IPFunctor.IM.mk_dest indexedToggleTree

example :
    IPFunctor.IM.dest
        ((IPFunctor.IM.destEquiv (P := IndexedToggle) (i := false)).symm
          (IPFunctor.IM.dest indexedToggleTree)) =
      IPFunctor.IM.dest indexedToggleTree := by
  exact (IPFunctor.IM.destEquiv (P := IndexedToggle) (i := false)).apply_symm_apply _

/-! The two presentations have different seed-state types and step functions;
their equality is obtained only by matching the indexed branch transition at
every unfolding. -/
example : indexedToggleTree = indexedToggleTreeWrapped := by
  apply IPFunctor.IM.bisim
    (R := fun index left right =>
      ∃ next,
        left = IPFunctor.IM.corec indexedToggleStep index next ∧
        right = IPFunctor.IM.corec indexedToggleStepWrapped index (next, ()))
  · intro index left right h
    rcases h with ⟨next, rfl, rfl⟩
    refine
      ⟨next,
        (fun _ => IPFunctor.IM.corec indexedToggleStep _ (!next)),
        (fun _ => IPFunctor.IM.corec indexedToggleStepWrapped _ (!next, ())),
        ?_, ?_, ?_⟩
    · rw [IPFunctor.IM.dest_corec]
      rfl
    · rw [IPFunctor.IM.dest_corec]
      rfl
    · intro direction
      exact ⟨!next, rfl, rfl⟩
  · exact ⟨true, rfl, rfl⟩

example :
    (Responder.reindexBehavior twoCalls behavior).head.toFunB
        query PUnit.unit = true := by
  change
    (Responder.reindexBehavior twoCalls
      (responder.behavior false)).head.toFunB query PUnit.unit = true
  rw [Responder.reindexBehavior_behavior
    twoCalls responder false]
  change
    (Responder.reindex twoCalls responder).answer false query = true
  rfl

/-! Universe producer canaries: base positions/directions, display
positions/directions, indexed states, and coalgebra witnesses remain
independent. -/

section Universes

universe uI uA uA' uA'' uB uB' uB'' uC uD uC' uD' uC'' uD'' uX uS uF

def indexedMProducer
    {I : Type uI} (P : IPFunctor.Endo I)
    (X : I → Type uX)
    (step : (i : I) → X i → P.Obj X i)
    (i : I) (state : X i) : IPFunctor.IM P i :=
  IPFunctor.IM.corec step i state

def displayedMProducer
    {P : PFunctor.{uA, uB}}
    (S : Display.{uA, uB, uC, uD} P)
    (X : PFunctor.M P → Type uX)
    (step : (tree : PFunctor.M P) → X tree →
      S.Obj X (PFunctor.M.dest tree))
    (tree : PFunctor.M P) (state : X tree) : Display.M S tree :=
  Display.M.corec X step tree state

def verifiedBehaviorProducer
    {P : PFunctor.{uA, uB}}
    (S : Display.{uA, uB, uC, uD} P)
    {State : Type uS} (R : Responder State P)
    (I : State → Type uF)
    (displayedR : Display.Coalgebra (Display.responder S) R.out I)
    (state : State) (witness : I state) :
    Display.M (Display.responder S) (R.behavior state) :=
  Responder.verifiedBehavior S R I displayedR state witness

def reindexBehaviorProducer
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    (f : Handler (FreeM Q) P)
    (behavior : PFunctor.M (Q ⊸ X.{uA', uB'})) :
    PFunctor.M (P ⊸ X.{uA, uB}) :=
  Responder.reindexBehavior f behavior

def reindexVerifiedBehaviorProducer
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : Handler (FreeM Q) P) (df : Display.Handler S T f)
    (behavior : PFunctor.M (Q ⊸ X.{uA', uB'}))
    (displayedBehavior : Display.M (Display.responder T) behavior) :
    Display.M (Display.responder S) (Responder.reindexBehavior f behavior) :=
  Responder.reindexVerifiedBehavior S T f df behavior displayedBehavior

/-- The final target response universe remains independent in ordinary
state-free reindexing composition. -/
theorem reindexBehaviorCompProducer
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
    {R : PFunctor.{uA'', uB''}}
    (second : Handler (FreeM R) Q) (first : Handler (FreeM Q) P)
    (behavior : PFunctor.M (R ⊸ X.{uA'', uB''})) :
    Responder.reindexBehavior first
        (Responder.reindexBehavior second behavior) =
      Responder.reindexBehavior (second.comp first) behavior :=
  Responder.reindexBehavior_comp second first behavior

/-- The verified composition law has the same independent final-target
response universe as its base-handler and coalgebra composition laws. -/
theorem reindexVerifiedBehaviorCompProducer
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
    {R : PFunctor.{uA'', uB''}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Q)
    (U : Display.{uA'', uB'', uC'', uD''} R)
    (second : Handler (FreeM R) Q) (dsecond : Display.Handler T U second)
    (first : Handler (FreeM Q) P) (dfirst : Display.Handler S T first)
    (behavior : PFunctor.M (R ⊸ X.{uA'', uB''}))
    (displayedBehavior : Display.M (Display.responder U) behavior) :
    Display.M.transport
        (Responder.reindexBehavior_comp second first behavior)
        (Responder.reindexVerifiedBehavior S T first dfirst
          (Responder.reindexBehavior second behavior)
          (Responder.reindexVerifiedBehavior T U second dsecond
            behavior displayedBehavior)) =
      Responder.reindexVerifiedBehavior S U (second.comp first)
        (dsecond.comp dfirst) behavior displayedBehavior :=
  Responder.reindexVerifiedBehavior_comp S T U second dsecond first dfirst
    behavior displayedBehavior

end Universes

end PFunctor.ResponderBehaviorExample
