/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.PatternRunsOnMatter.Display

/-!
Worked examples for base and proof-relevant responder reindexing. Contract
evidence depends on both the supplied precondition and actual answer; invariant
evidence is state-indexed data and affects the next witness.
-/

@[expose] public section

namespace PFunctor.ResponderReindexExample

def Interface : PFunctor where
  A := Unit
  B := fun _ => Bool

def contract : Display Interface where
  position _ := Bool
  direction _ expected answer := if expected = answer then Fin 2 else Fin 3

def directionVal (expected answer : Bool)
    (evidence : contract.direction () expected answer) : Nat := by
  change (if expected = answer then Fin 2 else Fin 3) at evidence
  split at evidence
  · exact evidence.val
  · exact evidence.val

def directionFromNat (expected answer : Bool) (value : Nat) :
    contract.direction () expected answer := by
  simp only [contract]
  split
  · exact ⟨value % 2, Nat.mod_lt _ (by decide)⟩
  · exact ⟨value % 3, Nat.mod_lt _ (by decide)⟩

def target : Responder Bool Interface :=
  Responder.mk' (fun state _ => state) (fun state _ => !state)

def Invariant (state : Bool) := if state then Fin 2 else Fin 3

def invariantVal (state : Bool) (witness : Invariant state) : Nat := by
  simp only [Invariant] at witness
  split at witness
  · exact witness.val
  · exact witness.val

def invariantFromNat (state : Bool) (value : Nat) : Invariant state := by
  simp only [Invariant]
  split
  · exact ⟨value % 2, Nat.mod_lt _ (by decide)⟩
  · exact ⟨value % 3, Nat.mod_lt _ (by decide)⟩

def targetObligation :
    (state : Bool) → Invariant state →
      (query : Unit) → (precondition : Bool) →
        contract.direction query precondition (target.answer state query) ×
          Invariant (target.next state query) :=
  fun state witness query precondition =>
    let post := directionFromNat precondition (target.answer state query)
      (invariantVal state witness)
    ⟨post, invariantFromNat (target.next state query)
      (invariantVal state witness + directionVal precondition
        (target.answer state query) post)⟩

def verifiedTarget :
    Display.Coalgebra (Display.responder contract) target.out Invariant :=
  (Display.responderCoalgebraEquiv contract target Invariant).symm
    targetObligation

/-- Two target calls; both the returned answers and displayed evidence flow
into the source leaf. -/
def twoCalls : Handler (FreeM Interface) Interface :=
  fun _ => .liftBind () fun first =>
    .liftBind () fun second =>
      .pure (Bool.xor first second)

/-- A concrete complete path through the encoded two-call program.  Its two
directions deliberately differ so that the backward component of
`Handler.toFreeLens` cannot silently swap or duplicate answers. -/
def twoCallsPath : FreeM.Path (FreeP.encode (twoCalls ())).1 :=
  ⟨false, ⟨true, ⟨⟩⟩⟩

/-- The forward component of the structural handler/lens equivalence is the
unlabelled program shape. -/
example :
    (Handler.toFreeLens twoCalls).toFunA () =
      (FreeP.encode (twoCalls ())).1 :=
  rfl

/-- The backward component reads the source result at the selected complete
path; here `false xor true` is observable. -/
example :
    (Handler.toFreeLens twoCalls).toFunB () twoCallsPath = true :=
  rfl

/-- Decoding after encoding preserves a nontrivial handler extensionally. -/
example : Handler.ofFreeLens (Handler.toFreeLens twoCalls) = twoCalls :=
  Handler.freeLensEquiv.left_inv twoCalls

/-- Encoding after decoding preserves a nontrivial lens extensionally. -/
example :
    Handler.toFreeLens
        (Handler.ofFreeLens (Handler.toFreeLens twoCalls)) =
      Handler.toFreeLens twoCalls :=
  Handler.freeLensEquiv.right_inv (Handler.toFreeLens twoCalls)

def displayedTwoCalls : Display.Handler contract contract twoCalls :=
  fun _ sourcePrecondition =>
    ⟨sourcePrecondition, fun first firstEvidence =>
      ⟨first, fun second secondEvidence =>
        contract.leaf (contract.direction () sourcePrecondition)
          (Bool.xor first second)
          (directionFromNat sourcePrecondition (Bool.xor first second)
            (directionVal sourcePrecondition first firstEvidence +
              directionVal first second secondEvidence))⟩⟩

/-- A separate nonidentity handler for composition-law canaries. -/
def negateCall : Handler (FreeM Interface) Interface :=
  fun _ => .liftBind () fun answer => .pure (!answer)

def displayedNegateCall : Display.Handler contract contract negateCall :=
  fun _ sourcePrecondition =>
    ⟨sourcePrecondition, fun answer evidence =>
      contract.leaf (contract.direction () sourcePrecondition) (!answer)
        (directionFromNat sourcePrecondition (!answer)
          (directionVal sourcePrecondition answer evidence))⟩

example : target.runFree (twoCalls ()) false = (true, false) :=
  rfl

def source := Responder.reindex twoCalls target

/-- G5's categorical reconstruction reaches the same responder, including
the nontrivial answer and returned state below. -/
example : Responder.reindexViaRunAgainst twoCalls target = source :=
  Responder.reindexViaRunAgainst_eq_reindex twoCalls target

example : Responder.runAgainstResult target (twoCalls ()) false =
    (true, false) := by
  rw [Responder.runAgainstResult_eq_runFree]
  rfl

example : source.answer false () = true :=
  rfl

example : source.next false () = false :=
  rfl

def initialWitness : Invariant false :=
  invariantFromNat false 1

def displayedExecution :=
  Responder.runFreeDisplayed contract target verifiedTarget
    (displayedTwoCalls () false) false initialWitness

def patternDisplayedExecution :=
  Responder.runAgainstDisplayed contract target verifiedTarget
    (displayedTwoCalls () false) false initialWitness

def verifiedSource :=
  Responder.reindexCoalgebra contract contract twoCalls displayedTwoCalls
    target verifiedTarget

def transportedCoalgebraExecution :=
  Responder.transportRunEvidence (contract.direction () false) Invariant
    (Responder.runAgainstResult_eq_runFree
      target (twoCalls ()) false).symm
    ((Display.responderCoalgebraEquiv contract source Invariant)
      verifiedSource false initialWitness () false)

/-- The state-presented verified action is directly the transported
displayed responder-reindexing obligation, with nonconstant postcondition and
state-invariant evidence. -/
example : patternDisplayedExecution = transportedCoalgebraExecution :=
  Responder.runAgainstDisplayed_eq_reindexCoalgebra contract contract
    twoCalls displayedTwoCalls target verifiedTarget false initialWitness
    () false

/-- Both proof-relevant components survive transport through the G5
Pattern-Runs-on-Matter identification. -/
example :
    Responder.transportRunEvidence (contract.direction () false) Invariant
        (Responder.runAgainstResult_eq_runFree
          target (twoCalls ()) false)
        patternDisplayedExecution = displayedExecution :=
  Responder.runAgainstDisplayed_eq_runFreeDisplayed contract target
    verifiedTarget (displayedTwoCalls () false) false initialWitness

example : directionVal false (target.runFree (twoCalls ()) false).1
    displayedExecution.1 = 1 :=
  rfl

example : invariantVal (target.runFree (twoCalls ()) false).2
    displayedExecution.2 = 0 :=
  rfl

example : directionVal false (target.runFree (twoCalls ()) false).1
    (Responder.transportRunEvidence (contract.direction () false) Invariant
      (Responder.runAgainstResult_eq_runFree target (twoCalls ()) false)
      transportedCoalgebraExecution).1 = 1 := by
  rw [← show patternDisplayedExecution = transportedCoalgebraExecution from
    Responder.runAgainstDisplayed_eq_reindexCoalgebra contract contract
      twoCalls displayedTwoCalls target verifiedTarget false initialWitness
      () false]
  unfold patternDisplayedExecution
  rw [Responder.runAgainstDisplayed_eq_runFreeDisplayed]
  rfl

example : invariantVal (target.runFree (twoCalls ()) false).2
    (Responder.transportRunEvidence (contract.direction () false) Invariant
      (Responder.runAgainstResult_eq_runFree target (twoCalls ()) false)
      transportedCoalgebraExecution).2 = 0 := by
  rw [← show patternDisplayedExecution = transportedCoalgebraExecution from
    Responder.runAgainstDisplayed_eq_reindexCoalgebra contract contract
      twoCalls displayedTwoCalls target verifiedTarget false initialWitness
      () false]
  unfold patternDisplayedExecution
  rw [Responder.runAgainstDisplayed_eq_runFreeDisplayed]
  rfl

example : directionVal false (source.answer false ())
    ((Display.responderCoalgebraEquiv contract source Invariant)
      verifiedSource false initialWitness () false).1 = 1 :=
  rfl

example : invariantVal (source.next false ())
    ((Display.responderCoalgebraEquiv contract source Invariant)
      verifiedSource false initialWitness () false).2 = 0 :=
  rfl

example :
    Responder.reindex twoCalls (Responder.reindex negateCall target) =
      Responder.reindex (negateCall.comp twoCalls) target :=
  Responder.reindex_comp negateCall twoCalls target

/-- The free-handler encoding uses the existing substitution fold for
categorical composition. -/
example :
    Handler.toFreeLens (negateCall.comp twoCalls) =
      FreeP.foldLens (FreeP.substMonoid Interface)
          (Handler.toFreeLens negateCall) ∘ₗ
        Handler.toFreeLens twoCalls :=
  Handler.toFreeLens_comp negateCall twoCalls

/-- Proof-relevant displayed composition is associative only after transport
along the ordinary handler law; this canary uses nonconstant evidence. -/
example :
    Display.Handler.transport
        (Handler.comp_assoc twoCalls negateCall twoCalls)
        ((displayedTwoCalls.comp displayedNegateCall).comp
          displayedTwoCalls) =
      displayedTwoCalls.comp
        (displayedNegateCall.comp displayedTwoCalls) :=
  Display.Handler.comp_assoc displayedTwoCalls displayedNegateCall
    displayedTwoCalls

/-! These committed observations make handler-composition order independently
falsifiable.  Starting from `false`, interpreting `twoCalls` through
`negateCall` returns `true`, while interpreting `negateCall` through
`twoCalls` returns `false`; both executions return to state `false`. -/

example : target.runFree ((negateCall.comp twoCalls) ()) false = (true, false) :=
  rfl

example : target.runFree ((twoCalls.comp negateCall) ()) false = (false, false) :=
  rfl

example :
    (Display.responderCoalgebraEquiv contract
      (Responder.reindex (Handler.id Interface) target) Invariant
      (Responder.reindexCoalgebra contract contract (Handler.id Interface)
        (Display.Handler.id contract) target verifiedTarget)
      false initialWitness () false) =
    (Display.responderCoalgebraEquiv contract target Invariant verifiedTarget
      false initialWitness () false) :=
  Responder.reindexCoalgebra_id_obligation contract target verifiedTarget
    false initialWitness () false

/-- The transport-sensitive displayed execution theorem is exercised directly
on a two-node source program and a nonidentity reindexing handler. -/
example :
    Responder.transportRunEvidence (contract.direction () false) Invariant
        (Responder.runFree_reindex negateCall target (twoCalls ()) false)
        (Responder.runFreeDisplayed contract
          (Responder.reindex negateCall target)
          (Responder.reindexCoalgebra contract contract negateCall
            displayedNegateCall target verifiedTarget)
          (displayedTwoCalls () false) false initialWitness) =
      Responder.runFreeDisplayed contract target verifiedTarget
        (contract.liftM contract (twoCalls ()) (displayedTwoCalls () false)
          negateCall displayedNegateCall) false initialWitness :=
  Responder.runFreeDisplayed_reindex contract contract negateCall
    displayedNegateCall target verifiedTarget (twoCalls ())
    (displayedTwoCalls () false) false initialWitness

/-! Observe both proof-relevant components of the transported fusion result,
independently of the fusion theorem.  This catches implementations that erase
or mis-route postcondition or invariant data even if a theorem is changed in
lockstep with the implementation. -/

def displayedFusionLeft :=
  Responder.transportRunEvidence (contract.direction () false) Invariant
      (Responder.runFree_reindex negateCall target (twoCalls ()) false)
      (Responder.runFreeDisplayed contract
        (Responder.reindex negateCall target)
        (Responder.reindexCoalgebra contract contract negateCall
          displayedNegateCall target verifiedTarget)
        (displayedTwoCalls () false) false initialWitness)

def displayedFusionRight :=
  Responder.runFreeDisplayed contract target verifiedTarget
    (contract.liftM contract (twoCalls ()) (displayedTwoCalls () false)
      negateCall displayedNegateCall) false initialWitness

example : directionVal false
    (target.runFree ((twoCalls ()).liftM negateCall) false).1
    displayedFusionLeft.1 = 1 :=
  rfl

example : invariantVal
    (target.runFree ((twoCalls ()).liftM negateCall) false).2
    displayedFusionLeft.2 = 0 :=
  rfl

example : directionVal false
    (target.runFree ((twoCalls ()).liftM negateCall) false).1
    displayedFusionRight.1 = 1 :=
  rfl

example : invariantVal
    (target.runFree ((twoCalls ()).liftM negateCall) false).2
    displayedFusionRight.2 = 0 :=
  rfl

/-- The displayed composition law is exercised with two nonidentity programs
and response-dependent evidence. -/
example :
    Responder.transportRunEvidence (contract.direction () false) Invariant
        (Responder.runFree_reindex negateCall target (twoCalls ()) false)
        ((Display.responderCoalgebraEquiv contract
          (Responder.reindex twoCalls (Responder.reindex negateCall target))
          Invariant)
          (Responder.reindexCoalgebra contract contract twoCalls
            displayedTwoCalls (Responder.reindex negateCall target)
            (Responder.reindexCoalgebra contract contract negateCall
              displayedNegateCall target verifiedTarget))
          false initialWitness () false) =
      (Display.responderCoalgebraEquiv contract
        (Responder.reindex (negateCall.comp twoCalls) target) Invariant)
        (Responder.reindexCoalgebra contract contract
          (negateCall.comp twoCalls)
          (displayedNegateCall.comp displayedTwoCalls) target verifiedTarget)
        false initialWitness () false :=
  Responder.reindexCoalgebra_comp_obligation contract contract contract
    twoCalls displayedTwoCalls negateCall displayedNegateCall target
    verifiedTarget false initialWitness () false

/-! Producer-level canaries preserve all compatible universe separation. -/

universe uA uA' uA'' uA''' uB uB' uC uD uC' uD' uE uF uS uV

section UniverseCanary

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
variable {State : Type uS}

def universeFreeLensEquiv :
    Handler (FreeM Q) P ≃ Lens P (FreeP Q) :=
  Handler.freeLensEquiv

def universeDisplayHandlerTransport
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    {f g : Handler (FreeM Q) P} (h : f = g)
    (df : Display.Handler S T f) : Display.Handler S T g :=
  Display.Handler.transport (S := S) (T := T) h df

example
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    {f : Handler (FreeM Q) P} (df : Display.Handler S T f) :
    Display.Handler.transport (Handler.comp_id f)
        (df.comp (Display.Handler.id S)) = df :=
  Display.Handler.comp_id (S := S) (T := T) df

example
    {Middle : PFunctor.{uA', uB}} {Third : PFunctor.{uA'', uB}}
    {Target : PFunctor.{uA''', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Middle)
    (U : Display.{uA'', uB, uE, uF} Third)
    (W : Display.{uA''', uB', uE, uF} Target)
    {f : Handler (FreeM Middle) P}
    {g : Handler (FreeM Third) Middle}
    {h : Handler (FreeM Target) Third}
    (df : Display.Handler S T f)
    (dg : Display.Handler T U g)
    (dh : Display.Handler U W h) :
    Display.Handler.transport (Handler.comp_assoc h g f)
        ((dh.comp dg).comp df) = dh.comp (dg.comp df) :=
  Display.Handler.comp_assoc (S := S) (T := T) (U := U) (W := W) df dg dh

def universeHandlerCompFinal
    {Middle : PFunctor.{uA', uB}} {Target : PFunctor.{uA'', uB'}}
    (second : Handler (FreeM Target) Middle)
    (first : Handler (FreeM Middle) P) : Handler (FreeM Target) P :=
  second.comp first

/-- `FreeM.liftM_comp` is an arbitrary-lawful-monad theorem, not merely a
composition theorem specialized to a second free monad. -/
theorem universeLiftMCompOption
    {Middle : PFunctor.{uA', uB}} {E : Type uB}
    (program : FreeM P E)
    (first : (a : P.A) → FreeM Middle (P.B a))
    (second : (a : Middle.A) → Option (Middle.B a)) :
    (program.liftM first).liftM second =
      program.liftM (fun a ↦ (first a).liftM second) :=
  FreeM.liftM_comp program first second

def universeRunFree {E : Type uV}
    (R : Responder State Q) (program : FreeM Q E) (state : State) :
    E × State :=
  R.runFree program state

def universeReindex (f : Handler (FreeM Q) P) (R : Responder State Q) :
    Responder State P :=
  Responder.reindex f R

def universeRunFreeDisplayed
    (T : Display.{uA', uB', uC', uD'} Q)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    {E : Type uV} {F : E → Type uE}
    {program : FreeM Q E}
    (displayedProgram : FreeM.Displayed (T.toDisplayedAlgebra F) program)
    (state : State) (witness : I state) :
    F (R.runFree program state).1 × I (R.runFree program state).2 :=
  Responder.runFreeDisplayed T R displayedR displayedProgram state witness

def universeReindexCoalgebra
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB', uC', uD'} Q)
    (f : Handler (FreeM Q) P) (df : Display.Handler S T f)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I) :
    Display.Coalgebra (Display.responder S) (Responder.reindex f R).out I :=
  Responder.reindexCoalgebra S T f df R displayedR

example
    {Middle : PFunctor.{uA', uB}} {Target : PFunctor.{uA'', uB'}}
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Middle)
    (U : Display.{uA'', uB', uC', uD'} Target)
    (first : Handler (FreeM Middle) P)
    (dfirst : Display.Handler S T first)
    (second : Handler (FreeM Target) Middle)
    (dsecond : Display.Handler T U second)
    (R : Responder State Target)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder U) R.out I)
    (state : State) (witness : I state)
    (query : P.A) (contract : S.position query) :=
  Responder.reindexCoalgebra_comp_obligation S T U first dfirst second
    dsecond R displayedR state witness query contract

def universeRunAgainstProgramObj {E : Type uV}
    (R : Responder State Q) (program : FreeM Q E) (state : State) :
    (FreeP X.{uA', uB'}).Obj (E × State) :=
  Responder.runAgainstProgramObj R program state

def universeRunAgainstDisplayed
    (T : Display.{uA', uB', uC', uD'} Q)
    (R : Responder State Q)
    {I : State → Type uF}
    (displayedR : Display.Coalgebra (Display.responder T) R.out I)
    {E : Type uV} {F : E → Type uE}
    {program : FreeM Q E}
    (displayedProgram : FreeM.Displayed (T.toDisplayedAlgebra F) program)
    (state : State) (witness : I state) :=
   Responder.runAgainstDisplayed T R displayedR displayedProgram state witness

end UniverseCanary

end PFunctor.ResponderReindexExample
