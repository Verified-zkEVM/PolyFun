/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Responder.Reindex

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

example : source.answer false () = true :=
  rfl

example : source.next false () = false :=
  rfl

def initialWitness : Invariant false :=
  invariantFromNat false 1

def displayedExecution :=
  Responder.runFreeDisplayed contract target verifiedTarget
    (displayedTwoCalls () false) false initialWitness

example : directionVal false (target.runFree (twoCalls ()) false).1
    displayedExecution.1 = 1 :=
  rfl

example : invariantVal (target.runFree (twoCalls ()) false).2
    displayedExecution.2 = 0 :=
  rfl

def verifiedSource :=
  Responder.reindexCoalgebra contract contract twoCalls displayedTwoCalls
    target verifiedTarget

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

universe uA uA' uA'' uB uB' uC uD uC' uD' uE uF uS uV

section UniverseCanary

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
variable {State : Type uS}

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

end UniverseCanary

end PFunctor.ResponderReindexExample
