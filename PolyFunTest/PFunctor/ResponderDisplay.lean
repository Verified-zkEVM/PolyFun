/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module


public import PolyFun.PFunctor.Dynamical.Responder.Display

/-!
Worked examples for proof-relevant responder contracts. The response type,
contract position, contract evidence, and state witness are all genuinely
dependent data rather than propositions.
-/

@[expose] public section

namespace PFunctor.Display.ResponderExample

inductive Query where
  | bit
  | choice

def Response : Query → Type
  | .bit => Bool
  | .choice => Fin 3

def Interface : PFunctor where
  A := Query
  B := Response

/-- Contract positions depend on the query, and postcondition evidence depends
on both the chosen contract position and the actual response. -/
def contract : Display Interface where
  position
    | .bit => Bool
    | .choice => Fin 2
  direction
    | .bit, expected, answer => if expected = answer then Fin 2 else PUnit
    | .choice, bound, answer => Fin (bound.val + answer.val + 1)

def answer (state : Nat) : (a : Query) → Response a
  | .bit => state % 2 == 0
  | .choice => ⟨state % 3, Nat.mod_lt _ (by decide)⟩

def next (state : Nat) : Query → Nat
  | .bit => state + 1
  | .choice => state + 2

def system : Responder Nat Interface :=
  Responder.mk' answer next

/-- A proof-relevant, state-indexed invariant family. -/
def Invariant (state : Nat) := Fin (state + 1)

def answerContract (state : Nat) :
    (a : Query) → (c : contract.position a) →
      contract.direction a c (system.answer state a)
  | .bit, expected => by
      simp only [contract]
      split
      · exact 0
      · exact PUnit.unit
  | .choice, bound => ⟨0, by simp⟩

/-- The local dependent-Mealy obligation: for every query and supplied
pre-witness, certify the committed answer and preserve the state witness. -/
def localStep (state : Nat) (witness : Invariant state) :
    (a : Query) → (c : contract.position a) →
      contract.direction a c (system.answer state a) ×
        Invariant (system.next state a) :=
  fun a c => ⟨answerContract state a c, match a with
    | .bit => ⟨witness.val, by simp [system, next]; omega⟩
    | .choice => ⟨witness.val, by simp [system, next]; omega⟩⟩

/-- The same local obligation, transported through the canonical equivalence,
is a generic displayed coalgebra over the existing responder's `out` map. -/
def displayed :
    Coalgebra (responder contract) system.out Invariant :=
  (responderCoalgebraEquiv contract system Invariant).symm localStep

example (state : Nat) (witness : Invariant state) :
    (responderCoalgebraEquiv contract system Invariant displayed) state witness =
      localStep state witness := by
  simp [displayed]

example (state : Nat) (witness : Invariant state) :
    (((responderCoalgebraEquiv contract system Invariant displayed) state witness
      Query.choice ⟨0, by decide⟩).2).val = witness.val := by
  rfl

example :
    answerContract 0 .bit true = (0 : Fin 2) :=
  rfl

example (state : Nat) :
    (answerContract state .choice ⟨0, by decide⟩).val = 0 :=
  rfl

example
    (answerSection : (Interface ⊸ X).A)
    (evidence : (responder contract).position answerSection)
    (query : (Interface ⊸ X).B answerSection)
    (precondition : contract.position query.1) :
    (responderChart contract).toFunB ⟨answerSection, evidence⟩
      ⟨query, precondition⟩ = query :=
  rfl

end PFunctor.Display.ResponderExample

namespace PFunctor.Display.ResponderRegression

/-- A one-query interface used to expose the variance of responder displays. -/
def Unary : PFunctor where
  A := PUnit
  B := fun _ => PUnit

/-- Empty preconditions make the paper obligation vacuously inhabited. This
regression would fail if responder positions incorrectly chose a pre-witness
with `Sigma` instead of accepting it with `∀`. -/
def emptyPrecondition : Display Unary where
  position _ := PEmpty
  direction _ c := PEmpty.elim c

example (answerSection : (Unary ⊸ X).A) :
    (responder emptyPrecondition).position answerSection :=
  fun _ c => PEmpty.elim c

/-- The recursively displayed continuation may depend on the supplied
pre-witness, even though its base next state does not. -/
def booleanPrecondition : Display Unary where
  position _ := Bool
  direction _ _ _ := PUnit

def booleanSystem : Responder PUnit Unary :=
  Responder.mk' (fun _ _ => PUnit.unit) (fun _ _ => PUnit.unit)

def booleanObligation :
    (state : PUnit) → Bool →
      (a : PUnit) → (precondition : Bool) → PUnit × Bool :=
  fun _ _ _ precondition => ⟨PUnit.unit, precondition⟩

def booleanDisplayed :
    Coalgebra (responder booleanPrecondition) booleanSystem.out (fun _ => Bool) :=
  (responderCoalgebraEquiv booleanPrecondition booleanSystem (fun _ => Bool)).symm
    booleanObligation

example (witness : Bool) :
    (booleanDisplayed PUnit.unit witness).2 ⟨PUnit.unit, PUnit.unit⟩ false = false :=
  rfl

example (witness : Bool) :
    (booleanDisplayed PUnit.unit witness).2 ⟨PUnit.unit, PUnit.unit⟩ true = true :=
  rfl

universe uA uB uC uD uE uF

/-- A universe canary keeping all six relevant levels independent. -/
def LargeInterface : PFunctor.{uA, uB} where
  A := ULift.{uA, 0} PUnit
  B := fun _ => ULift.{uB, 0} PUnit

def largeContract : Display.{uA, uB, uC, uD} LargeInterface where
  position _ := ULift.{uC, 0} PUnit
  direction _ _ _ := ULift.{uD, 0} PUnit

def LargeState := ULift.{uE, 0} PUnit

def largeSystem : Responder LargeState LargeInterface :=
  Responder.mk' (fun _ _ => ULift.up.{uB, 0} PUnit.unit) (fun state _ => state)

def LargeWitness (_ : LargeState) := ULift.{uF, 0} PUnit

def largeObligation :
    (state : LargeState) → LargeWitness state →
      (a : LargeInterface.A) → (c : largeContract.position a) →
        largeContract.direction a c (largeSystem.answer state a) ×
          LargeWitness (largeSystem.next state a) :=
  fun _ witness _ _ => ⟨ULift.up.{uD, 0} PUnit.unit, witness⟩

def largeEquiv :
    Coalgebra (responder largeContract) largeSystem.out LargeWitness ≃
      ((state : LargeState) → LargeWitness state →
        (a : LargeInterface.A) → (c : largeContract.position a) →
          largeContract.direction a c (largeSystem.answer state a) ×
            LargeWitness (largeSystem.next state a)) :=
  responderCoalgebraEquiv largeContract largeSystem LargeWitness

end PFunctor.Display.ResponderRegression
