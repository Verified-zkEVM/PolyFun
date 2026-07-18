/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module


public import PolyFun.PFunctor.Display.Chart
public import PolyFun.PFunctor.Display.Coalgebra
public import PolyFun.PFunctor.Dynamical.Responder

/-!
# Proof-relevant contracts for responders

For a display `S` over an interface `P`, `Display.responder S` is the induced
display over the responder interface `P ⊸ X`. A base position of `P ⊸ X` is an
answer-section for `P`; a displayed position maps every query and admissible
pre-witness to answer-dependent post-evidence. Its displayed direction is that
pre-witness, so a displayed responder coalgebra must preserve its witness for
every query/pre-witness pair.

This is the intrinsic PolyFun form of the paper's dependent Mealy contract. It
uses the existing `Responder` / `DynSystem` state presentation and the generic
`Display.Coalgebra`; it does not introduce another verified-machine record.

This notion is not `DynSystem.SafetyRefinement`. A displayed responder
coalgebra preserves proof-relevant data over one system's states and answers;
a safety refinement is a proposition-valued relational policy connecting two
systems, together with initial-state and assumption/safety obligations.

The ordinary chart `responderChart` forgets contract witnesses. It is not a
lens in general: lifting a bare query contravariantly would require inventing
an element of `S.position a`, which may even be empty.
-/

@[expose] public section

universe uA uB uC uD uE uF

namespace PFunctor
namespace Display

variable {P : PFunctor.{uA, uB}}

/-- The responder display induced by a display over the query interface.

Above an answer-section `answer : (P ⊸ X).A`, a displayed position sends every
query and precondition witness to answer-dependent postcondition evidence.
The displayed direction remembers the supplied precondition witness, because
the recursively verified continuation may depend on it. -/
def responder (S : Display.{uA, uB, uC, uD} P) :
    Display.{max uA uB, max uA uB, max uA uC uD, uC}
      (P ⊸ X.{uA, uB}) where
  position answer :=
    (a : P.A) → (c : S.position a) →
      S.direction a c (answer.toFunB a PUnit.unit)
  direction _answer _contract query := S.position query.1

@[simp]
theorem responder_position (S : Display.{uA, uB, uC, uD} P)
    (answer : (P ⊸ X.{uA, uB}).A) :
    (responder S).position answer =
      ((a : P.A) → (c : S.position a) →
        S.direction a c (answer.toFunB a PUnit.unit)) :=
  rfl

@[simp]
theorem responder_direction (S : Display.{uA, uB, uC, uD} P)
    (answer : (P ⊸ X.{uA, uB}).A)
    (contract : (responder S).position answer)
    (query : (P ⊸ X.{uA, uB}).B answer) :
    (responder S).direction answer contract query = S.position query.1 :=
  rfl

/-- The canonical chart that forgets responder-contract evidence. -/
def responderChart (S : Display.{uA, uB, uC, uD} P) :
    Chart (responder S).total (P ⊸ X.{uA, uB}) :=
  (responder S).forget

@[simp]
theorem responderChart_toFunA (S : Display.{uA, uB, uC, uD} P)
    (answer : (P ⊸ X.{uA, uB}).A)
    (contract : (responder S).position answer) :
    (responderChart S).toFunA ⟨answer, contract⟩ = answer :=
  rfl

@[simp]
theorem responderChart_toFunB (S : Display.{uA, uB, uC, uD} P)
    (answer : (P ⊸ X.{uA, uB}).A)
    (contract : (responder S).position answer)
    (query : (P ⊸ X.{uA, uB}).B answer)
    (precondition : (responder S).direction answer contract query) :
    (responderChart S).toFunB ⟨answer, contract⟩ ⟨query, precondition⟩ = query :=
  rfl

/-- A displayed responder coalgebra is exactly the paper's local dependent
Mealy application obligation.

This is the object-action form of the paper's dependent Mealy application
obligation. The equivalence is stated for the existing `Responder` coalgebra
map `R.out`; no duplicate displayed dynamical-system structure is introduced. -/
def responderCoalgebraEquiv
    (S : Display.{uA, uB, uC, uD} P)
    {C : Type uE} (R : Responder C P) (F : C → Type uF) :
    Coalgebra (responder S) R.out F ≃
      ((state : C) → F state → (a : P.A) → (c : S.position a) →
        S.direction a c (R.answer state a) × F (R.next state a)) where
  toFun := fun displayed state witness a c =>
    let step := displayed state witness
    ⟨step.1 a c, step.2 ⟨a, PUnit.unit⟩ c⟩
  invFun := fun obligation state witness =>
    ⟨fun a c => (obligation state witness a c).1, fun
      | ⟨a, PUnit.unit⟩, c => (obligation state witness a c).2⟩
  left_inv displayed := by
    funext state witness
    apply Sigma.ext rfl
    rfl
  right_inv obligation := by
    funext state witness a c
    rfl

@[simp]
theorem responderCoalgebraEquiv_postcondition
    (S : Display.{uA, uB, uC, uD} P)
    {C : Type uE} (R : Responder C P) (F : C → Type uF)
    (displayed : Coalgebra (responder S) R.out F)
    (state : C) (witness : F state) (a : P.A) (c : S.position a) :
    ((responderCoalgebraEquiv S R F) displayed state witness a c).1 =
      (displayed state witness).1 a c :=
  rfl

@[simp]
theorem responderCoalgebraEquiv_next
    (S : Display.{uA, uB, uC, uD} P)
    {C : Type uE} (R : Responder C P) (F : C → Type uF)
    (displayed : Coalgebra (responder S) R.out F)
    (state : C) (witness : F state) (a : P.A) (c : S.position a) :
    ((responderCoalgebraEquiv S R F) displayed state witness a c).2 =
      (displayed state witness).2 ⟨a, PUnit.unit⟩ c :=
  rfl

@[simp]
theorem responderCoalgebraEquiv_symm_postcondition
    (S : Display.{uA, uB, uC, uD} P)
    {C : Type uE} (R : Responder C P) (F : C → Type uF)
    (obligation :
      (state : C) → F state → (a : P.A) → (c : S.position a) →
        S.direction a c (R.answer state a) × F (R.next state a))
    (state : C) (witness : F state) (a : P.A) (c : S.position a) :
    ((responderCoalgebraEquiv S R F).symm obligation state witness).1 a c =
      (obligation state witness a c).1 :=
  rfl

@[simp]
theorem responderCoalgebraEquiv_symm_next
    (S : Display.{uA, uB, uC, uD} P)
    {C : Type uE} (R : Responder C P) (F : C → Type uF)
    (obligation :
      (state : C) → F state → (a : P.A) → (c : S.position a) →
        S.direction a c (R.answer state a) × F (R.next state a))
    (state : C) (witness : F state) (a : P.A) (c : S.position a) :
    ((responderCoalgebraEquiv S R F).symm obligation state witness).2
        ⟨a, PUnit.unit⟩ c =
      (obligation state witness a c).2 :=
  rfl

end Display
end PFunctor
