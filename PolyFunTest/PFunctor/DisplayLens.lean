/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Lens

/-!
# Regression tests for morphisms of polynomial displays

These examples exercise the forward displayed-position map, the dependent
backward displayed-direction map, totalization, the one-operation handler
embedding, and heterogeneous source/target response universes.
-/

@[expose] public section

namespace PFunctor.DisplayLensCanary

universe uA uB uC uD uA' uB' uC' uD'

/-- A displayed lens retains independent universes for both base interfaces
and both displayed fibers. -/
def heterogeneous
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB', uC', uD'} Q}
    (base : Lens P Q)
    (toPosition : (a : P.A) → S.position a → T.position (base.toFunA a))
    (toDirection : (a : P.A) → (c : S.position a) →
      (answer : Q.B (base.toFunA a)) →
      T.direction (base.toFunA a) (toPosition a c) answer →
        S.direction a c (base.toFunB a answer)) :
    Display.Lens S T base :=
  ⟨toPosition, toDirection⟩

def heterogeneousTotal
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB', uC', uD'} Q}
    {base : Lens P Q} (displayed : Display.Lens S T base) :
    Lens S.total T.total :=
  displayed.toTotal

def heterogeneousHandler
    {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB'}}
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB', uC', uD'} Q}
    {base : Lens P Q} (displayed : Display.Lens S T base) :
    Display.Handler S T (Handler.ofLens base) :=
  displayed.toHandler

abbrev Source : PFunctor := ⟨Bool, fun _ => Bool⟩

abbrev Target : PFunctor := ⟨PUnit, fun _ => Nat⟩

abbrev base : Lens Source Target where
  toFunA _ := PUnit.unit
  toFunB _ answer := decide (answer % 2 = 0)

abbrev sourceDisplay : Display Source where
  position _ := Bool
  direction _ _ _ := Bool

abbrev targetDisplay : Display Target where
  position _ := String
  direction _ _ _ := Nat

abbrev displayed : Display.Lens sourceDisplay targetDisplay base where
  toPosition _ contract := if contract = true then "true" else "false"
  toDirection _ _ _ direction := decide (direction % 2 = 0)

example : displayed.toPosition true true = "true" :=
  rfl

example : displayed.toPosition false false = "false" :=
  rfl

example : displayed.toDirection true true 3 4 = true :=
  rfl

example : displayed.toDirection false false 2 3 = false :=
  rfl

example : displayed.toTotal.toFunA ⟨true, true⟩ =
    ⟨PUnit.unit, "true"⟩ :=
  rfl

example : displayed.toTotal.toFunB ⟨true, true⟩ ⟨3, 4⟩ =
    ⟨false, true⟩ :=
  rfl

example : ((displayed.toHandler true true).2 3 4).down = true :=
  rfl

example :
    Display.Handler.transport rfl displayed.toHandler = displayed.toHandler := by
  simp

end PFunctor.DisplayLensCanary
