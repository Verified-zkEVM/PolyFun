/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Sim.Facts

/-!
# Universe-polymorphic handler and simulation examples

These examples pin the independent universes of source signatures, target
signatures, returned values, and composed handlers. The concrete example also
checks coproduct routing and makes the answer selected by a composed handler
observable in the returned value.
-/

@[expose] public section

universe uEA uEB uFA uFB uGA uGB uHA uHB uQA uR

namespace ITree.HandlerSimulationExamples

variable {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
  {G : PFunctor.{uGA, uGB}} {Q : PFunctor.{uQA, uEB}} {R : Type uR}

/-- A handler's sort joins the four independent universes of its source and
target signatures. -/
example : Type (max uEA uEB uFA uFB) := ITree.Handler E F

/-- Simulation preserves a return type whose universe is independent of both
event signatures. -/
def simulateSeparated (handler : ITree.Handler E F) (tree : ITree E R) :
    ITree F R :=
  ITree.simulate handler tree

example (handler : ITree.Handler E F) (value : R) :
    ITree.simulate handler (ITree.pure value) = ITree.pure value :=
  ITree.simulate_pure handler value

/-- Pure event renaming has the same universe separation as generic
simulation. -/
def mapSpecSeparated (lens : PFunctor.Lens E F) (tree : ITree E R) :
    ITree F R :=
  ITree.mapSpec lens tree

example (first : PFunctor.Lens E F) (second : PFunctor.Lens F G)
    (tree : ITree E R) :
    ITree.mapSpec (second ∘ₗ first) tree =
      ITree.mapSpec second (ITree.mapSpec first tree) :=
  ITree.mapSpec_comp first second tree

/-- Handler composition permits all three signatures to use independent
position and direction universes. -/
def compSeparated (first : ITree.Handler E F) (second : ITree.Handler F G) :
    ITree.Handler E G :=
  second.comp first

/-- Coproduct routing only inherits the equal direction-universe constraint
of `PFunctor.sum`; the two position universes and target universes remain
independent. -/
def caseSeparated (left : ITree.Handler E G) (right : ITree.Handler Q G) :
    ITree.Handler.{max uEA uQA, uEB, uGA, uGB} (E + Q) G :=
  ITree.Handler.case_ left right

example {H : PFunctor.{uHA, uHB}} (outer : ITree.Handler G H)
    (left : ITree.Handler E G) (right : ITree.Handler Q G) :
    outer.comp (ITree.Handler.case_ left right) =
      ITree.Handler.case_ (outer.comp left) (outer.comp right) :=
  ITree.Handler.comp_case outer left right

/-! ## Observable routing and composition -/

inductive ReadEvent where
  | bit

inductive CountEvent where
  | amount

inductive ChoiceEvent where
  | choose

inductive FinalEvent where
  | tick

@[reducible] def ReadSpec : PFunctor := ⟨ReadEvent, fun | .bit => Bool⟩

@[reducible] def CountSpec : PFunctor := ⟨CountEvent, fun | .amount => Nat⟩

@[reducible] def ChoiceSpec : PFunctor := ⟨ChoiceEvent, fun | .choose => Bool⟩

@[reducible] def FinalSpec : PFunctor := ⟨FinalEvent, fun | .tick => Bool⟩

def readHandler : ITree.Handler ReadSpec FinalSpec
  | .bit => ITree.pure true

def countHandler : ITree.Handler CountSpec FinalSpec
  | .amount => ITree.pure 7

example :
    ITree.Handler.case_ readHandler countHandler (.inl .bit) = ITree.pure true :=
  rfl

example :
    ITree.Handler.case_ readHandler countHandler (.inr .amount) =
      countHandler .amount :=
  rfl

example : countHandler .amount = ITree.pure (7 : Nat) := rfl

/-- The first handler negates the answer supplied by its target event. -/
def negateHandler : ITree.Handler ReadSpec ChoiceSpec
  | .bit => ITree.query .choose (fun answer => ITree.pure (!answer))

/-- The second handler resolves that target event with `true`. -/
def chooseTrueHandler : ITree.Handler ChoiceSpec FinalSpec
  | .choose => ITree.pure true

/-- Composition order and answer flow are observable: `true` is selected by
the second handler, negated by the first handler's continuation, and returned
as `false` after the productivity-forced silent step. -/
example : chooseTrueHandler.comp negateHandler .bit =
    ITree.step (ITree.pure false) := by
  rw [ITree.Handler.comp_apply, negateHandler, ITree.simulate_query_eq_bind,
    chooseTrueHandler, ITree.bind_pure_left, ITree.simulate_pure]
  rfl

end ITree.HandlerSimulationExamples
