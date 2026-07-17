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

example (tree : ITree E R) :
    ITree.WeakBisim (ITree.simulate (ITree.Handler.id E) tree) tree :=
  ITree.simulate_id tree

example (handler : ITree.Handler E F) (value : R) :
    ITree.simulate handler (ITree.pure value) = ITree.pure value :=
  ITree.simulate_pure handler value

example (handler : ITree.Handler E F) (event : E.A)
    (cont : E.B event → ITree E R) :
    ITree.simulate handler (ITree.query event cont) =
      ITree.bind (handler event)
        (fun answer => ITree.step (ITree.simulate handler (cont answer))) :=
  ITree.simulate_query_eq_bind handler event cont

example {S : Type uQA} {RR : R → S → Prop}
    (handler : ITree.Handler E F) {tree : ITree E R} {tree' : ITree E S}
    (h : ITree.WeakBisimRel RR tree tree') :
    ITree.WeakBisimRel RR (ITree.simulate handler tree)
      (ITree.simulate handler tree') :=
  ITree.simulate_weakBisimRel handler h

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

example {S : Type uQA} (lens : PFunctor.Lens E F)
    (tree : ITree E R) (cont : R → ITree E S) :
    ITree.mapSpec lens (ITree.bind tree cont) =
      ITree.bind (ITree.mapSpec lens tree)
        (fun value => ITree.mapSpec lens (cont value)) :=
  ITree.mapSpec_bind lens tree cont

example {S : Type uQA} (lens : PFunctor.Lens E F)
    (f : R → S) (tree : ITree E R) :
    ITree.mapSpec lens (ITree.map f tree) =
      ITree.map f (ITree.mapSpec lens tree) :=
  ITree.mapSpec_map lens f tree

example {S : Type uQA} (lens : PFunctor.Lens E F)
    (body : S → ITree E (S ⊕ R)) (init : S) :
    ITree.mapSpec lens (ITree.iter body init) =
      ITree.iter (fun s => ITree.mapSpec lens (body s)) init :=
  ITree.mapSpec_iter lens body init

example {S : Type uQA} {T : Type uHA} (lens : PFunctor.Lens E F)
    (first : R → ITree E S) (second : S → ITree E T) (value : R) :
    ITree.mapSpec lens (ITree.cat first second value) =
      ITree.cat (ITree.mapSpec lens ∘ first)
        (ITree.mapSpec lens ∘ second) value :=
  ITree.mapSpec_cat lens first second value

/-- Handler composition permits all three signatures to use independent
position and direction universes. -/
def compSeparated (first : ITree.Handler E F) (second : ITree.Handler F G) :
    ITree.Handler E G :=
  second.comp first

example (first : ITree.Handler E F) (second : ITree.Handler F G)
    (tree : ITree E R) :
    ITree.WeakBisim
      (ITree.simulate second (ITree.simulate first tree))
      (ITree.simulate (second.comp first) tree) :=
  ITree.simulate_comp second first tree

example {H : PFunctor.{uHA, uHB}} (first : ITree.Handler E F)
    (second : ITree.Handler F G) (third : ITree.Handler G H) (a : E.A) :
    ITree.WeakBisim (third.comp (second.comp first) a)
      ((third.comp second).comp first a) :=
  ITree.Handler.comp_assoc_apply third second first a

example (first : PFunctor.Lens E F) (second : PFunctor.Lens F G)
    (a : E.A) :
    ITree.WeakBisim
      ((ITree.Handler.ofLens second).comp (ITree.Handler.ofLens first) a)
      (ITree.Handler.ofLens (second ∘ₗ first) a) :=
  ITree.Handler.ofLens_comp_apply first second a

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

/-- Sequential and composite interpretation agree on a query whose answer is
transformed by the inner handler and resolved by the outer handler. -/
example : ITree.WeakBisim
    (ITree.simulate chooseTrueHandler
      (ITree.simulate negateHandler
        (ITree.query .bit (fun answer => ITree.pure answer))))
    (ITree.simulate (chooseTrueHandler.comp negateHandler)
      (ITree.query .bit (fun answer => ITree.pure answer))) :=
  ITree.simulate_comp chooseTrueHandler negateHandler _

end ITree.HandlerSimulationExamples
