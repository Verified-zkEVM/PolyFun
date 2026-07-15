/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Construct
public import PolyFun.ITree.Unfold

/-!
# Universe-polymorphic interaction-tree examples

These examples are compile-time canaries for the public universe contract of
`ITree`. Event positions, event directions, returned values, and coalgebra
states may inhabit independent universes.
-/

@[expose] public section

universe u uA uB uR uS uT uState

namespace ITree.UniverseExamples

variable {F : PFunctor.{uA, uB}} {R : Type uR} {S : Type uS}
  {State : Type uState}

/-- The one-step shape joins only the event-position and return universes. -/
example : Type (max uA uR) := ITree.Shape F R

/-- Directions of the one-step polynomial remain in the event-direction
universe. -/
example : PFunctor.{max uA uR, uB} := ITree.Poly F R

/-- The final coalgebra joins the two signature universes with the return
universe. -/
example : Type (max uA uB uR) := ITree F R

/-- A visible query can return a value from a universe unrelated to either
universe of the event signature. -/
def queryAndReturn (a : F.A) (k : F.B a → R) : ITree F R :=
  ITree.query a (fun answer => ITree.pure (k answer))

example (a : F.A) (k : F.B a → R) :
    ITree.shape (queryAndReturn a k) = .query a := by
  simp [queryAndReturn]

/-- Named bind supports a universe change in the return type. -/
def mixedBind (tree : ITree F R) (next : R → ITree F S) : ITree F S :=
  ITree.bind tree next

/-- Named map supports a universe change in the return type. -/
def mixedMap (f : R → S) (tree : ITree F R) : ITree F S :=
  ITree.map f tree

/-- Kleisli composition inherits the mixed-universe behavior of bind. -/
def mixedCat {T : Type uT} (first : R → ITree F S) (second : S → ITree F T) :
    R → ITree F T :=
  ITree.cat first second

/-- A non-returning loop may be assigned a result in any universe. -/
def mixedForever (tree : ITree F R) : ITree F S :=
  ITree.forever tree

/-- Discarding a result does not force the unit type into the source-result
universe. -/
def mixedIgnore (tree : ITree F R) : ITree F PUnit.{uT + 1} :=
  ITree.ignore tree

/-- Lean's `Monad` interface is necessarily homogeneous in the value universe;
the named operations above provide the heterogeneous API. -/
def homogeneousDo {A B : Type u} (tree : ITree F A) (next : A → ITree F B) :
    ITree F B := do
  next (← tree)

/-- Embedding an M-type behavior permits an independently universe-lifted
empty return type. -/
def behaviorToITree (tree : PFunctor.M F) : ITree F PEmpty.{uR + 1} :=
  PFunctor.M.toITree tree

/-- Dynamical-system states are also independent of the signature and empty
return universes. -/
def systemToITree (system : PFunctor.DynSystem State F) (state : State) :
    ITree F PEmpty.{uR + 1} :=
  system.toITree state

end ITree.UniverseExamples
