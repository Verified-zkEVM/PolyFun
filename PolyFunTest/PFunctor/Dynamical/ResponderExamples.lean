/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Responder

/-!
# Examples for responders (stateful answerers over the internal hom)

Regression tests for `PFunctor/Dynamical/Responder.lean`: the `committed` /
`answer` / `next` accessors, the stateless `ofSection` / `ofHandler`
constructors, and the Kleisli–Mealy bridge `equivStateHandler` with its
definitional round-trips.
-/

@[expose] public section

namespace PFunctor
namespace Responder.Examples

/-- A query interface with a single query type answered by a natural number. -/
abbrev q : PFunctor.{0, 0} := monomial PUnit Nat

/-- A responder that returns its state as the answer to every query and
increments its state on each query. -/
def echoResponder : Responder Nat q :=
  Responder.mk' (fun s _ => s) (fun s _ => s + 1)

example : echoResponder.answer 5 PUnit.unit = (5 : Nat) := rfl

example : echoResponder.next 5 PUnit.unit = 6 := rfl

/-- `answer` reads the committed section at the query asked. -/
example (s : Nat) (a : PUnit) :
    echoResponder.answer s a = (echoResponder.committed s).toFunB a PUnit.unit := rfl

/-! ## Stateless responders -/

/-- A deterministic handler yields the same responder as its section lens. -/
example (h : Handler Id q) :
    (Responder.ofHandler h : Responder PUnit.{1} q) =
      Responder.ofSection (sectionLens h) := rfl

/-! ## The Kleisli–Mealy bridge -/

/-- The `Responder ≃ Handler (StateT S Id)` bridge round-trips definitionally. -/
example (R : Responder Nat q) :
    Responder.equivStateHandler.symm (Responder.equivStateHandler R) = R := rfl

example (h : Handler (StateT Nat Id) q) :
    Responder.equivStateHandler (Responder.equivStateHandler.symm h) = h := rfl

/-- The forward direction of the bridge answers from the state and threads the
next state, i.e. it is a Mealy step in Kleisli form. -/
example (s : Nat) (a : PUnit) :
    echoResponder.toStateHandler a s = (echoResponder.answer s a, echoResponder.next s a) :=
  rfl

end Responder.Examples
end PFunctor
