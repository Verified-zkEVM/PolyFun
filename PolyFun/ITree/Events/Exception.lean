/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Sim.Defs

/-! # Exception events

A standard event signature for computations that may raise exceptions. The
polynomial functor `ExceptE ε` has a single event family `throw e` for
`e : ε`, with answer type `PEmpty` (the throw never resumes).

`interpExcept` eliminates exception events from a tree over `ExceptE ε + E`.
A thrown exception terminates as `Except.error`, while ordinary returns become
`Except.ok` and external `E`-events remain visible. `runExcept` is its
conventional runner alias.

Coq references:

* `Events/Exception.v` — `exceptE`, `interp_except`.
-/

@[expose] public section

universe uε uEA uB uα

namespace ITree

/-- Exception events over an error type `ε : Type u`. The single event
family is `throw e` for `e : ε`; the answer type `PEmpty` reflects the fact
that a thrown exception never returns. The error, empty-answer, and eventual
computation-result universes are independent. -/
def ExceptE (ε : Type uε) : PFunctor.{uε, uB} where
  A := ε
  B _ := PEmpty.{uB + 1}

namespace ExceptE

variable {ε : Type uε} {α : Type uα}

/-- Throw the exception `e`, never returning. The arbitrary return type `α`
is supplied by `PEmpty.elim` on the (empty) answer type of `e`. -/
def throw (e : ε) : ITree (ExceptE.{uε, uB} ε) α :=
  query (F := ExceptE.{uε, uB} ε) e PEmpty.elim

end ExceptE

/-! ## Exception interpretation -/

/-- One productive layer of exception interpretation. A thrown exception has
no continuation and becomes an immediate `Except.error` leaf. -/
def interpExceptStep {ε : Type uε} {E : PFunctor.{uEA, uB}}
    {α : Type uα}
    (t : ITree (ExceptE.{uε, uB} ε + E : PFunctor.{max uε uEA, uB}) α) :
    (Poly E (Except ε α)).Obj
      (ITree (ExceptE.{uε, uB} ε + E : PFunctor.{max uε uEA, uB}) α) :=
  match shape' t with
  | ⟨.pure r, _⟩ => ⟨.pure (.ok r), PEmpty.elim⟩
  | ⟨.step, c⟩ => ⟨.step, fun _ => c PUnit.unit⟩
  | ⟨.query (.inl e), _⟩ => ⟨.pure (.error e), PEmpty.elim⟩
  | ⟨.query (.inr e), c⟩ => ⟨.query e, c⟩

/-- Eliminate exception events from `t`, returning either the first thrown
exception or the ordinary result. External events remain visible. -/
def interpExcept {ε : Type uε} {E : PFunctor.{uEA, uB}}
    {α : Type uα}
    (t : ITree (ExceptE.{uε, uB} ε + E : PFunctor.{max uε uEA, uB}) α) :
    ITree E (Except ε α) :=
  PFunctor.M.corec interpExceptStep t

/-- Conventional runner name for `interpExcept`. -/
def runExcept {ε : Type uε} {E : PFunctor.{uEA, uB}}
    {α : Type uα}
    (t : ITree (ExceptE.{uε, uB} ε + E : PFunctor.{max uε uEA, uB}) α) :
    ITree E (Except ε α) :=
  interpExcept t

end ITree
