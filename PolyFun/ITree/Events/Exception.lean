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

Together with a handler that runs `throw e` to "abort with `e`", this gives
the standard exception monad as an ITree.

Coq references:

* `Events/Exception.v` — `exceptE`, `interp_except`.
-/

@[expose] public section

universe uε uB uα

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

end ITree
