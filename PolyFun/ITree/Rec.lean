/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Sim.Defs

/-! # Recursive procedure helpers

`ITree.mutualRec` and `ITree.fixRec` are the standard recursive procedure-call
combinators built on top of the `PFunctor.sum` infrastructure. The event
`CallE α β` describes "one recursive call expecting an `α`-argument and
returning a `β`-result"; it is the source signature passed to `fixRec`.

Semantically, a body `body : Handler D (D + E)` describes "one layer" of a
potentially recursive procedure: it may emit `D`-calls (recursive) or
`E`-calls (external). `mutualRec body` returns a `Handler D E` that folds
the recursion away while leaving every external `E`-event intact. The
implementation is a single `ITree.corec` over `ITree (D + E)`, with
each recursive `D`-event replaced by one silent `step` followed by
`bind (body d) continuation`. The silent step is what makes the corec
productive.

`D` and `E` may have independent event-position universes, and every final
result universe is independent of the event signatures. Their direction
universes remain equal because the current `PFunctor.sum` representation
requires that genuine local constraint. In particular, `CallE α β` itself
does have independent argument and result universes; `fixRec` only requires
the external signature's direction universe to agree with that of `β` at the
coproduct boundary.

Coq references:

* `Interp/Recursion.v` — `mrec`, `rec`, `interp_mrec`, `calling'`.
* `Core/CategoryOps.v` — the underlying KTree categorical structure.
-/

@[expose] public section

universe uDA uEA uB uα uCallA uCallB

namespace ITree

/-- `CallE α β` is a polynomial functor with a single event, modelling "make
a recursive call with an `α`-argument and expect a `β`-result".

In Coq this is `inductive callE (A B : Type) : Type → Type | Call : A →
callE A B B`. Translated to a polynomial functor, the event name carries the
input `α`-value and the answer type is constantly `β`. -/
def CallE (α : Type uCallA) (β : Type uCallB) : PFunctor.{uCallA, uCallB} where
  A := α
  B _ := β

namespace CallE

variable {α : Type uCallA} {β : Type uCallB}

/-- Issue a single recursive call, returning its result. -/
def call (a : α) : ITree (CallE α β) β :=
  lift (F := CallE α β) a

end CallE

/-! ### Mutual recursion -/

/-- Step transformer used by `mutualRec`. Given a handler `body` that may
itself emit `D`-calls, produce one node of the output `ITree E α` from the
current state `u : ITree (D + E) α`.

The four cases mirror the ITree shape constructors:

* `.pure r` — emit `.pure r`.
* `.step c` — pass the silent step through.
* `.query (.inl d) c` — emit a silent `.step` whose continuation runs
  `bind (body d) c`, i.e. splice in the recursive body.
* `.query (.inr e) c` — emit `.query e` with the same continuation.

The `.step` inserted in the `.inl` case is what keeps the enclosing
`ITree.corec` productive even in the presence of unbounded recursive
calls. -/
def mutualRecStep {D : PFunctor.{uDA, uB}} {E : PFunctor.{uEA, uB}} {α : Type uα}
    (body : ∀ a : D.A, ITree (D + E : PFunctor.{max uDA uEA, uB}) (D.B a))
    (u : ITree (D + E : PFunctor.{max uDA uEA, uB}) α) :
    (ViewPoly E α).Obj (ITree (D + E : PFunctor.{max uDA uEA, uB}) α) :=
  match ITree.shape' u with
  | ⟨.pure r, _⟩ => ⟨.pure r, PEmpty.elim⟩
  | ⟨.step, c⟩ => ⟨.step, fun _ => c PUnit.unit⟩
  | ⟨.query (.inl d), c⟩ => ⟨.step, fun _ => bind (body d) c⟩
  | ⟨.query (.inr e), c⟩ => ⟨.query e, c⟩

/-- Interpret a tree over the combined spec `D + E` by splicing recursive
`D`-calls into the body. -/
def interpMrec {D : PFunctor.{uDA, uB}} {E : PFunctor.{uEA, uB}} {α : Type uα}
    (body : ∀ a : D.A, ITree (D + E : PFunctor.{max uDA uEA, uB}) (D.B a))
    (u : ITree (D + E : PFunctor.{max uDA uEA, uB}) α) : ITree E α :=
  ITree.corec (mutualRecStep body) u

/-- `ITree.mutualRec body req` interprets a `D`-request `req` by repeatedly
invoking `body : Handler D (D + E)`. Each recursive `D`-call in the body is
silent-step-guarded so the combined corecursive definition is productive.

This is the Lean version of Coq's `mrec`. -/
def mutualRec {D : PFunctor.{uDA, uB}} {E : PFunctor.{uEA, uB}}
    (body : ∀ a : D.A, ITree (D + E : PFunctor.{max uDA uEA, uB}) (D.B a))
    (req : D.A) : ITree E (D.B req) :=
  interpMrec body (body req)

/-- `ITree.fixRec body a` defines a single recursive procedure with input
`α`, recursive-call argument feedback, and result `β`, returning the
specialised tree at input `a`.

This is the Lean version of Coq's `rec`. It is a direct specialisation of
`mutualRec` to the single-call event signature `CallE α β`. -/
def fixRec {E : PFunctor.{uEA, uB}} {α : Type uCallA} {β : Type uB}
    (body : α → ITree (CallE α β + E : PFunctor.{max uCallA uEA, uB}) β) (a : α) : ITree E β :=
  mutualRec (D := CallE α β) (E := E) body a

end ITree
