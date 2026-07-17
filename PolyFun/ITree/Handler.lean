/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Basic
public import PolyFun.PFunctor.Lens.Basic

/-! # Event handlers

A *handler* `Handler E F` interprets each event of the source spec `E` as an
interaction tree over the target spec `F`. Equivalently, a handler is a
choice of `F`-program for every `E`-event. Handlers are the data of the
fundamental ITree simulation operator `ITree.simulate` (see
`PolyFun.ITree.Sim.Defs`).

The position and direction universes of `E` and `F` are all independent:
for `E : PFunctor.{uEA, uEB}` and `F : PFunctor.{uFA, uFB}`, handlers live in
`Type (max uEA uEB uFA uFB)`.

For pure event renaming (no extra silent steps and no extra queries),
`ITree.mapSpec` consumes a `PFunctor.Lens`. A `Lens E F` carries a forward
shape map `E.A → F.A` together with a backward arity map
`∀ a, F.B (toFunA a) → E.B a`, which is precisely the data needed to relabel
each `query` node of an interaction tree along an event-spec morphism.

## Naming

| Coq                | Lean                              |
| ------------------ | --------------------------------- |
| `E ~> itree F`     | `ITree.Handler E F`               |
| `E ~> F`           | `PFunctor.Lens E F`               |
| `handler E := ...` | `Handler.id`                      |
| `case_ E F`        | `Handler.case_`                   |
| handler composition | `Handler.comp` (in `Sim.Defs`)  |
-/

@[expose] public section

universe uEA uEB uFA uFB uGA uGB

namespace ITree

/-- An event handler `Handler E F` is a polymorphic interpretation of every
`E`-event as an `F`-program.

Concretely, for each event name `a : E.A` we choose an interaction tree of
type `ITree F (E.B a)` returning the answer expected by the source signature.

This is the Lean version of Coq's `Handler E F := E ~> itree F`. -/
def Handler (E : PFunctor.{uEA, uEB}) (F : PFunctor.{uFA, uFB}) :
    Type (max uEA uEB uFA uFB) :=
  ∀ a : E.A, ITree F (E.B a)

namespace Handler

variable {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
  {G : PFunctor.{uGA, uGB}}

/-- The trivial handler that interprets each `E`-event as itself, i.e. the
single-step `lift` from `PolyFun.ITree.Basic`. -/
def id (E : PFunctor.{uEA, uEB}) : Handler E E :=
  fun a => lift a

/-- Promote a polynomial-functor lens to a handler that performs a pure
renaming. For each source event `a : E.A`, the handler issues the renamed
event `φ.toFunA a` and feeds the answer back through the lens's backward
arity map.

There are no extra silent steps and no extra queries: this is the canonical
"event-renaming" handler. -/
def ofLens (φ : PFunctor.Lens E F) : Handler E F :=
  fun a => query (φ.toFunA a) (fun b => pure (φ.toFunB a b))

@[simp] theorem ofLens_id (E : PFunctor.{uEA, uEB}) :
    ofLens (PFunctor.Lens.id E) = id E := by
  funext a
  rfl

/-! ### Coproduct routing -/

/-- Route events from a coproduct signature through one of two handlers.

The source signatures share a direction universe because `PFunctor.sum`
currently requires it; their position universes and both universes of the
target signature remain independent. -/
def case_ {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uEB}}
    (left : Handler.{uEA, uEB, uGA, uGB} E G)
    (right : Handler.{uFA, uEB, uGA, uGB} F G) :
    Handler.{max uEA uFA, uEB, uGA, uGB} (E + F) G
  | .inl a => left a
  | .inr a => right a

@[simp] theorem case_inl {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uEB}}
    (left : Handler.{uEA, uEB, uGA, uGB} E G)
    (right : Handler.{uFA, uEB, uGA, uGB} F G) (a : E.A) :
    case_ left right (.inl a) = left a := rfl

@[simp] theorem case_inr {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uEB}}
    (left : Handler.{uEA, uEB, uGA, uGB} E G)
    (right : Handler.{uFA, uEB, uGA, uGB} F G) (a : F.A) :
    case_ left right (.inr a) = right a := rfl

/-- Copairing pure-renaming handlers agrees with copairing their underlying
lenses. -/
theorem case_ofLens {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uEB}}
    (left : PFunctor.Lens E G) (right : PFunctor.Lens F G) :
    case_ (ofLens left) (ofLens right) =
      ofLens (PFunctor.Lens.sumPair left right) := by
  funext a
  cases a <;> rfl

end Handler

end ITree
