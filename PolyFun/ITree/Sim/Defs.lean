/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Construct
public import PolyFun.ITree.Handler

/-! # ITree simulation operators

`ITree.simulate` interprets every event of the source spec via a `Handler`
to produce an interaction tree over the target spec. `ITree.mapSpec`
specialises this to event-renaming via a `PFunctor.Lens`, performing a pure
relabelling without inserting any extra silent steps or queries.

Both operators permit the source positions, source directions, target
positions, target directions, and return values to inhabit independent
universes. `Handler.comp` composes two handlers by simulating the output of
the first through the second.

The shape of `simulate` mirrors Coq's `interp` (`Core/Subevent.v`): we run
the source ITree, replacing every `query a c` with `bind (h a) c`, every
`step c` with `step (... continue ...)`, and every `pure r` with `pure r`.
The recursion is encoded with `iter`, leveraging the fact that the iteration
combinator already inserts a productive silent step at each loop step (so
`simulate` is automatically productive even if the source ITree spends a
long stretch in `query` nodes).
-/

@[expose] public section

universe uEA uEB uFA uFB uGA uGB uHA uHB uα

namespace ITree

variable {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
  {G : PFunctor.{uGA, uGB}} {α : Type uα}

/-! ### Generic simulation -/

/-- Simulate an interaction tree over events `E` by interpreting every
`E`-event via the handler `h : Handler E F`, producing an interaction tree
over events `F`.

This is the Lean analogue of Coq's `interp h : itree E ~> itree F`. -/
def simulate (h : Handler E F) (t : ITree E α) : ITree F α :=
  iter
    (fun (t : ITree E α) =>
      match shape' t with
      | ⟨.pure r, _⟩ => pure (.inr r)
      | ⟨.step, c⟩ => pure (.inl (c PUnit.unit))
      | ⟨.query a, c⟩ => bind (h a) (fun b => pure (.inl (c b))))
    t

/-! ### Handler composition -/

namespace Handler

/-- Compose event handlers by simulating the output of the first handler with
the second. Thus `second.comp first` interprets `E`-events as `F`-programs and
then interprets those `F`-programs over `G`.

Composition is maximally universe-polymorphic. Its pointwise weak identity and
pure-renaming laws are stated in `PolyFun.ITree.Sim.Facts`.
-/
def comp (second : Handler F G) (first : Handler E F) : Handler E G :=
  fun a => simulate second (first a)

@[simp] theorem comp_apply (second : Handler F G) (first : Handler E F) (a : E.A) :
    second.comp first a = simulate second (first a) := rfl

/-- Handler composition distributes definitionally over coproduct routing. -/
theorem comp_case {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uEB}}
    {G : PFunctor.{uGA, uGB}} {H : PFunctor.{uHA, uHB}}
    (outer : Handler G H) (left : Handler E G) (right : Handler F G) :
    outer.comp (Handler.case_ left right) =
      Handler.case_ (outer.comp left) (outer.comp right) := by
  funext a
  cases a <;> rfl

end Handler

/-! ### Event renaming -/

/-- Step transformer used by `mapSpec`. Given a polynomial-functor lens
`φ : PFunctor.Lens E F` and the current ITree node, produce one node of the
target ITree by relabelling the head event. -/
def mapSpecStep (φ : PFunctor.Lens E F) (t : ITree E α) : (Poly F α).Obj (ITree E α) :=
  match shape' t with
  | ⟨.pure r, _⟩ => ⟨.pure r, PEmpty.elim⟩
  | ⟨.step, c⟩ => ⟨.step, fun _ => c PUnit.unit⟩
  | ⟨.query a, c⟩ => ⟨.query (φ.toFunA a), fun b => c (φ.toFunB a b)⟩

@[simp] theorem mapSpecStep_pure (φ : PFunctor.Lens E F) (r : α) :
    mapSpecStep (α := α) φ (pure (F := E) r) = ⟨.pure r, PEmpty.elim⟩ := by
  simp [mapSpecStep]

@[simp] theorem mapSpecStep_step (φ : PFunctor.Lens E F) (t : ITree E α) :
    mapSpecStep φ (step t) = ⟨.step, fun _ => t⟩ := by
  simp [mapSpecStep]

@[simp] theorem mapSpecStep_query (φ : PFunctor.Lens E F) (a : E.A)
    (k : E.B a → ITree E α) :
    mapSpecStep (α := α) φ (query a k) =
      ⟨.query (φ.toFunA a), fun b => k (φ.toFunB a b)⟩ := by
  simp [mapSpecStep]

/-- Apply a polynomial-functor lens `φ : PFunctor.Lens E F` to every event
of an interaction tree, leaving the leaves and silent steps untouched.

This is the Lean analogue of Coq's `translate (h : E ~> F) : itree E ~> itree F`.

It coincides with `simulate (Handler.ofLens φ)` up to (weak) bisimulation;
defining it directly via `M.corec` produces a strongly bisimilar but more
efficient implementation that does not insert the silent step that `iter`
would otherwise add. -/
def mapSpec (φ : PFunctor.Lens E F) : ITree E α → ITree F α :=
  PFunctor.M.corec (F := Poly F α) (mapSpecStep φ)

end ITree
