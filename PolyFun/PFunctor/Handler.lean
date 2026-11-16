/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.Lens.Basic

/-!
# Monadic Handlers for Polynomial Functors

A `PFunctor.Handler m q` chooses a direction of `q` at each position, with the
choice interpreted in the type constructor `m`. This is the generic interface
consumed by `FreeM.liftM`; it does not depend on machines or dynamical systems.
In particular, taking `m := StateT σ n` threads one shared runtime state through
every handled position. That ambient state is distinct from a dynamical
system's private operational state.

A handler is contravariant in its interface and covariant in its target. `Handler.comapLens`
pulls a handler back along a lens: a request of the source interface is answered by the
handler at the translated request, with the answer translated back by the lens. `mapTarget`
changes the target. Interpreting a program relabelled along a lens is interpreting the original
program through the pulled-back handler (`FreeM.liftM_mapLens`).
-/

@[expose] public section

universe u v w uA uA' uI

namespace PFunctor

/-- A **handler** for the interface `q`: a monadic choice of direction at each
position (a Kleisli section of `q`). With `m := Id` this is an ordinary
dependent choice of one direction at every position, while a probabilistic
monad gives a randomized choice. -/
abbrev Handler (m : Type u → Type v) (q : PFunctor.{uA, u}) :=
  (a : q.A) → m (q.B a)

namespace Handler

/-- Postcompose every answer computation of a handler by a polymorphic map
between target type constructors. No monad laws are needed for this basic
change-of-target operation. -/
def mapTarget {m : Type u → Type v} {n : Type u → Type w}
    {q : PFunctor.{uA, u}} (transform : ∀ {α : Type u}, m α → n α)
    (handler : PFunctor.Handler m q) : PFunctor.Handler n q :=
  fun position => transform (handler position)

@[simp, grind =] theorem mapTarget_apply {m : Type u → Type v} {n : Type u → Type w}
    {q : PFunctor.{uA, u}} (transform : ∀ {α : Type u}, m α → n α)
    (handler : PFunctor.Handler m q) (position : q.A) :
    mapTarget transform handler position = transform (handler position) :=
  rfl

@[simp, grind =] theorem mapTarget_id {m : Type u → Type v}
    {q : PFunctor.{uA, u}} (handler : PFunctor.Handler m q) :
    mapTarget (fun computation => computation) handler = handler :=
  rfl

theorem mapTarget_mapTarget {m : Type u → Type v} {n : Type u → Type w}
    {o : Type u → Type uI} {q : PFunctor.{uA, u}}
    (second : ∀ {α : Type u}, n α → o α)
    (first : ∀ {α : Type u}, m α → n α)
    (handler : PFunctor.Handler m q) :
    mapTarget second (mapTarget first handler) =
      mapTarget (fun computation => second (first computation)) handler :=
  rfl

@[deprecated (since := "2026-10-19")] alias mapTarget_comp := mapTarget_mapTarget

/-! ## Pulling a handler back along a lens -/

section comapLens

variable {m : Type u → Type v} [Functor m] {P : PFunctor.{uA, u}} {Q : PFunctor.{uI, u}}

/-- Pull a handler back along a lens. A request `a` of `P` is answered by `handler` at the
request `l.toFunA a` of `Q`, and the answer is translated back by `l.toFunB a`. -/
def comapLens (handler : PFunctor.Handler m Q) (l : Lens P Q) : PFunctor.Handler m P :=
  fun a => l.toFunB a <$> handler (l.toFunA a)

@[simp, grind =] theorem comapLens_apply (handler : PFunctor.Handler m Q) (l : Lens P Q)
    (a : P.A) : comapLens handler l a = l.toFunB a <$> handler (l.toFunA a) :=
  rfl

/-- Pulling a handler back along the identity lens returns the handler. -/
@[simp] theorem comapLens_id [LawfulFunctor m] (handler : PFunctor.Handler m P) :
    comapLens handler (Lens.id P) = handler := by
  funext a
  exact id_map (handler a)

/-- Pulling a handler back along a composite lens pulls it back along each lens in turn. -/
theorem comapLens_comp [LawfulFunctor m] {R : PFunctor.{uA', u}}
    (handler : PFunctor.Handler m R) (l₂ : Lens Q R) (l₁ : Lens P Q) :
    comapLens handler (l₂ ∘ₗ l₁) = comapLens (comapLens handler l₂) l₁ := by
  funext a
  exact comp_map (l₂.toFunB (l₁.toFunA a)) (l₁.toFunB a)
    (handler (l₂.toFunA (l₁.toFunA a)))

/-- Changing the target by a map that commutes with `Functor.map` commutes with pulling back
along a lens. -/
theorem mapTarget_comapLens {n : Type u → Type w} [Functor n]
    (transform : ∀ {α : Type u}, m α → n α)
    (htransform : ∀ {α β : Type u} (f : α → β) (x : m α),
      transform (f <$> x) = f <$> transform x)
    (handler : PFunctor.Handler m Q) (l : Lens P Q) :
    mapTarget transform (comapLens handler l) = comapLens (mapTarget transform handler) l := by
  funext a
  exact htransform _ _

end comapLens

/-- An effectful stateful handler for `q`: on each position it reads a state,
performs effects in `m`, and returns a direction together with the next state.

This is a transparent name for `Handler (StateT S m) q`, so it introduces no
new data or laws. At `m := Id` it is the pure Kleisli--Mealy presentation used
by `Responder.equivStateful`. -/
abbrev Stateful (m : Type u → Type v) (S : Type u)
    (q : PFunctor.{uA, u}) :=
  Handler (StateT S m) q

/-- Combine monadic handlers for an indexed family into a handler for its
indexed coproduct. -/
def sigma {I : Type uI} {P : I → PFunctor.{uA, u}} {m : Type u → Type v}
    (f : (i : I) → PFunctor.Handler m (P i)) : PFunctor.Handler m (PFunctor.sigma P) :=
  fun a => f (PFunctor.sigma.fst a) (PFunctor.sigma.snd a)

@[simp]
theorem sigma_apply {I : Type uI} {P : I → PFunctor.{uA, u}} {m : Type u → Type v}
    (f : (i : I) → PFunctor.Handler m (P i)) (i : I) (a : (P i).A) :
    sigma f (PFunctor.sigma.mk i a) = f i a :=
  rfl

end Handler

end PFunctor
