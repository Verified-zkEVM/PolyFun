/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Free.Basic
public import PolyFun.PFunctor.Handler

/-!
# Identity and composition of free handlers

This module equips handlers valued in a free monad with their Kleisli identity,
and composes a free handler with a handler into any monad. The generic
`PFunctor.Handler` definition remains independent of `FreeM`.

`second.comp first` interprets each operation of `P` as a free program over `Q`
through `first`, then runs that program through `second : Handler m Q`. With
`m := FreeM R` this is Kleisli composition of free handlers; for a general monad
it is the precomposition that implements one interface in terms of another and
then runs the result. `id_comp` is the left-identity law for free handlers;
`comp_id`, `comp_assoc` and `liftM_comp` hold for any `LawfulMonad m`.

`ofLens l` reads a lens as the free handler that issues one translated request. Interpreting
through it is `FreeM.mapLens` (`liftM_ofLens`, `liftMHom_ofLens`), and composing a handler with
it pulls the handler back along the lens (`comp_ofLens`).
-/

@[expose] public section

universe u u' v uA uA' uA''

namespace PFunctor
namespace Handler

/-- The identity free handler for a polynomial interface. -/
@[implicit_reducible]
def id (P : PFunctor.{uA, u}) : Handler (FreeM P) P :=
  fun a => FreeM.lift a

/-- Regard a polynomial lens as the one-operation free handler that issues
the mapped operation and translates its answer through the lens. -/
def ofLens {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}}
    (f : Lens P Q) : Handler (FreeM Q) P :=
  fun a => FreeM.liftBind (f.toFunA a) fun answer =>
    FreeM.pure (f.toFunB a answer)

@[simp] theorem ofLens_apply
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}}
    (f : Lens P Q) (a : P.A) :
    ofLens f a = FreeM.liftBind (f.toFunA a) fun answer =>
      FreeM.pure (f.toFunB a answer) :=
  rfl

@[simp] theorem ofLens_id (P : PFunctor.{uA, u}) :
    ofLens (Lens.id P) = id P :=
  rfl

/-- Interpreting a program through the one-operation handler of a lens relabels it along the
lens. -/
theorem liftM_ofLens {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}} (l : Lens P Q)
    {α : Type u} (x : FreeM P α) : x.liftM (ofLens l) = x.mapLens l := by
  induction x with
  | pure _ => rfl
  | lift_bind a k ih => exact congrArg (FreeM.liftBind (l.toFunA a)) (funext fun d => ih _)

/-- Composition of a free handler with a handler into any monad, in categorical
order: `second.comp first` first interprets by `first`, then by `second`. With
`m := FreeM R` this is Kleisli composition of free handlers. The source and
intermediate direction universes agree because `FreeM.liftM` requires them to;
the target monad's universes remain independent. -/
@[implicit_reducible]
def comp {m : Type u → Type v} [Monad m] {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    (second : Handler m Q) (first : Handler (FreeM Q) P) :
    Handler m P :=
  fun a => (first a).liftM second

@[simp]
theorem comp_apply {m : Type u → Type v} [Monad m] {P : PFunctor.{uA, u}}
    {Q : PFunctor.{uA', u}} (second : Handler m Q) (first : Handler (FreeM Q) P)
    (a : P.A) :
    second.comp first a = (first a).liftM second :=
  rfl

/-- The one-operation handler embedding preserves lens composition. -/
theorem ofLens_comp
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u'}}
    (second : Lens Q R) (first : Lens P Q) :
    ofLens (second ∘ₗ first) = (ofLens second).comp (ofLens first) := rfl

/-- Pulling the one-operation handler of a lens back along another lens gives the one-operation
handler of the composite lens. -/
theorem comapLens_ofLens
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u'}}
    (second : Lens Q R) (first : Lens P Q) :
    (ofLens second).comapLens first = ofLens (second ∘ₗ first) := rfl

/-- Composing a handler with the one-operation handler of a lens pulls the handler back along
the lens. -/
theorem comp_ofLens {m : Type u → Type v} [Monad m] [LawfulMonad m] {P : PFunctor.{uA, u}}
    {Q : PFunctor.{uA', u}} (second : Handler m Q) (l : Lens P Q) :
    second.comp (ofLens l) = second.comapLens l := by
  funext a
  exact bind_pure_comp _ _

/-- Bundled form of `liftM_ofLens`: the fold of the one-operation handler of a lens is
`FreeM.mapLensHom`. -/
theorem liftMHom_ofLens {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}} (l : Lens P Q) :
    FreeM.liftMHom (ofLens l) = FreeM.mapLensHom l :=
  MonadHom.ext' fun _ x => liftM_ofLens l x

@[simp]
theorem id_comp {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    (first : Handler (FreeM Q) P) :
    (id Q).comp first = first := by
  funext a
  exact FreeM.liftM_lift_eq_self (first a)

@[simp]
theorem comp_id {m : Type u → Type v} [Monad m] [LawfulMonad m] {P : PFunctor.{uA, u}}
    (second : Handler m P) :
    second.comp (id P) = second := by
  funext a
  exact FreeM.liftM_lift second a

/-- Running a program through a composite handler runs it through `first`, then
runs the resulting free program through `second`. -/
@[simp]
theorem liftM_comp {m : Type u → Type v} [Monad m] [LawfulMonad m] {P : PFunctor.{uA, u}}
    {Q : PFunctor.{uA', u}} (second : Handler m Q) (first : Handler (FreeM Q) P)
    {α : Type u} (x : FreeM P α) :
    x.liftM (second.comp first) = (x.liftM first).liftM second :=
  (FreeM.liftM_comp x first second).symm

/-- Handler composition is associative in categorical order. -/
theorem comp_assoc {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}} {R : PFunctor.{uA'', u}}
    (third : Handler m R)
    (second : Handler (FreeM R) Q)
    (first : Handler (FreeM Q) P) :
    (third.comp second).comp first = third.comp (second.comp first) := by
  funext a
  exact (FreeM.liftM_comp (first a) second third).symm

end Handler
end PFunctor
