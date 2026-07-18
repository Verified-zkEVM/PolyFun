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

This module equips handlers valued in a free monad with their Kleisli identity
and categorical-order composition. The generic `PFunctor.Handler` definition
remains independent of `FreeM`.
-/

@[expose] public section

universe u u' uA uA' uA'' uA'''

namespace PFunctor
namespace Handler

/-- The identity free handler for a polynomial interface. -/
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

/-- Kleisli composition of free handlers, in categorical order:
`second.comp first` first interprets by `first`, then by `second`. The source
and intermediate direction universes agree because `FreeM.liftM` requires
them to; the final target direction universe remains independent. -/
def comp {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u'}}
    (second : Handler (FreeM R) Q) (first : Handler (FreeM Q) P) :
    Handler (FreeM R) P :=
  fun a => (first a).liftM second

@[simp]
theorem comp_apply {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u'}}
    (second : Handler (FreeM R) Q) (first : Handler (FreeM Q) P)
    (a : P.A) :
    second.comp first a = (first a).liftM second :=
  rfl

/-- The one-operation handler embedding preserves lens composition. -/
theorem ofLens_comp
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u'}}
    (second : Lens Q R) (first : Lens P Q) :
    ofLens (second ∘ₗ first) = (ofLens second).comp (ofLens first) := by
  funext operation
  rfl

@[simp]
theorem id_comp {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    (first : Handler (FreeM Q) P) :
    (id Q).comp first = first := by
  funext a
  exact FreeM.liftM_lift_eq_self (first a)

@[simp]
theorem comp_id {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}}
    (second : Handler (FreeM Q) P) :
    second.comp (id P) = second := by
  funext a
  exact FreeM.liftM_lift second a

/-- Free-handler composition is associative in categorical order. -/
theorem comp_assoc
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u}} {V : PFunctor.{uA''', u'}}
    (third : Handler (FreeM V) R)
    (second : Handler (FreeM R) Q)
    (first : Handler (FreeM Q) P) :
    (third.comp second).comp first = third.comp (second.comp first) := by
  funext a
  exact (FreeM.liftM_comp (first a) second third).symm

end Handler
end PFunctor
