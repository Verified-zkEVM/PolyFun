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

universe u uA uA' uA'' uA'''

namespace PFunctor
namespace Handler

/-- The identity free handler for a polynomial interface. -/
def id (P : PFunctor.{uA, u}) : Handler (FreeM P) P :=
  fun a => FreeM.lift a

/-- Kleisli composition of free handlers, in categorical order:
`second.comp first` first interprets by `first`, then by `second`. -/
def comp {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u}}
    (second : Handler (FreeM R) Q) (first : Handler (FreeM Q) P) :
    Handler (FreeM R) P :=
  fun a => (first a).liftM second

@[simp]
theorem comp_apply {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u}}
    (second : Handler (FreeM R) Q) (first : Handler (FreeM Q) P)
    (a : P.A) :
    second.comp first a = (first a).liftM second :=
  rfl

@[simp]
theorem id_comp {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    (first : Handler (FreeM Q) P) :
    (id Q).comp first = first := by
  funext a
  exact FreeM.liftM_lift_eq_self (first a)

@[simp]
theorem comp_id {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    (second : Handler (FreeM Q) P) :
    second.comp (id P) = second := by
  funext a
  exact FreeM.liftM_lift second a

/-- Free-handler composition is associative in categorical order. -/
theorem comp_assoc
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u}} {V : PFunctor.{uA''', u}}
    (third : Handler (FreeM V) R)
    (second : Handler (FreeM R) Q)
    (first : Handler (FreeM Q) P) :
    (third.comp second).comp first = third.comp (second.comp first) := by
  funext a
  exact (FreeM.liftM_comp (first a) second third).symm

end Handler
end PFunctor
