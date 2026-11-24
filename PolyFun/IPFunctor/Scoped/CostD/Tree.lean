/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import PolyFun.PFunctor.Free.Cost.Value
public import PolyFun.PFunctor.Free.Code

/-!
# Ticked programs

The evaluator of the cost language D returns a free program whose calls are the calls of an
interface `P` and ticks. A tick carries the amount it charges in a cost codomain `ω`. The ticks
are the calls of the linear polynomial functor `PFunctor.linear ω`: a tick at `w` has one answer.
A ticked program is a free program over `Ticked P ω = P + PFunctor.linear ω`.

## Main definitions

* `Ticked`, `tick`, `call`: the interface of ticked programs, a tick and a call of `P`.
* `erase`: the program with its ticks removed, the fold of the handler that keeps the calls of
  `P` and answers each tick at once.
* `cost`: the worst-case cost (`PFunctor.FreeM.cost`), with a call of `P` at `a` charged `q a`
  and a tick charged its amount.

## Main results

* `erase_pure`, `erase_bind`, `erase_tick`, `erase_call`: `erase` is a monad morphism that
  removes ticks and keeps calls.
* `cost_pure`, `cost_tick_bind`: a leaf costs nothing, and a tick adds its amount.
-/

@[expose] public section

universe u

namespace IPFunctor.CostD

open PFunctor

/-- The interface of ticked programs: the calls of `P` and the ticks, each tick carrying the
amount it charges. -/
abbrev Ticked (P : PFunctor.{u, u}) (ω : Type u) : PFunctor.{u, u} := P + PFunctor.linear ω

variable {P : PFunctor.{u, u}} {ω : Type u} {α β : Type u}

/-- A tick of amount `w`. -/
def tick (w : ω) : PFunctor.FreeM (Ticked P ω) PUnit :=
  PFunctor.FreeM.lift (P := Ticked P ω) (Sum.inr w)

/-- A call of `P` at `a` in a ticked program. -/
def call (a : P.A) : PFunctor.FreeM (Ticked P ω) (P.B a) :=
  PFunctor.FreeM.lift (P := Ticked P ω) (Sum.inl a)

/-- The handler that keeps the calls of `P` and answers each tick at once. -/
def eraseHandler : (a : (Ticked P ω).A) → PFunctor.FreeM P ((Ticked P ω).B a)
  | .inl a => PFunctor.FreeM.lift a
  | .inr _ => pure PUnit.unit

/-- A ticked program with its ticks removed. -/
def erase (x : PFunctor.FreeM (Ticked P ω) α) : PFunctor.FreeM P α :=
  x.liftM eraseHandler

/-- Unfolding lemma of `erase` at a leaf. -/
@[simp] theorem erase_pure (a : α) :
    erase (pure a : PFunctor.FreeM (Ticked P ω) α) = pure a := rfl

/-- `erase` commutes with bind. -/
@[simp] theorem erase_bind (x : PFunctor.FreeM (Ticked P ω) α)
    (f : α → PFunctor.FreeM (Ticked P ω) β) :
    erase (x >>= f) = erase x >>= fun a => erase (f a) :=
  PFunctor.FreeM.liftM_bind _ _ _

/-- Unfolding lemma of `erase` at a tick: the tick is answered at once. -/
@[simp] theorem erase_tick (w : ω) : erase (tick (P := P) w) = pure PUnit.unit := rfl

/-- Unfolding lemma of `erase` at a call: the call is kept. -/
@[simp] theorem erase_call (a : P.A) :
    erase (call (ω := ω) a) = PFunctor.FreeM.lift a := rfl

/-- The worst-case cost of a ticked program: a call of `P` at `a` costs `q a`, and a tick costs
its amount. -/
noncomputable def cost [Add ω] [Zero ω] [CompleteLattice ω] (q : P.A → ω)
    (x : PFunctor.FreeM (Ticked P ω) α) : ω :=
  PFunctor.FreeM.cost (Sum.elim q id) x

section Cost

variable [Add ω] [Zero ω] [CompleteLattice ω] (q : P.A → ω)

/-- Unfolding lemma of `cost` at a leaf. -/
@[simp] theorem cost_pure (a : α) : cost q (pure a : PFunctor.FreeM (Ticked P ω) α) = 0 := rfl

/-- A tick of amount `w` followed by `f` costs `w` plus the cost of `f`. -/
@[simp] theorem cost_tick_bind (w : ω) (f : PUnit → PFunctor.FreeM (Ticked P ω) α) :
    cost q (tick w >>= f) = w + cost q (f PUnit.unit) := by
  simp [cost, tick, PFunctor.FreeM.cost_bind']

end Cost

end IPFunctor.CostD
