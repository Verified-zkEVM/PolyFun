/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.Basic
public import PolyFun.PFunctor.Trace
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Charges on an interface

A charge prices the calls of an interface `P` in a cost type `ω`: a call at position `a` costs
`c a`. Throughout PolyFun a charge is the plain function `c : P.A → ω`; the cost of a program is a
fold of its charge (`PolyFun.PFunctor.Free.Cost`).

As a polynomial map, a charge is a lens into the constant polynomial `C ω`, whose positions are the
prices and which has no directions to answer: `Lens.toConst c`, and every such lens has this form
(`Lens.toConstEquiv`). Charges on composite interfaces are then lens constructions: pulling a
charge back along a lens is composition (`Lens.toConst_comp`), and the charge on a sum is the
copairing (`Lens.sumPair_toConst`).

A charge read off events instead of positions, `e : P.Idx → ω`, prices a call together with its
answer. `TraceList.charge e` extends it additively to the event traces of `PolyFun.PFunctor.Trace`.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uE w

namespace PFunctor

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {ω : Type w}

namespace Lens

/-- Pulling a charge back along a lens is lens composition. -/
@[simp]
theorem toConst_comp (c : Q.A → ω) (l : Lens P Q) :
    (toConst c : Lens Q (C.{w, uE} ω)) ∘ₗ l = toConst (c ∘ l.toFunA) :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun e => PEmpty.elim e

/-- The charge on a sum of interfaces is the copairing of the charges. -/
@[simp]
theorem sumPair_toConst {Q : PFunctor.{uA₂, uB}} (c₁ : P.A → ω) (c₂ : Q.A → ω) :
    sumPair (toConst c₁ : Lens P (C.{w, uE} ω)) (toConst c₂) = toConst (Sum.elim c₁ c₂) :=
  Lens.ext _ _ (fun a => by cases a <;> rfl) fun _ => funext fun e => PEmpty.elim e

end Lens

namespace TraceList

variable [AddMonoid ω]

/-- The additive valuation of an event trace: the sum of the charges of its events. -/
def charge (e : P.Idx → ω) (t : TraceList P) : ω :=
  ((FreeMonoid.toList t).map e).sum

variable (e : P.Idx → ω)

@[simp]
theorem charge_one : charge e (1 : TraceList P) = 0 :=
  rfl

@[simp]
theorem charge_nil : charge e ([] : TraceList P) = 0 :=
  rfl

@[simp]
theorem charge_cons (i : P.Idx) (t : TraceList P) :
    charge e ((i :: t : List P.Idx) : TraceList P) = e i + charge e t :=
  List.sum_cons

@[simp]
theorem charge_of (i : P.Idx) : charge e (FreeMonoid.of i) = e i := by
  simp [charge]

@[simp]
theorem charge_mul (s t : TraceList P) : charge e (s * t) = charge e s + charge e t := by
  simp [charge]

end TraceList

end PFunctor
