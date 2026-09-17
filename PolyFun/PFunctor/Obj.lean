/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Equality of polynomial objects

Extensionality and constructor injectivity through the public shape and child
projections of `PFunctor.Obj`.
-/

public section

namespace PFunctor.Obj

universe uA uB u

variable {P : PFunctor.{uA, uB}} {α : Type u}

-- Upstream candidate: Mathlib.Data.PFunctor.Univariate.Basic, alongside Obj.rec.
/-- Polynomial objects are equal when their shapes and child families agree. -/
@[ext]
theorem ext {x y : P α} (h : x.fst = y.fst) (h' : HEq x.snd y.snd) : x = y := by
  cases x using Obj.rec with | mk a f =>
    cases y using Obj.rec with | mk b g =>
      cases h
      cases h'
      rfl

/-- Equal constructed polynomial objects have equal shapes and child families. -/
theorem mk.inj {a b : P.A} {f : P.B a → α} {g : P.B b → α}
    (h : Obj.mk a f = Obj.mk b g) : a = b ∧ HEq f g :=
  Obj.ext_iff.mp h

/-- Constructor injectivity for polynomial objects. -/
@[simp]
theorem mk.inj_iff {a b : P.A} {f : P.B a → α} {g : P.B b → α} :
    Obj.mk a f = Obj.mk b g ↔ a = b ∧ HEq f g :=
  Obj.ext_iff

end PFunctor.Obj
