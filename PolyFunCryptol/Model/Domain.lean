/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.Syntax
public import PolyFun.Control.Domain.Result
public import PolyFun.IPFunctor.Scoped.Domain

/-!
# Lazy semantic domains

Sequence elements and tuple components are computations. Function values are
continuous maps from computations to computations, so an unused argument
need not return. The outer computation separately records bottom, an error,
or the availability of the value's outer constructor.
-/

public section

open OmegaCompletePartialOrder

namespace Cryptol

/-- A value carrier with its information order and increasing suprema. -/
structure ValueDomain where
  /-- The semantic values. -/
  Carrier : Type
  /-- Their information order. -/
  order : OmegaCompletePartialOrder Carrier

attribute [instance] ValueDomain.order

instance : CoeSort ValueDomain Type := ⟨ValueDomain.Carrier⟩

/-- The value domain of a closed type. Its reduction computes the carrier
types of fields, arguments, and sequence positions in dependent APIs. -/
@[expose, implicit_reducible] noncomputable def valueDomain : ClosedTy → ValueDomain
  | .var e => e.elim
  | .bit => ⟨DiscreteOrder Bool, inferInstance⟩
  | .integer => ⟨DiscreteOrder Int, inferInstance⟩
  | .unit => ⟨DiscreteOrder Unit, inferInstance⟩
  | .seq l a => ⟨l.Index → DomainResult EvalError (valueDomain a), inferInstance⟩
  | .prod a b =>
      ⟨DomainResult EvalError (valueDomain a) × DomainResult EvalError (valueDomain b),
        inferInstance⟩
  | .arrow a b =>
      ⟨DomainResult EvalError (valueDomain a) →𝒄 DomainResult EvalError (valueDomain b),
        inferInstance⟩

/-- Semantic values at a type. -/
abbrev Value (a : ClosedTy) : Type := valueDomain a

/-- Possibly divergent or erroneous computations at a type. -/
abbrev Computation (a : ClosedTy) : Type := DomainResult EvalError (Value a)

/-- Each closed type's computations, as a pointed domain. -/
@[expose, reducible] noncomputable def computationDomain (a : ClosedTy) : PointedDomain :=
  .ofType (Computation a)

/-- A semantic environment supplies a suspended computation for each variable. -/
abbrev Environment (Γ : List ClosedTy) := IPFunctor.ScopedDomain.Env computationDomain Γ

/-! The generic environment operations, under the names used by the Cryptol model. -/

namespace Environment

export IPFunctor.ScopedDomain.Env (empty cons cons_zero cons_succ consContinuous
  consContinuous_apply append appendContinuous rename)

end Environment

end Cryptol
