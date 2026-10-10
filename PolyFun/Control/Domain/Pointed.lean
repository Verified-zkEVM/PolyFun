/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.Result

/-!
# Bundled pointed domains and dependent families

An indexed semantic type can compute its carrier, information order, and bottom
together. Dependent products introduce no extra suspension; `result` adds a fresh
outer bottom and error alternative, even when the inner domain already has bottom.
-/

public section

universe u v

/-- A carrier with increasing suprema and a least element. -/
structure PointedDomain where
  /-- Semantic computations. -/
  Carrier : Type u
  /-- Information order and increasing suprema. -/
  cpo : OmegaCompletePartialOrder Carrier
  /-- The least computation. -/
  bot : OrderBot Carrier

attribute [instance] PointedDomain.cpo PointedDomain.bot

instance : CoeSort PointedDomain (Type u) := ⟨PointedDomain.Carrier⟩

namespace PointedDomain

/-- Bundle an existing pointed omega-CPO without changing its carrier. -/
@[expose, reducible] def ofType (α : Type u) [OmegaCompletePartialOrder α] [OrderBot α] :
    PointedDomain := ⟨α, inferInstance, inferInstance⟩

/-- A dependent family of computations, ordered pointwise. -/
@[expose, reducible] def pi (ι : Type v) (D : ι → PointedDomain.{u}) : PointedDomain :=
  ofType ((i : ι) → D i)

/-- Suspend an entire family or computation, preserving its internal partial information. -/
@[expose, reducible] noncomputable def result (ε : Type v) (D : PointedDomain.{u}) :
    PointedDomain :=
  ofType (DomainResult ε D)

/-- Transport a computation along equality of its bundled semantic domains. -/
@[expose] def cast {D E : PointedDomain.{u}} (h : D = E) :
    OmegaCompletePartialOrder.ContinuousHom D E := by
  cases h
  exact OmegaCompletePartialOrder.ContinuousHom.id

@[simp] theorem cast_rfl {D : PointedDomain.{u}} (x : D) : cast rfl x = x := rfl

@[simp] theorem cast_bot {D E : PointedDomain.{u}} (h : D = E) : cast h ⊥ = ⊥ := by
  cases h
  rfl

/-- Successive semantic transports compose without changing a computation. -/
theorem cast_cast {D E F : PointedDomain.{u}} (h : D = E) (k : E = F) (x : D) :
    cast k (cast h x) = cast (h.trans k) x := by
  cases h
  cases k
  rfl

end PointedDomain
