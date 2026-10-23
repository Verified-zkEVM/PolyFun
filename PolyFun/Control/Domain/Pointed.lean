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

/-- Transport by any equality proof from a domain to itself is identity. -/
@[simp] theorem cast_self {D : PointedDomain.{u}} (h : D = D) (x : D) : cast h x = x := rfl

theorem cast_rfl {D : PointedDomain.{u}} (x : D) : cast rfl x = x := rfl

@[simp] theorem cast_bot {D E : PointedDomain.{u}} (h : D = E) : cast h ⊥ = ⊥ := by
  cases h
  rfl

/-- Transport preserves the underlying value across equal semantic domains. -/
@[simp] theorem cast_heq {D E : PointedDomain.{u}} (h : D = E) (x : D) :
    HEq (cast h x) x := by
  cases h
  rfl

/-- Equality after semantic transport is heterogeneous equality before transport. -/
theorem cast_eq_iff {D E : PointedDomain.{u}} (h : D = E) (x : D) (y : E) :
    cast h x = y ↔ HEq x y := by
  cases h
  exact ⟨heq_of_eq, eq_of_heq⟩

/-- Successive semantic transports compose without changing a computation. -/
theorem cast_cast {D E F : PointedDomain.{u}} (h : D = E) (k : E = F) (x : D) :
    cast k (cast h x) = cast (h.trans k) x := by
  cases h
  cases k
  rfl

/-- Pointwise correspondence identifies continuous functions across equal domains. -/
theorem hom_heq {D E : PointedDomain.{u}} {F G : PointedDomain.{v}}
    (hD : D = E) (hF : F = G)
    (f : OmegaCompletePartialOrder.ContinuousHom D F)
    (g : OmegaCompletePartialOrder.ContinuousHom E G)
    (h : ∀ x y, HEq x y → HEq (f x) (g y)) : HEq f g := by
  cases hD
  cases hF
  apply heq_of_eq
  apply OmegaCompletePartialOrder.ContinuousHom.ext
  intro x
  exact eq_of_heq (h x x HEq.rfl)

/-- Equal continuous unfolding maps have equal least fixed points across domain transport. -/
theorem fix_heq {D E : PointedDomain.{u}} (hD : D = E)
    (f : OmegaCompletePartialOrder.ContinuousHom D D)
    (g : OmegaCompletePartialOrder.ContinuousHom E E)
    (h : ∀ x y, HEq x y → HEq (f x) (g y)) :
    HEq f.fix g.fix := by
  cases hD
  exact congr_arg_heq (fun k : OmegaCompletePartialOrder.ContinuousHom D D => k.fix)
    (eq_of_heq (hom_heq rfl rfl f g h))

/-- Corresponding components form corresponding dependent semantic families. -/
theorem pi_heq {I : Type v} {D E : I → PointedDomain.{u}} (hD : ∀ i, D i = E i)
    {f : (i : I) → D i} {g : (i : I) → E i} (h : ∀ i, HEq (f i) (g i)) : HEq f g := by
  cases funext hD
  exact heq_of_eq (funext (fun i => eq_of_heq (h i)))

/-- Suspending corresponding values retains their correspondence. -/
theorem result_value_heq {D E : PointedDomain.{u}} {ε : Type v} (hD : D = E)
    {x : D} {y : E} (h : HEq x y) :
    HEq (DomainResult.value x : DomainResult ε D) (DomainResult.value y : DomainResult ε E) := by
  cases hD
  cases eq_of_heq h
  rfl

end PointedDomain
