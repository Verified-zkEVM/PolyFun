/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Basic

/-!
# Charts Between Indexed Polynomial Functors

A `Chart P Q` between two indexed polynomial functors `P Q : IPFunctor I J` is a *covariant*
morphism: forward maps on both positions and responses, together with the source-index
preservation law `src_eq` in the chart direction (the pushed-forward response and the
original response have the same source in `I`).

Charts and lenses are dual: lenses pull responses *back* (contravariantly), charts push them
*forward*. See [`Lens`](../Lens/Basic.lean) for the contravariant analogue.

This file provides the basic structure plus identity, composition, and the structural
equivalence companion. The richer monoidal infrastructure of
[`PFunctor.Chart`](../../PFunctor/Chart/Basic.lean) is intentionally not mirrored here yet —
extend on demand as downstream consumers need it.
-/

@[expose] public section

universe uI uJ uA uA₁ uA₂ uA₃ uA₄ uB uB₁ uB₂ uB₃ uB₄

namespace IPFunctor

variable {I : Type uI} {J : Type uJ}

/-- A **chart** between indexed polynomial functors `P Q : IPFunctor I J`: a forward map on
positions, a forward map on responses, and the source-index preservation law `src_eq`. -/
structure Chart (P : IPFunctor.{uI, uJ, uA₁, uB₁} I J)
                (Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J) where
  /-- Forward map on positions. -/
  toFunA : ∀ j, P.A j → Q.A j
  /-- Forward map on responses: a `P`-response at `a` pushes to a `Q`-response at the
  forward-mapped shape `toFunA j a`. -/
  toFunB : ∀ j a, P.B j a → Q.B j (toFunA j a)
  /-- Source-index preservation: the pushed-forward child source agrees with the original. -/
  src_eq : ∀ j a b, Q.src j (toFunA j a) (toFunB j a b) = P.src j a b

namespace Chart

/-- The identity chart. -/
protected def id (P : IPFunctor.{uI, uJ, uA, uB} I J) : Chart P P where
  toFunA _ := id
  toFunB _ _ := id
  src_eq _ _ _ := rfl

/-- Composition of charts in function-composition order: `c ∘c c'` applies `c'` first,
then `c`. -/
def comp {P : IPFunctor.{uI, uJ, uA₁, uB₁} I J}
    {Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J}
    {R : IPFunctor.{uI, uJ, uA₃, uB₃} I J}
    (c : Chart Q R) (c' : Chart P Q) : Chart P R where
  toFunA j := c.toFunA j ∘ c'.toFunA j
  toFunB j a := c.toFunB j (c'.toFunA j a) ∘ c'.toFunB j a
  src_eq j a b := by
    simp only [Function.comp_apply, c.src_eq, c'.src_eq]

@[inherit_doc] scoped infixl:75 " ∘c " => IPFunctor.Chart.comp

variable {P : IPFunctor.{uI, uJ, uA₁, uB₁} I J}
  {Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J}
  {R : IPFunctor.{uI, uJ, uA₃, uB₃} I J}
  {S : IPFunctor.{uI, uJ, uA₄, uB₄} I J}

@[simp]
theorem id_comp (f : Chart P Q) : (Chart.id Q) ∘c f = f := rfl

@[simp]
theorem comp_id (f : Chart P Q) : f ∘c (Chart.id P) = f := rfl

theorem comp_assoc (c : Chart R S) (c' : Chart Q R) (c'' : Chart P Q) :
    (c ∘c c') ∘c c'' = c ∘c (c' ∘c c'') := rfl

/-! ## Equivalence (isomorphism in the chart category) -/

/-- A structural equivalence in the chart category. -/
@[ext]
structure Equiv (P : IPFunctor.{uI, uJ, uA₁, uB₁} I J)
                (Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J) where
  /-- The forward chart. -/
  toChart : Chart P Q
  /-- The inverse chart. -/
  invChart : Chart Q P
  /-- Round-trip on `P`. -/
  left_inv : invChart ∘c toChart = Chart.id P
  /-- Round-trip on `Q`. -/
  right_inv : toChart ∘c invChart = Chart.id Q

@[inherit_doc] scoped infix:50 " ≃c " => IPFunctor.Chart.Equiv

namespace Equiv

/-- The identity equivalence on `P`, built from the identity chart in both directions. -/
@[refl]
def refl (P : IPFunctor.{uI, uJ, uA, uB} I J) : P ≃c P where
  toChart := Chart.id P
  invChart := Chart.id P
  left_inv := rfl
  right_inv := rfl

/-- The inverse of an equivalence, swapping the forward and inverse charts. -/
@[symm]
def symm (e : P ≃c Q) : Q ≃c P where
  toChart := e.invChart
  invChart := e.toChart
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Composition of equivalences, composing the forward and inverse charts respectively. -/
@[trans]
def trans (e₁ : P ≃c Q) (e₂ : Q ≃c R) : P ≃c R where
  toChart := e₂.toChart ∘c e₁.toChart
  invChart := e₁.invChart ∘c e₂.invChart
  left_inv := by
    rw [comp_assoc]
    rw (occs := [2]) [← comp_assoc]
    simp [e₁.left_inv, e₂.left_inv]
  right_inv := by
    rw [comp_assoc]
    rw (occs := [2]) [← comp_assoc]
    simp [e₁.right_inv, e₂.right_inv]

end Equiv

end Chart

end IPFunctor
