/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Category.Monoidal

/-!
# Ordinary-import canaries for the equivalence groupoid

The groupoid laws of lens equivalences that need no inverse law, and the round trips between lens
equivalences and isomorphisms of the lens categories, are definitional. These examples check by
`rfl`, through ordinary imports and at independent universes, that a consumer sees them.
-/

@[expose] public section

universe uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ u v

namespace PolyFunTest.ModuleAPI.Lens.EquivGroupoid

open CategoryTheory _root_.PFunctor

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {S : PFunctor.{uA₄, uB₄}}

example (e : P ≃ₗ Q) : e.symm.symm = e := rfl

example (e : P ≃ₗ Q) : e.trans (Lens.Equiv.refl Q) = e := rfl

example (e₁ : P ≃ₗ Q) (e₂ : Q ≃ₗ R) (e₃ : R ≃ₗ S) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) := rfl

example (e : P ≃c Q) : (Chart.Equiv.refl P).trans e = e := rfl

example {X Y : LensCat.{uA₁, uB₁}} (i : X ≅ Y) : LensCat.Iso.mk (LensCat.Iso.toLensEquiv i) = i :=
  rfl

example {X Y : TensorCat.{uA₁, uB₁}} (e : X.toPFunctor ≃ₗ Y.toPFunctor) :
    TensorCat.Iso.toLensEquiv (TensorCat.Iso.mk e) = e := rfl

example {X Y : CompCat.{u, v}} (e : X.toPFunctor ≃ₗ Y.toPFunctor) :
    (CompCat.lensEquivEquivIso e).hom = e.toLens := rfl

end PolyFunTest.ModuleAPI.Lens.EquivGroupoid
