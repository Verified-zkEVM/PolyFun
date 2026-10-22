/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Category.Monoidal
public import PolyFun.PFunctor.Comonoid

/-!
# Equivalences of polynomials as a groupoid

These examples chain `≃ₗ`, `≃c` and `≃ₚ` in `calc` at independent universes, simplify through
their `simps` projections, use the uniqueness of lenses out of `0` and into `1`, convert between
lens equivalences and isomorphisms of the lens categories, and apply the `ext` lemmas for
morphisms of `LensCat` and `Cat♯`.
-/

@[expose] public section

universe uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PolyFunTest.PFunctor.Lens.EquivGroupoid

open CategoryTheory _root_.PFunctor

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-! ## `calc` and `simp` -/

example (e : P ≃ₗ Q) (f : Q ≃ₗ R) : P ≃ₗ R :=
  calc P ≃ₗ Q := e
    _ ≃ₗ R := f

example (e : P ≃c Q) (f : Q ≃c R) : P ≃c R :=
  calc P ≃c Q := e
    _ ≃c R := f

example (e : P ≃ₚ Q) (f : Q ≃ₚ R) : P ≃ₚ R :=
  calc P ≃ₚ Q := e
    _ ≃ₚ R := f

example (e : P ≃ₗ Q) (f : Q ≃ₗ R) :
    (e.trans f).symm.toLens = e.invLens ∘ₗ f.invLens := by
  simp

example (e : P ≃ₗ Q) : e.symm.trans e = Lens.Equiv.refl Q := by simp

example (e : P ≃c Q) : e.trans e.symm = Chart.Equiv.refl P := by simp

example (e : P ≃ₚ Q) (a : Q.A) : e.symm.equivA a = e.equivA.symm a := by simp

example (e e' : P ≃ₗ Q) (h : e.toLens = e'.toLens) : e = e' :=
  Lens.Equiv.toLens_injective h

/-! ## Initial and terminal lenses -/

example (l l' : Lens (0 : PFunctor.{uA₁, uB₁}) Q) : l = l' := Subsingleton.elim l l'

example (l : Lens P (1 : PFunctor.{uA₂, uB₂})) : l = Lens.terminal := Unique.eq_default l

/-! ## Isomorphisms of the lens categories -/

example {X Y : TensorCat.{0, 0}} (e : X.toPFunctor ≃ₗ Y.toPFunctor) :
    TensorCat.Iso.toLensEquiv (TensorCat.Iso.mk e) = e := rfl

example {X Y : CompCat.{0, 0}} (i : X ≅ Y) : CompCat.Iso.mk (CompCat.Iso.toLensEquiv i) = i :=
  rfl

example {X Y : LensCat.{0, 0}} (i : X ≅ Y) : (LensCat.lensEquivEquivIso.symm i).toLens = i.hom :=
  rfl

/-! ## Extensionality for morphisms -/

example {X Y : LensCat.{0, 0}} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by
  ext <;> rfl

example {C D : Comonoid.{0, 0}} (f : C ⟶ D) : 𝟙 C ≫ f = f := by
  ext : 1
  simp

end PolyFunTest.PFunctor.Lens.EquivGroupoid
