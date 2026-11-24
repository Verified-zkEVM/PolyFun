/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Coalgebra
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Coalgebras for a lawful endofunctor on types

Bundling the state type and its structure map gives a Mathlib coalgebra. Both representations
have the same morphisms, with the same identity maps and composition.
-/

public section

open CategoryTheory

universe u

namespace Coalg

variable {F : Type u → Type u} [_root_.Functor F] [LawfulFunctor F] {S T U : Type u}

/-- Bundle the state type and the structure map as a categorical coalgebra. -/
@[expose] def toEndofunctorCoalgebra (A : Coalg F S) : Endofunctor.Coalgebra (ofTypeFunctor F) :=
  ⟨S, ↾A.out⟩

/-- Read the structure map of a categorical coalgebra on its carrier. -/
@[expose] def ofEndofunctorCoalgebra (A : Endofunctor.Coalgebra (ofTypeFunctor F)) :
    Coalg F A.V := ⟨A.str.hom⟩

@[simp] theorem of_toEndofunctorCoalgebra (A : Coalg F S) :
    ofEndofunctorCoalgebra A.toEndofunctorCoalgebra = A := rfl

@[simp] theorem to_ofEndofunctorCoalgebra (A : Endofunctor.Coalgebra (ofTypeFunctor F)) :
    (ofEndofunctorCoalgebra A).toEndofunctorCoalgebra = A := rfl

/-- Coalgebra morphisms correspond by keeping their underlying function. -/
@[expose] def Hom.endofunctorEquiv (A : Coalg F S) (B : Coalg F T) :
    Hom A B ≃ (A.toEndofunctorCoalgebra ⟶ B.toEndofunctorCoalgebra) where
  toFun f := ⟨↾f.toFun, by ext x; exact congrFun f.comm x⟩
  invFun f := ⟨f.f.hom, by funext x; exact ConcreteCategory.congr_hom f.h x⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem Hom.endofunctorEquiv_apply {A : Coalg F S} {B : Coalg F T}
    (f : Hom A B) (x : S) : ((endofunctorEquiv A B f).f) x = f x := rfl

@[simp] theorem Hom.endofunctorEquiv_id (A : Coalg F S) :
    endofunctorEquiv A A (id A) = 𝟙 A.toEndofunctorCoalgebra := rfl

@[simp] theorem Hom.endofunctorEquiv_comp {A : Coalg F S} {B : Coalg F T} {C : Coalg F U}
    (g : Hom B C) (f : Hom A B) :
    endofunctorEquiv A C (g.comp f) = endofunctorEquiv A B f ≫ endofunctorEquiv B C g := rfl

end Coalg
