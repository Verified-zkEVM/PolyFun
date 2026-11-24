/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Basic.FunLike.Basic

/-!
# F-coalgebras

An `F`-coalgebra is a type `S` together with a
structure map `out : S → F S`.

It has the arrow shape dual to an `F`-algebra `F S → S`: a coalgebra
observes one layer of structure from a state. No monad or comonad laws are imposed.

## Main definitions

* `Coalg F S`: structure with field `out : S → F S`.
* `Coalg.Hom A B`: a function `S₁ → S₂` that commutes with the structure
  maps (`Functor.map f ∘ out = out ∘ f`). Equipped with coercion, `id`, `comp`.

## Relationship to Mathlib and Poly

`CategoryTheory.Endofunctor.Coalgebra` in Mathlib defines coalgebras for
endofunctors on an arbitrary category. The module `PolyFun.Control.Coalgebra.Category`
relates its objects and morphisms to the ones here for lawful endofunctors on `Type u`.
The `Type`-level definition suffices for the polynomial-functor framework:
a `PFunctor.DynSystem S p` is exactly a `p.Obj`-coalgebra on `S` via
`PFunctor.DynSystem.out`, in the sense of the Poly book (Spivak, 2022).
-/

@[expose] public section

universe u v

/-- An `F`-coalgebra on `S` is a structure map `out : S → F S`.

Named `Coalg` to avoid collision with `Mathlib.RingTheory.Coalgebra`.
No `[Functor F]` constraint is imposed on the structure itself, and the source and
target universes may differ. Categorical endofunctor coalgebras specialize to
the same-universe case with a lawful functor. -/
structure Coalg (F : Type u → Type v) (S : Type u) where
  /-- The structure map of the coalgebra, unfolding a state `S` into one layer of `F`. -/
  out : S → F S

export Coalg (out)

/-! ## Coalg morphisms -/

/-- A coalgebra morphism between `F`-coalgebras on `S₁` and `S₂` is a function
that commutes with the structure maps:
```
      out
  S₁ -----> F S₁
  |          |
  f        F f
  |          |
  v          v
  S₂ -----> F S₂
      out
```
In the interaction framework, coalgebra morphisms between processes correspond
to forward simulations that preserve step structure. -/
structure Coalg.Hom {F : Type u → Type v} [Functor F] {S₁ S₂ : Type u}
    (A : Coalg F S₁) (B : Coalg F S₂) where
  /-- The underlying function between state spaces. -/
  toFun : S₁ → S₂
  /-- The commutativity condition: `F.map f ∘ out = out ∘ f`. -/
  comm : Functor.map toFun ∘ A.out = B.out ∘ toFun

namespace Coalg.Hom

variable {F : Type u → Type v} [Functor F]
variable {S₁ S₂ S₃ : Type u} {A : Coalg F S₁} {B : Coalg F S₂} {C : Coalg F S₃}

instance : FunLike (Coalg.Hom A B) S₁ S₂ where
  coe := Coalg.Hom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext]
theorem ext {f g : Coalg.Hom A B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

variable [LawfulFunctor F]

/-- The identity coalgebra morphism. -/
def id (A : Coalg F S₁) : Coalg.Hom A A where
  toFun := _root_.id
  comm := by funext x; simp [Function.comp, id_map]

/-- Composition of coalgebra morphisms. -/
def comp (g : Coalg.Hom B C) (f : Coalg.Hom A B) : Coalg.Hom A C where
  toFun := g.toFun ∘ f.toFun
  comm := by
    funext x
    have hf := congrFun f.comm x
    have hg := congrFun g.comm (f.toFun x)
    simp only [Function.comp_apply] at hf hg ⊢
    rw [comp_map, hf, hg]

@[simp]
theorem id_apply (x : S₁) : (Coalg.Hom.id A) x = x := rfl

@[simp]
theorem comp_apply (g : Coalg.Hom B C) (f : Coalg.Hom A B) (x : S₁) :
    (Coalg.Hom.comp g f) x = g (f x) := rfl

/-! Coalgebra morphisms form a category, on the nose. These mirror `MonadHom.comp`'s
laws in `PolyFun/Control/Monad/Hom.lean`: both hom types compose their carrier maps
pointwise and package the corresponding preservation laws, so their composition APIs
should agree. -/

@[simp]
theorem comp_id (f : Coalg.Hom A B) : f.comp (Coalg.Hom.id A) = f := rfl

@[simp]
theorem id_comp (f : Coalg.Hom A B) : (Coalg.Hom.id B).comp f = f := rfl

theorem comp_assoc {S₄ : Type u} {D : Coalg F S₄}
    (h : Coalg.Hom C D) (g : Coalg.Hom B C) (f : Coalg.Hom A B) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

end Coalg.Hom
