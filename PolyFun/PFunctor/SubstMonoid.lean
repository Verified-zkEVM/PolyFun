/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Lens.Basic
public import Mathlib.CategoryTheory.Category.Basic
import Batteries.Tactic.Lint

/-!
# Monoids for polynomial substitution

A `SubstMonoid` is a monoid object in the composition-monoidal category
`(Poly, ◃, y)`: a polynomial `p`, a unit lens `y ⇆ p`, and a multiplication
lens `p ◃ p ⇆ p` satisfying the two unit laws and associativity. Under
polynomial extension, every substitution monoid induces a monad on `Type`.
The fields use the names of Mathlib's `CategoryTheory.MonObj`: `one`, `mul`,
`one_mul`, `mul_one` and `mul_assoc`.

The laws are stated directly with the composition unitors and associator from
`PFunctor.Lens.Equiv`. This à-la-carte presentation avoids choosing between the
lens and chart category instances on `PFunctor` and matches the existing
`PFunctor.Comonoid` API.

`SubstMonoid.Hom` packages the polynomial monad morphisms: lenses preserving
the unit and multiplication. They form a category under ordinary lens
composition.

This file records the polynomial-level structure and its morphisms. Packaging
the induced monad on each extension, and constructing the free substitution
monoid, are separate layers.

## References

* Libkind and Spivak, *Pattern Runs on Matter: The Free Monad Monad as a
  Module over the Cofree Comonad Comonad*.
* Niu and Spivak, *Polynomial Functors: A Mathematical Theory of Interaction*,
  Chapter 7.
-/

@[expose] public section

universe uA uB

open CategoryTheory

namespace PFunctor

/-! ## Substitution monoids -/

set_option linter.checkUnivs false in
/-- A monoid object in the composition-monoidal category `(Poly, ◃, y)`.

The unit and multiplication are polynomial lenses. The laws use the explicit
unitors `yComp` and `compY` and associator `compAssoc`; no ambient monoidal
category instance is required. -/
-- The carrier's position and direction universes are independent; `checkUnivs`
-- sees only their joint contribution to the structure's resulting sort.
structure SubstMonoid where
  /-- The carrier polynomial. -/
  carrier : PFunctor.{uA, uB}
  /-- The unit `η : y ⇆ p`. Its universe instance agrees with the composition
  unit appearing beside `carrier ◃ carrier`. -/
  one : Lens y.{max uA uB, uB} carrier
  /-- The multiplication `μ : p ◃ p ⇆ p`. -/
  mul : Lens (carrier ◃ carrier) carrier
  /-- Left unitality: `μ ∘ (η ◃ id) ∘ λ⁻¹ = id`. -/
  protected one_mul : mul ∘ₗ (one ◃ₗ Lens.id carrier) ∘ₗ
      Lens.Equiv.yComp.invLens = Lens.id carrier
  /-- Right unitality: `μ ∘ (id ◃ η) ∘ ρ⁻¹ = id`. -/
  protected mul_one : mul ∘ₗ (Lens.id carrier ◃ₗ one) ∘ₗ
      Lens.Equiv.compY.invLens = Lens.id carrier
  /-- Associativity: multiplying the outer pair or the inner pair agrees. -/
  protected mul_assoc : mul ∘ₗ (mul ◃ₗ Lens.id carrier) =
      mul ∘ₗ (Lens.id carrier ◃ₗ mul) ∘ₗ Lens.Equiv.compAssoc.toLens

namespace SubstMonoid

@[deprecated (since := "2026-10-19")] alias mult := mul
@[deprecated (since := "2026-10-19")] alias unit := one
@[deprecated (since := "2026-10-19")] alias unit_left := SubstMonoid.one_mul
@[deprecated (since := "2026-10-19")] alias unit_right := SubstMonoid.mul_one
@[deprecated (since := "2026-10-19")] alias assoc := SubstMonoid.mul_assoc

/-! ## Morphisms -/

/-- A homomorphism of substitution monoids. It is a lens on carriers that
preserves the unit and multiplication. -/
structure Hom (M N : SubstMonoid.{uA, uB}) where
  /-- The underlying lens between carrier polynomials. -/
  toLens : Lens M.carrier N.carrier
  /-- Preservation of the unit. -/
  protected map_one : toLens ∘ₗ M.one = N.one
  /-- Preservation of multiplication. -/
  protected map_mul : toLens ∘ₗ M.mul =
    N.mul ∘ₗ (toLens ◃ₗ toLens)

@[deprecated (since := "2026-10-19")] alias Hom.map_mult := Hom.map_mul
@[deprecated (since := "2026-10-19")] alias Hom.map_unit := Hom.map_one

instance {M N : SubstMonoid.{uA, uB}} :
    Coe (Hom M N) (Lens M.carrier N.carrier) :=
  ⟨Hom.toLens⟩

@[ext]
theorem Hom.ext {M N : SubstMonoid.{uA, uB}} (f g : Hom M N)
    (h : f.toLens = g.toLens) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity substitution-monoid homomorphism. -/
def Hom.id (M : SubstMonoid.{uA, uB}) : Hom M M where
  toLens := Lens.id M.carrier
  map_one := rfl
  map_mul := by simp

/-- Composition of substitution-monoid homomorphisms, in diagrammatic order. -/
def Hom.comp {M N O : SubstMonoid.{uA, uB}} (f : Hom M N) (g : Hom N O) : Hom M O where
  toLens := g.toLens ∘ₗ f.toLens
  map_one := by
    rw [Lens.comp_assoc, f.map_one, g.map_one]
  map_mul := by
    calc
      (g.toLens ∘ₗ f.toLens) ∘ₗ M.mul =
          g.toLens ∘ₗ (f.toLens ∘ₗ M.mul) := rfl
      _ = g.toLens ∘ₗ (N.mul ∘ₗ (f.toLens ◃ₗ f.toLens)) := by
        rw [f.map_mul]
      _ = (g.toLens ∘ₗ N.mul) ∘ₗ (f.toLens ◃ₗ f.toLens) := rfl
      _ = (O.mul ∘ₗ (g.toLens ◃ₗ g.toLens)) ∘ₗ
          (f.toLens ◃ₗ f.toLens) := by
        rw [g.map_mul]
      _ = O.mul ∘ₗ ((g.toLens ◃ₗ g.toLens) ∘ₗ
          (f.toLens ◃ₗ f.toLens)) := rfl
      _ = O.mul ∘ₗ ((g.toLens ∘ₗ f.toLens) ◃ₗ
          (g.toLens ∘ₗ f.toLens)) := by
        rw [Lens.compMap_comp]

@[simp] theorem Hom.id_toLens (M : SubstMonoid.{uA, uB}) :
    (Hom.id M).toLens = Lens.id M.carrier := rfl

@[simp] theorem Hom.comp_toLens {M N O : SubstMonoid.{uA, uB}}
    (f : Hom M N) (g : Hom N O) :
    (f.comp g).toLens = g.toLens ∘ₗ f.toLens := rfl

@[simp] theorem Hom.id_comp {M N : SubstMonoid.{uA, uB}} (f : Hom M N) :
    (Hom.id M).comp f = f :=
  Hom.ext _ _ (Lens.comp_id f.toLens)

@[simp] theorem Hom.comp_id {M N : SubstMonoid.{uA, uB}} (f : Hom M N) :
    f.comp (Hom.id N) = f :=
  Hom.ext _ _ (Lens.id_comp f.toLens)

theorem Hom.comp_assoc {M N O P : SubstMonoid.{uA, uB}}
    (f : Hom M N) (g : Hom N O) (h : Hom O P) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  Hom.ext _ _ (Lens.comp_assoc h.toLens g.toLens f.toLens)

/-- The category of substitution monoids and their homomorphisms. -/
instance : Category SubstMonoid.{uA, uB} where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-- Morphisms of substitution monoids are determined by their underlying lenses. -/
@[ext]
theorem hom_ext {M N : SubstMonoid.{uA, uB}} {f g : M ⟶ N} (h : f.toLens = g.toLens) : f = g :=
  Hom.ext f g h

@[simp] theorem id_toLens (M : SubstMonoid.{uA, uB}) :
    (𝟙 M : M ⟶ M).toLens = Lens.id M.carrier := rfl

@[simp] theorem comp_toLens {M N O : SubstMonoid.{uA, uB}} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).toLens = g.toLens ∘ₗ f.toLens := rfl

end SubstMonoid

end PFunctor
