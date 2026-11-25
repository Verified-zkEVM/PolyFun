/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Lens.BangLE
public import Mathlib.CategoryTheory.Monad.Kleisli

/-!
# The one-shape Diller–Nahm category

A lens `bang P ⇆ Q` is a morphism of the Diller–Nahm category, the co-Kleisli category of the
multiset exponential (`Lens.bangComp`). Composition is the multiset bind of demands, and the
counit is its identity (`Lens.bangComp_bangCounit`, `Lens.bangCounit_bangComp`,
`Lens.bangComp_assoc`); these are the laws of `CategoryTheory.Cokleisli LensCat.bangComonad`,
stated for lenses between polynomials of independent universes.

The one-shape Diller–Nahm category (`OneShapeDN`) is its full subcategory on the polynomials
`y^ι` with one position: a morphism `ι ⟶ ι'` is a lens `bang (y^ι) ⇆ y^ι'`, which sends each
`i' : ι'` to a finite multiset over `ι`, the units of `ι` that one unit of `i'` demands. At finite
`ι` it is the count matrix of `Lens.countMat` (`Lens.ofCountMat`). The inclusion into the
co-Kleisli category is `OneShapeDN.toCokleisli`.

This is the Diller–Nahm (multiset) variant of the Dialectica category in the polynomial
presentation of Moss and von Glehn (*Dialectica models of type theory*, LICS 2018, §8).
-/

@[expose] public section

universe uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ u

open CategoryTheory

namespace PFunctor

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {S : PFunctor.{uA₄, uB₄}}

/-- The forward map of a co-Kleisli composite is the composite of the forward maps. -/
@[simp]
theorem bangComp_toFunA (g : Lens (bang Q) R) (f : Lens (bang P) Q) (a : P.A) :
    (bangComp g f).toFunA a = g.toFunA (f.toFunA a) :=
  rfl

/-- The counit is a left identity of co-Kleisli composition. -/
@[simp]
theorem bangComp_bangCounit (f : Lens (bang P) Q) : bangComp (bangCounit Q) f = f :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Multiset.singleton_bind _ _

/-- The counit is a right identity of co-Kleisli composition. -/
@[simp]
theorem bangCounit_bangComp (g : Lens (bang P) Q) : bangComp g (bangCounit P) = g :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ =>
    (Multiset.bind_singleton _ id).trans (Multiset.map_id _)

/-- Co-Kleisli composition is associative: binding demands is associative. -/
theorem bangComp_assoc (h : Lens (bang R) S) (g : Lens (bang Q) R) (f : Lens (bang P) Q) :
    bangComp (bangComp h g) f = bangComp h (bangComp g f) :=
  Lens.ext _ _ (fun _ => rfl) fun _ => funext fun _ => Multiset.bind_assoc

end Lens

/-! ## The one-shape Diller–Nahm category -/

/-- An object of the one-shape Diller–Nahm category: a type of resources `ι`, standing for the
polynomial `y^ι`. -/
structure OneShapeDN : Type (u + 1) where
  /-- Regard a type of resources as an object of the one-shape Diller–Nahm category. -/
  of ::
  /-- The resources: the directions of the one-position polynomial. -/
  ι : Type u

namespace OneShapeDN

/-- The one-shape Diller–Nahm category: a morphism `X ⟶ Y` is a lens `bang (y^X.ι) ⇆ y^Y.ι`,
composed in the co-Kleisli category of the exponential, with the counit as identity. -/
instance instCategory : Category OneShapeDN.{u} where
  Hom X Y := Lens (bang (y^X.ι : PFunctor.{0, u})) (y^Y.ι : PFunctor.{0, u})
  id _ := Lens.bangCounit _
  comp f g := Lens.bangComp g f
  id_comp f := Lens.bangCounit_bangComp f
  comp_id f := Lens.bangComp_bangCounit f
  assoc f g h := (Lens.bangComp_assoc h g f).symm

/-- The identity of the one-shape Diller–Nahm category is the counit. -/
@[simp]
theorem id_eq (X : OneShapeDN.{u}) : 𝟙 X = Lens.bangCounit (y^X.ι : PFunctor.{0, u}) :=
  rfl

/-- Composition in the one-shape Diller–Nahm category is co-Kleisli composition. -/
@[simp]
theorem comp_eq {X Y Z : OneShapeDN.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = Lens.bangComp (P := y^X.ι) (Q := y^Y.ι) (R := y^Z.ι) g f :=
  rfl

/-- The inclusion of the one-shape Diller–Nahm category into the co-Kleisli category of the
exponential. -/
def toCokleisli : OneShapeDN.{u} ⥤ Cokleisli LensCat.bangComonad.{0, u} where
  obj X := Cokleisli.mk _ (LensCat.of (y^X.ι))
  map f := ⟨f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end OneShapeDN

end PFunctor
