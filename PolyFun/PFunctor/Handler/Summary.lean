/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Handler.CountMat
public import PolyFun.PFunctor.Lens.DillerNahm
public import Mathlib.CategoryTheory.Opposites

/-!
# The summary functor of handlers certified by count matrices

The category `CountCertifiedCat ω` has as objects interfaces `P` with a vector charge
`c : P.A → ι → ω` over a finite type of resources `ι`, and as morphisms `X ⟶ Y` the handlers
implementing `X.P` by programs over `Y.P` certified by a one-shape Diller–Nahm morphism
(`Handler.CountCertified`). Identities are the identity handlers certified by the counit, and
composition is `Handler.CountCertified.comp`. Its laws are the laws of handler composition
(`Handler.id_comp`, `Handler.comp_id`, `Handler.comp_assoc`) together with those of co-Kleisli
composition (`Lens.bangComp_bangCounit`, `Lens.bangCounit_bangComp`, `Lens.bangComp_assoc`).

The summary functor `CountCertifiedCat.summary` forgets the implementation and keeps the
certificate: it sends `X` to its resources `X.ι` and a certified handler to its one-shape
Diller–Nahm morphism, in the opposite of the one-shape Diller–Nahm category `OneShapeDN`, since
the morphism points from the resources of the implementing interface to those of the implemented
one. The summary of a morphism bounds the use of every program run through its handler
(`CountCertifiedCat.isChargeBound_liftM_summary`, from `Handler.isChargeBound_liftM_demand`), and
the demand matrix of the summary of a composite is the product of the demand matrices
(`CountCertifiedCat.demand_summary_map_comp`, from `Lens.countMat_bangComp`).

The one-shape Diller–Nahm category is the polynomial presentation of the Diller–Nahm variant of
the Dialectica category of Moss and von Glehn (*Dialectica models of type theory*, LICS 2018, §8).
-/

@[expose] public section

universe uA uA₂ uB uB₂ u u' w

open CategoryTheory Opposite

namespace PFunctor

namespace Handler

namespace CountCertified

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {ι : Type u} {ι' : Type u'}
  [Fintype ι] [DecidableEq ι'] {ω : Type w} [CommSemiring ω] [PartialOrder ω] [IsOrderedRing ω]
  {c : P.A → ι → ω} {e : Q.A → ι' → ω}

omit [IsOrderedRing ω] in
/-- Two certified handlers are equal when their handlers and their lenses are equal. -/
theorem ext {D D' : CountCertified P Q c e} (hh : D.handler = D'.handler)
    (hl : D.lens = D'.lens) : D = D' := by
  cases D
  cases D'
  cases hh
  cases hl
  rfl

end CountCertified

end Handler

set_option linter.checkUnivs false in
/-- An object of the category of handlers certified by count matrices: an interface `P` with a
vector charge `c` over a finite type of resources `ι`. -/
structure CountCertifiedCat (ω : Type w) where
  /-- An interface with a vector charge as an object. -/
  of ::
  /-- The interface. -/
  P : PFunctor.{uA, uB}
  /-- The resources. -/
  ι : Type u
  /-- The resources are finite. -/
  [fintype : Fintype ι]
  /-- The resources have decidable equality. -/
  [decEq : DecidableEq ι]
  /-- The charge of each call, a vector over the resources. -/
  c : P.A → ι → ω

namespace CountCertifiedCat

attribute [instance] fintype decEq

variable (ω : Type w) [CommSemiring ω] [PartialOrder ω] [IsOrderedRing ω]

/-- The category of handlers certified by count matrices: a morphism `X ⟶ Y` is a handler
implementing `X.P` by programs over `Y.P`, certified by a one-shape Diller–Nahm morphism from the
resources of `Y` to those of `X`. -/
instance instCategory : Category (CountCertifiedCat.{uA, uB, u, w} ω) where
  Hom X Y := Handler.CountCertified X.P Y.P X.c Y.c
  id X := Handler.CountCertified.id X.P X.c
  comp f g := g.comp f
  id_comp _ := Handler.CountCertified.ext (Handler.comp_id _) (Lens.bangComp_bangCounit _)
  comp_id _ := Handler.CountCertified.ext (Handler.id_comp _) (Lens.bangCounit_bangComp _)
  assoc _ _ _ :=
    Handler.CountCertified.ext (Handler.comp_assoc _ _ _).symm (Lens.bangComp_assoc _ _ _)

/-- The summary functor: an interface with a vector charge goes to its resources, and a certified
handler to its one-shape Diller–Nahm morphism, in the opposite category. -/
def summary : CountCertifiedCat.{uA, uB, u, w} ω ⥤ OneShapeDN.{u}ᵒᵖ where
  obj X := op (OneShapeDN.of X.ι)
  map f := Quiver.Hom.op f.lens
  map_id _ := rfl
  map_comp _ _ := rfl

variable {ω}

/-- The summary of a certified handler is its lens. -/
@[simp]
theorem summary_map_unop {X Y : CountCertifiedCat.{uA, uB, u, w} ω} (f : X ⟶ Y) :
    ((summary ω).map f).unop = f.lens :=
  rfl

/-- **Use bounds through a summary.** A program with use vector `u` runs through the handler of
`f` with use vector `u` times the demand matrix of the summary of `f`. -/
theorem isChargeBound_liftM_summary {X Y : CountCertifiedCat.{uA, uB, u, w} ω} (f : X ⟶ Y)
    {α : Type uB} {x : FreeM X.P α} {u : X.ι → ω} (hx : x.IsChargeBound X.c u) :
    (x.liftM f.handler).IsChargeBound Y.c
      (Matrix.vecMul u (Matrix.of (Lens.demand ω ((summary ω).map f).unop))) :=
  Handler.CountCertified.isChargeBound_liftM f hx

/-- **The summary is multiplicative on demands.** The demand matrix of the summary of a composite
is the product of the demand matrices of the summaries. -/
theorem demand_summary_map_comp {X Y Z : CountCertifiedCat.{uA, uB, u, w} ω} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    Matrix.of (Lens.demand (ι := X.ι) (ι' := Z.ι) ω ((summary ω).map (f ≫ g)).unop) =
      Matrix.of (Lens.demand (ι := X.ι) (ι' := Y.ι) ω ((summary ω).map f).unop) *
        Matrix.of (Lens.demand (ι := Y.ι) (ι' := Z.ι) ω ((summary ω).map g).unop) :=
  Lens.demand_bangComp_eq_mul f.lens g.lens

/-- **Use bounds through a composite.** A program with use vector `u` runs through the handler of
`f ≫ g` with use vector `u` times the product of the demand matrices of the summaries of `f` and
`g`. -/
theorem isChargeBound_liftM_summary_comp {X Y Z : CountCertifiedCat.{uA, uB, u, w} ω}
    (f : X ⟶ Y) (g : Y ⟶ Z) {α : Type uB} {x : FreeM X.P α} {u : X.ι → ω}
    (hx : x.IsChargeBound X.c u) :
    (x.liftM (f ≫ g).handler).IsChargeBound Z.c
      (Matrix.vecMul u (Matrix.of (Lens.demand (ι := X.ι) (ι' := Y.ι) ω ((summary ω).map f).unop) *
        Matrix.of (Lens.demand (ι := Y.ι) (ι' := Z.ι) ω ((summary ω).map g).unop))) :=
  Handler.CountCertified.isChargeBound_liftM_comp g f hx

end CountCertifiedCat

end PFunctor
