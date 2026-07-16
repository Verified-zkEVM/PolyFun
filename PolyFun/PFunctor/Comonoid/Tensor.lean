/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Comonoid
public import PolyFun.PFunctor.Lens.Duoidal
public import Mathlib.CategoryTheory.Iso

/-!
# Tensor products of polynomial comonoids

The duoidal interchange lens equips the tensor product of two comonoids in
`(Poly, ◃, y)` with a comonoid structure.  Its objects and outgoing arrows are
pairs, its counit combines the two component counits, and its comultiplication
composes each component independently.  This is the concrete construction in
Spivak–Niu, Proposition 8.77 in the current edition (Proposition 8.79 in the
earlier-edition notes).

The two input comonoids retain independent position and direction universes.
The counit uses `Lens.tensorUnitMap` to compare their independently instantiated
copies of the composition unit with the unit at the componentwise maximum.
Tensor products of retrofunctors are defined componentwise.

The common composition unit `X` is packaged as `Comonoid.unit`.  The tensor
left/right unitors and associator lift to `CategoryTheory.Iso`s of comonoids;
their forward and inverse retrofunctors use exactly the corresponding
polynomial-lens equivalences.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PFunctor
namespace Comonoid

/-! ## The composition-unit comonoid -/

/-- The composition unit `X` as a composition comonoid.  Its counit and
comultiplication are the canonical maps between universe-instantiated copies
of `X`; all of its arrows are the unique unit arrow. -/
def unit : Comonoid.{uA, uB} where
  carrier := X
  counit := Lens.unitComparison
  comult := Lens.compUnitMap ∘ₗ
    (Lens.unitComparison : Lens X.{uA, uB} X.{max uA uB, uB})
  counit_left := Lens.compUnitMap_counit_left
  counit_right := Lens.compUnitMap_counit_right
  coassoc := Lens.compUnitMap_coassoc.{uA, uB}

@[simp] theorem unit_carrier : (unit.{uA, uB}).carrier = X := rfl

/-- The counit of the composition-unit comonoid is the canonical comparison
between its two universe instantiations. -/
theorem unit_counit : (unit.{uA, uB}).counit = Lens.unitComparison := rfl

/-- The comultiplication of the composition-unit comonoid is the canonical
map `X ⇆ X ◃ X`, after comparing its source universe instantiation. -/
theorem unit_comult :
    (unit.{uA, uB}).comult =
      Lens.compUnitMap ∘ₗ
        (Lens.unitComparison : Lens X.{uA, uB} X.{max uA uB, uB}) := rfl

/-! ## Tensor product -/

/-- The counit of the tensor product of two composition comonoids. -/
def tensorCounit (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Lens (C.carrier ⊗ D.carrier)
      X.{max (max uA₁ uA₂) (max uB₁ uB₂), max uB₁ uB₂} :=
  Lens.tensorUnitMap ∘ₗ (C.counit ⊗ₗ D.counit)

/-- The comultiplication of the tensor product of two composition comonoids. -/
def tensorComult (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Lens (C.carrier ⊗ D.carrier)
      ((C.carrier ⊗ D.carrier) ◃ (C.carrier ⊗ D.carrier)) :=
  Lens.duoidalLens C.carrier C.carrier D.carrier D.carrier ∘ₗ
    (C.comult ⊗ₗ D.comult)

private theorem tensorCounit_left_factor
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Lens.Equiv.XComp.toLens ∘ₗ
        (tensorCounit C D ◃ₗ Lens.id (C.carrier ⊗ D.carrier)) ∘ₗ
        tensorComult C D =
      ((Lens.Equiv.XComp.toLens ∘ₗ
          (C.counit ◃ₗ Lens.id C.carrier) ∘ₗ C.comult) ⊗ₗ
        (Lens.Equiv.XComp.toLens ∘ₗ
          (D.counit ◃ₗ Lens.id D.carrier) ∘ₗ D.comult)) := by
  rfl

private theorem tensorCounit_right_factor
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Lens.Equiv.compX.toLens ∘ₗ
        (Lens.id (C.carrier ⊗ D.carrier) ◃ₗ tensorCounit C D) ∘ₗ
        tensorComult C D =
      ((Lens.Equiv.compX.toLens ∘ₗ
          (Lens.id C.carrier ◃ₗ C.counit) ∘ₗ C.comult) ⊗ₗ
        (Lens.Equiv.compX.toLens ∘ₗ
          (Lens.id D.carrier ◃ₗ D.counit) ∘ₗ D.comult)) := by
  rfl

private theorem tensorComult_assoc_left_factor
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Lens.Equiv.compAssoc.toLens ∘ₗ
        (tensorComult C D ◃ₗ Lens.id (C.carrier ⊗ D.carrier)) ∘ₗ
        tensorComult C D =
      (Lens.id (C.carrier ⊗ D.carrier) ◃ₗ
          Lens.duoidalLens C.carrier C.carrier D.carrier D.carrier) ∘ₗ
        Lens.duoidalLens C.carrier (C.carrier ◃ C.carrier)
          D.carrier (D.carrier ◃ D.carrier) ∘ₗ
        ((Lens.Equiv.compAssoc.toLens ∘ₗ
            (C.comult ◃ₗ Lens.id C.carrier) ∘ₗ C.comult) ⊗ₗ
          (Lens.Equiv.compAssoc.toLens ∘ₗ
            (D.comult ◃ₗ Lens.id D.carrier) ∘ₗ D.comult)) := by
  rfl

private theorem tensorComult_assoc_right_factor
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (Lens.id (C.carrier ⊗ D.carrier) ◃ₗ tensorComult C D) ∘ₗ
        tensorComult C D =
      (Lens.id (C.carrier ⊗ D.carrier) ◃ₗ
          Lens.duoidalLens C.carrier C.carrier D.carrier D.carrier) ∘ₗ
        Lens.duoidalLens C.carrier (C.carrier ◃ C.carrier)
          D.carrier (D.carrier ◃ D.carrier) ∘ₗ
        (((Lens.id C.carrier ◃ₗ C.comult) ∘ₗ C.comult) ⊗ₗ
          ((Lens.id D.carrier ◃ₗ D.comult) ∘ₗ D.comult)) := by
  rfl

/-- The tensor product of two comonoids in `(Poly, ◃, y)`.  The construction
is heterogeneous in both input universe pairs and lands at their componentwise
maximum. -/
def tensor (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Comonoid.{max uA₁ uA₂, max uB₁ uB₂} where
  carrier := C.carrier ⊗ D.carrier
  counit := tensorCounit C D
  comult := tensorComult C D
  counit_left := by
    rw [tensorCounit_left_factor, C.counit_left, D.counit_left,
      Lens.tensorMap_id]
  counit_right := by
    rw [tensorCounit_right_factor, C.counit_right, D.counit_right,
      Lens.tensorMap_id]
  coassoc := by
    rw [tensorComult_assoc_left_factor, C.coassoc, D.coassoc]
    exact (tensorComult_assoc_right_factor C D).symm

@[simp] theorem tensor_carrier
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (tensor C D).carrier = C.carrier ⊗ D.carrier := rfl

/-- The tensor-product counit is the componentwise counit followed by the
canonical comparison of tensor units. -/
theorem tensor_counit
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (tensor C D).counit = tensorCounit C D := rfl

/-- The tensor-product comultiplication is componentwise comultiplication
followed by duoidal interchange. -/
theorem tensor_comult
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (tensor C D).comult = tensorComult C D := rfl

/-! ## Tensor coherence isomorphisms -/

/-- The left tensor unitor, lifted from polynomial lenses to composition
comonoids.  Both directions preserve identities and composition. -/
def tensorUnitLeftIso (C : Comonoid.{uA, uB}) :
    CategoryTheory.Iso (tensor (unit.{uA, uB}) C) C where
  hom := {
    toLens := (Lens.Equiv.xTensor (P := C.carrier)).toLens
    map_counit := by rfl
    map_comult := by rfl }
  inv := {
    toLens := (Lens.Equiv.xTensor (P := C.carrier)).invLens
    map_counit := by rfl
    map_comult := by rfl }
  hom_inv_id := by rfl
  inv_hom_id := by rfl

@[simp] theorem tensorUnitLeftIso_hom_toLens (C : Comonoid.{uA, uB}) :
    (tensorUnitLeftIso C).hom.toLens =
      (Lens.Equiv.xTensor (P := C.carrier)).toLens := rfl

@[simp] theorem tensorUnitLeftIso_inv_toLens (C : Comonoid.{uA, uB}) :
    (tensorUnitLeftIso C).inv.toLens =
      (Lens.Equiv.xTensor (P := C.carrier)).invLens := rfl

/-- The right tensor unitor, lifted from polynomial lenses to composition
comonoids.  Both directions preserve identities and composition. -/
def tensorUnitRightIso (C : Comonoid.{uA, uB}) :
    CategoryTheory.Iso (tensor C (unit.{uA, uB})) C where
  hom := {
    toLens := (Lens.Equiv.tensorX (P := C.carrier)).toLens
    map_counit := by rfl
    map_comult := by rfl }
  inv := {
    toLens := (Lens.Equiv.tensorX (P := C.carrier)).invLens
    map_counit := by rfl
    map_comult := by rfl }
  hom_inv_id := by rfl
  inv_hom_id := by rfl

@[simp] theorem tensorUnitRightIso_hom_toLens (C : Comonoid.{uA, uB}) :
    (tensorUnitRightIso C).hom.toLens =
      (Lens.Equiv.tensorX (P := C.carrier)).toLens := rfl

@[simp] theorem tensorUnitRightIso_inv_toLens (C : Comonoid.{uA, uB}) :
    (tensorUnitRightIso C).inv.toLens =
      (Lens.Equiv.tensorX (P := C.carrier)).invLens := rfl

/-- The tensor associator, lifted from polynomial lenses to composition
comonoids.  The three input universe pairs remain independent. -/
def tensorAssocIso
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    CategoryTheory.Iso (tensor (tensor C D) E)
      (tensor C (tensor D E)) where
  hom := {
    toLens := (Lens.Equiv.tensorAssoc
      (P := C.carrier) (Q := D.carrier) (R := E.carrier)).toLens
    map_counit := by rfl
    map_comult := by rfl }
  inv := {
    toLens := (Lens.Equiv.tensorAssoc
      (P := C.carrier) (Q := D.carrier) (R := E.carrier)).invLens
    map_counit := by rfl
    map_comult := by rfl }
  hom_inv_id := by rfl
  inv_hom_id := by rfl

@[simp] theorem tensorAssocIso_hom_toLens
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    (tensorAssocIso C D E).hom.toLens =
      (Lens.Equiv.tensorAssoc
        (P := C.carrier) (Q := D.carrier) (R := E.carrier)).toLens := rfl

@[simp] theorem tensorAssocIso_inv_toLens
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    (tensorAssocIso C D E).inv.toLens =
      (Lens.Equiv.tensorAssoc
        (P := C.carrier) (Q := D.carrier) (R := E.carrier)).invLens := rfl

/-! ## Tensor products of retrofunctors -/

namespace Hom

/-- The componentwise tensor product of two retrofunctors. -/
def tensor
    {C₁ D₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ : Comonoid.{uA₂, uB₂}}
    (f : Hom C₁ D₁) (g : Hom C₂ D₂) :
    Hom (Comonoid.tensor C₁ C₂) (Comonoid.tensor D₁ D₂) where
  toLens := f.toLens ⊗ₗ g.toLens
  map_counit := by
    change Lens.tensorUnitMap ∘ₗ
        ((D₁.counit ⊗ₗ D₂.counit) ∘ₗ (f.toLens ⊗ₗ g.toLens)) = _
    rw [← Lens.tensorMap_comp, f.map_counit, g.map_counit]
    rfl
  map_comult := by
    change Lens.duoidalLens D₁.carrier D₁.carrier D₂.carrier D₂.carrier ∘ₗ
        ((D₁.comult ⊗ₗ D₂.comult) ∘ₗ (f.toLens ⊗ₗ g.toLens)) = _
    rw [← Lens.tensorMap_comp, f.map_comult, g.map_comult]
    rfl

@[simp] theorem tensor_toLens
    {C₁ D₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ : Comonoid.{uA₂, uB₂}}
    (f : Hom C₁ D₁) (g : Hom C₂ D₂) :
    (tensor f g).toLens = f.toLens ⊗ₗ g.toLens := rfl

@[simp] theorem tensor_id
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    tensor (Hom.id C) (Hom.id D) = Hom.id (Comonoid.tensor C D) := by
  apply Hom.ext
  exact Lens.tensorMap_id

theorem tensor_comp
    {C₁ D₁ E₁ : Comonoid.{uA₁, uB₁}}
    {C₂ D₂ E₂ : Comonoid.{uA₂, uB₂}}
    (f₁ : Hom C₁ D₁) (g₁ : Hom D₁ E₁)
    (f₂ : Hom C₂ D₂) (g₂ : Hom D₂ E₂) :
    tensor (f₁.comp g₁) (f₂.comp g₂) =
      (tensor f₁ f₂).comp (tensor g₁ g₂) := by
  apply Hom.ext
  exact Lens.tensorMap_comp f₁.toLens f₂.toLens g₁.toLens g₂.toLens

end Hom
end Comonoid
end PFunctor
