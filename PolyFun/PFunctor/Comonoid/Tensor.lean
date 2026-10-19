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
Niu–Spivak, Proposition 8.79.

The two input comonoids retain independent position and direction universes.
The counit uses `Lens.tensorUnitMap` to compare their independently instantiated
copies of the composition unit with the unit at the componentwise maximum.
Tensor products of retrofunctors are defined componentwise.

The common composition unit `y` is packaged as `Comonoid.trivial`.  The tensor
left/right unitors and associator lift to `CategoryTheory.Iso`s of comonoids;
their forward and inverse retrofunctors use exactly the corresponding
polynomial-lens equivalences.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PFunctor
namespace Comonoid

/-! ## The composition-unit comonoid -/

/-- The composition unit `y` as a composition comonoid.  Its counit and
comultiplication are the canonical maps between universe-instantiated copies
of `y`; all of its arrows are the unique unit arrow. -/
@[reducible]
def trivial : Comonoid.{uA, uB} where
  carrier := y
  counit := Lens.unitComparison
  comul := Lens.compUnitMap ∘ₗ
    (Lens.unitComparison : Lens y.{uA, uB} y.{max uA uB, uB})
  counit_left := Lens.compUnitMap_counit_left
  counit_right := Lens.compUnitMap_counit_right
  coassoc := Lens.compUnitMap_coassoc.{uA, uB}

@[deprecated (since := "2026-10-19")] alias unit := trivial

@[simp] theorem trivial_carrier : (trivial.{uA, uB}).carrier = y := rfl

@[deprecated (since := "2026-10-19")] alias unit_carrier := trivial_carrier

/-- The counit of the composition-unit comonoid is the canonical comparison
between its two universe instantiations. -/
theorem trivial_counit : (trivial.{uA, uB}).counit = Lens.unitComparison := rfl

@[deprecated (since := "2026-10-19")] alias unit_counit := trivial_counit

/-- The comultiplication of the composition-unit comonoid is the canonical
map `y ⇆ y ◃ y`, after comparing its source universe instantiation. -/
theorem trivial_comul :
    (trivial.{uA, uB}).comul =
      Lens.compUnitMap ∘ₗ
        (Lens.unitComparison : Lens y.{uA, uB} y.{max uA uB, uB}) := rfl

@[deprecated (since := "2026-10-19")] alias unit_comult := trivial_comul

/-! ## Tensor product -/

/-- The counit of the tensor product of two composition comonoids. -/
def tensorCounit (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Lens (C.carrier ⊗ D.carrier)
      y.{max (max uA₁ uA₂) (max uB₁ uB₂), max uB₁ uB₂} :=
  Lens.tensorUnitMap ∘ₗ (C.counit ⊗ₗ D.counit)

/-- The comultiplication of the tensor product of two composition comonoids. -/
def tensorComul (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Lens (C.carrier ⊗ D.carrier)
      ((C.carrier ⊗ D.carrier) ◃ (C.carrier ⊗ D.carrier)) :=
  Lens.duoidalLens C.carrier C.carrier D.carrier D.carrier ∘ₗ
    (C.comul ⊗ₗ D.comul)

@[deprecated (since := "2026-10-19")] alias tensorComult := tensorComul

private theorem tensorCounit_left_factor (C : Comonoid.{uA₁, uB₁})
    (D : Comonoid.{uA₂, uB₂}) :
    Lens.Equiv.yComp.toLens ∘ₗ
        (tensorCounit C D ◃ₗ Lens.id (C.carrier ⊗ D.carrier)) ∘ₗ
        tensorComul C D =
      ((Lens.Equiv.yComp.toLens ∘ₗ
          (C.counit ◃ₗ Lens.id C.carrier) ∘ₗ C.comul) ⊗ₗ
        (Lens.Equiv.yComp.toLens ∘ₗ
          (D.counit ◃ₗ Lens.id D.carrier) ∘ₗ D.comul)) := rfl

private theorem tensorCounit_right_factor (C : Comonoid.{uA₁, uB₁})
    (D : Comonoid.{uA₂, uB₂}) :
    Lens.Equiv.compY.toLens ∘ₗ
        (Lens.id (C.carrier ⊗ D.carrier) ◃ₗ tensorCounit C D) ∘ₗ
        tensorComul C D =
      ((Lens.Equiv.compY.toLens ∘ₗ
          (Lens.id C.carrier ◃ₗ C.counit) ∘ₗ C.comul) ⊗ₗ
        (Lens.Equiv.compY.toLens ∘ₗ
          (Lens.id D.carrier ◃ₗ D.counit) ∘ₗ D.comul)) := rfl

private theorem tensorComul_assoc_left_factor (C : Comonoid.{uA₁, uB₁})
    (D : Comonoid.{uA₂, uB₂}) :
    Lens.Equiv.compAssoc.toLens ∘ₗ
        (tensorComul C D ◃ₗ Lens.id (C.carrier ⊗ D.carrier)) ∘ₗ
        tensorComul C D =
      (Lens.id (C.carrier ⊗ D.carrier) ◃ₗ
          Lens.duoidalLens C.carrier C.carrier D.carrier D.carrier) ∘ₗ
        Lens.duoidalLens C.carrier (C.carrier ◃ C.carrier)
          D.carrier (D.carrier ◃ D.carrier) ∘ₗ
        ((Lens.Equiv.compAssoc.toLens ∘ₗ
            (C.comul ◃ₗ Lens.id C.carrier) ∘ₗ C.comul) ⊗ₗ
          (Lens.Equiv.compAssoc.toLens ∘ₗ
            (D.comul ◃ₗ Lens.id D.carrier) ∘ₗ D.comul)) := rfl

private theorem tensorComul_assoc_right_factor (C : Comonoid.{uA₁, uB₁})
    (D : Comonoid.{uA₂, uB₂}) :
    (Lens.id (C.carrier ⊗ D.carrier) ◃ₗ tensorComul C D) ∘ₗ
        tensorComul C D =
      (Lens.id (C.carrier ⊗ D.carrier) ◃ₗ
          Lens.duoidalLens C.carrier C.carrier D.carrier D.carrier) ∘ₗ
        Lens.duoidalLens C.carrier (C.carrier ◃ C.carrier)
          D.carrier (D.carrier ◃ D.carrier) ∘ₗ
        (((Lens.id C.carrier ◃ₗ C.comul) ∘ₗ C.comul) ⊗ₗ
          ((Lens.id D.carrier ◃ₗ D.comul) ∘ₗ D.comul)) := rfl

/-- The tensor product of two comonoids in `(Poly, ◃, y)`.  The construction
is heterogeneous in both input universe pairs and lands at their componentwise
maximum. -/
@[reducible]
def tensor (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Comonoid.{max uA₁ uA₂, max uB₁ uB₂} where
  carrier := C.carrier ⊗ D.carrier
  counit := tensorCounit C D
  comul := tensorComul C D
  counit_left := by
    rw [tensorCounit_left_factor, C.counit_left, D.counit_left,
      Lens.tensorMap_id]
  counit_right := by
    rw [tensorCounit_right_factor, C.counit_right, D.counit_right,
      Lens.tensorMap_id]
  coassoc := by
    rw [tensorComul_assoc_left_factor, C.coassoc, D.coassoc]
    exact (tensorComul_assoc_right_factor C D).symm

@[simp] theorem tensor_carrier (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (tensor C D).carrier = C.carrier ⊗ D.carrier := rfl

/-- The tensor-product counit is the componentwise counit followed by the
canonical comparison of tensor units. -/
theorem tensor_counit (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (tensor C D).counit = tensorCounit C D := rfl

/-- The tensor-product comultiplication is componentwise comultiplication
followed by duoidal interchange. -/
theorem tensor_comul (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (tensor C D).comul = tensorComul C D := rfl

@[deprecated (since := "2026-10-19")] alias tensor_comult := tensor_comul

/-! ## Tensor coherence isomorphisms -/

/-- The left tensor unitor, lifted from polynomial lenses to composition
comonoids.  Both directions preserve identities and composition. -/
def tensorLeftUnitor (C : Comonoid.{uA, uB}) :
    CategoryTheory.Iso (tensor (trivial.{uA, uB}) C) C where
  hom := {
    toLens := (Lens.Equiv.yTensor (P := C.carrier)).toLens
    map_counit := rfl
    map_comul := rfl }
  inv := {
    toLens := (Lens.Equiv.yTensor (P := C.carrier)).invLens
    map_counit := rfl
    map_comul := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

@[deprecated (since := "2026-10-19")] alias tensorUnitLeftIso := tensorLeftUnitor

@[simp] theorem tensorLeftUnitor_hom_toLens (C : Comonoid.{uA, uB}) :
    (tensorLeftUnitor C).hom.toLens =
      (Lens.Equiv.yTensor (P := C.carrier)).toLens := rfl

@[deprecated (since := "2026-10-19")] alias tensorUnitLeftIso_hom_toLens :=
  tensorLeftUnitor_hom_toLens

@[simp] theorem tensorLeftUnitor_inv_toLens (C : Comonoid.{uA, uB}) :
    (tensorLeftUnitor C).inv.toLens =
      (Lens.Equiv.yTensor (P := C.carrier)).invLens := rfl

@[deprecated (since := "2026-10-19")] alias tensorUnitLeftIso_inv_toLens :=
  tensorLeftUnitor_inv_toLens

/-- The right tensor unitor, lifted from polynomial lenses to composition
comonoids.  Both directions preserve identities and composition. -/
def tensorRightUnitor (C : Comonoid.{uA, uB}) :
    CategoryTheory.Iso (tensor C (trivial.{uA, uB})) C where
  hom := {
    toLens := (Lens.Equiv.tensorY (P := C.carrier)).toLens
    map_counit := rfl
    map_comul := rfl }
  inv := {
    toLens := (Lens.Equiv.tensorY (P := C.carrier)).invLens
    map_counit := rfl
    map_comul := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

@[deprecated (since := "2026-10-19")] alias tensorUnitRightIso := tensorRightUnitor

@[simp] theorem tensorRightUnitor_hom_toLens (C : Comonoid.{uA, uB}) :
    (tensorRightUnitor C).hom.toLens =
      (Lens.Equiv.tensorY (P := C.carrier)).toLens := rfl

@[deprecated (since := "2026-10-19")] alias tensorUnitRightIso_hom_toLens :=
  tensorRightUnitor_hom_toLens

@[simp] theorem tensorRightUnitor_inv_toLens (C : Comonoid.{uA, uB}) :
    (tensorRightUnitor C).inv.toLens =
      (Lens.Equiv.tensorY (P := C.carrier)).invLens := rfl

@[deprecated (since := "2026-10-19")] alias tensorUnitRightIso_inv_toLens :=
  tensorRightUnitor_inv_toLens

/-- The tensor associator, lifted from polynomial lenses to composition
comonoids.  The three input universe pairs remain independent. -/
def tensorAssociator
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    CategoryTheory.Iso (tensor (tensor C D) E)
      (tensor C (tensor D E)) where
  hom := {
    toLens := (Lens.Equiv.tensorAssoc
      (P := C.carrier) (Q := D.carrier) (R := E.carrier)).toLens
    map_counit := rfl
    map_comul := rfl }
  inv := {
    toLens := (Lens.Equiv.tensorAssoc
      (P := C.carrier) (Q := D.carrier) (R := E.carrier)).invLens
    map_counit := rfl
    map_comul := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

@[deprecated (since := "2026-10-19")] alias tensorAssocIso := tensorAssociator

@[simp] theorem tensorAssociator_hom_toLens
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    (tensorAssociator C D E).hom.toLens =
      (Lens.Equiv.tensorAssoc
        (P := C.carrier) (Q := D.carrier) (R := E.carrier)).toLens := rfl

@[deprecated (since := "2026-10-19")] alias tensorAssocIso_hom_toLens := tensorAssociator_hom_toLens

@[simp] theorem tensorAssociator_inv_toLens
    (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    (tensorAssociator C D E).inv.toLens =
      (Lens.Equiv.tensorAssoc
        (P := C.carrier) (Q := D.carrier) (R := E.carrier)).invLens := rfl

@[deprecated (since := "2026-10-19")] alias tensorAssocIso_inv_toLens := tensorAssociator_inv_toLens

/-! ## Tensor products of retrofunctors -/

namespace Hom

/-- The componentwise tensor product of two retrofunctors. -/
def tensor {C₁ D₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ : Comonoid.{uA₂, uB₂}} (f : Hom C₁ D₁)
    (g : Hom C₂ D₂) : Hom (Comonoid.tensor C₁ C₂) (Comonoid.tensor D₁ D₂) where
  toLens := f.toLens ⊗ₗ g.toLens
  map_counit := by
    change Lens.tensorUnitMap ∘ₗ
        ((D₁.counit ⊗ₗ D₂.counit) ∘ₗ (f.toLens ⊗ₗ g.toLens)) = _
    rw [← Lens.tensorMap_comp, f.map_counit, g.map_counit]
    rfl
  map_comul := by
    change Lens.duoidalLens D₁.carrier D₁.carrier D₂.carrier D₂.carrier ∘ₗ
        ((D₁.comul ⊗ₗ D₂.comul) ∘ₗ (f.toLens ⊗ₗ g.toLens)) = _
    rw [← Lens.tensorMap_comp, f.map_comul, g.map_comul]
    rfl

@[simp] theorem tensor_toLens {C₁ D₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ : Comonoid.{uA₂, uB₂}}
    (f : Hom C₁ D₁) (g : Hom C₂ D₂) : (tensor f g).toLens = f.toLens ⊗ₗ g.toLens := rfl

@[simp] theorem tensor_id (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    tensor (Hom.id C) (Hom.id D) = Hom.id (Comonoid.tensor C D) :=
  Hom.ext _ _ Lens.tensorMap_id

theorem tensor_comp {C₁ D₁ E₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ E₂ : Comonoid.{uA₂, uB₂}}
    (f₁ : Hom C₁ D₁) (g₁ : Hom D₁ E₁) (f₂ : Hom C₂ D₂) (g₂ : Hom D₂ E₂) :
    tensor (f₁.comp g₁) (f₂.comp g₂) = (tensor f₁ f₂).comp (tensor g₁ g₂) :=
  Hom.ext _ _ (Lens.tensorMap_comp f₁.toLens f₂.toLens g₁.toLens g₂.toLens)

end Hom
end Comonoid
end PFunctor
