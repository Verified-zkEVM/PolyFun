/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree.Universal
public import PolyFun.PFunctor.Comonoid.Tensor

/-!
# The cofree polynomial comonoid is lax monoidal

The cofree-comonoid construction carries canonical comparison maps

* `X ⇝ CofreeP X`, and
* `CofreeP P ⊗ CofreeP Q ⇝ CofreeP (P ⊗ Q)`.

They are the unique cofree extensions of the canonical unit comparison and of
the tensor of the two cogenerators.  The cofree universal property reduces
naturality, left and right unitality, and associativity to the corresponding
tensor-lens coherence equations.

This is Libkind–Spivak, *Pattern Runs on Matter*, Proposition C.1, and the
concrete lax-monoidal construction of Spivak–Niu, Proposition 8.79 in the
current edition (Proposition 8.81 in earlier-edition notes).  The module
supplies the explicit maps and laws needed downstream; it does not install an
abstract `LaxMonoidalFunctor` or symmetric-monoidal packaging.
-/

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PFunctor
namespace CofreeP

/-! ## Structure maps and generator equations -/

/-- The lax-monoidal unit retrofunctor, obtained by cofreely extending the
canonical comparison between the two required universe instances of `X`. -/
def laxUnitHom :
    Comonoid.Hom
      (Comonoid.unit.{max uA uB, max uA uB})
      (comonoid X.{uA, uB}) :=
  extend (Comonoid.unit.{max uA uB, max uA uB})
    (Lens.unitComparison :
      Lens X.{max uA uB, max uA uB} X.{uA, uB})

/-- The underlying lens of the lax-monoidal unit map. -/
def laxUnit : Lens X.{max uA uB, max uA uB} (CofreeP X.{uA, uB}) :=
  laxUnitHom.toLens

@[simp]
theorem laxUnitHom_toLens :
    laxUnitHom.{uA, uB}.toLens = laxUnit.{uA, uB} :=
  rfl

/-- Projecting the lax unit to one generator layer recovers the canonical unit
comparison. -/
@[simp]
theorem cogenerator_comp_laxUnit :
    cogenerator X.{uA, uB} ∘ₗ laxUnit.{uA, uB} =
      (Lens.unitComparison :
        Lens X.{max uA uB, max uA uB} X.{uA, uB}) := by
  exact restrict_extend (Comonoid.unit.{max uA uB, max uA uB})
    (Lens.unitComparison :
      Lens X.{max uA uB, max uA uB} X.{uA, uB})

/-- The binary lax-monoidal comparison retrofunctor, obtained by cofreely
extending the tensor of the two cogenerator lenses. -/
def laxTensorHom (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    Comonoid.Hom
      (Comonoid.tensor (comonoid P) (comonoid Q))
      (comonoid (P ⊗ Q)) :=
  extend (Comonoid.tensor (comonoid P) (comonoid Q))
    (cogenerator P ⊗ₗ cogenerator Q)

/-- The underlying lens of the binary lax-monoidal comparison. -/
def laxTensor (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    Lens (CofreeP P ⊗ CofreeP Q) (CofreeP (P ⊗ Q)) :=
  (laxTensorHom P Q).toLens

@[simp]
theorem laxTensorHom_toLens
    (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    (laxTensorHom P Q).toLens = laxTensor P Q :=
  rfl

/-- Projecting the binary comparison to one generator layer recovers the
tensor of the two cogenerators. -/
@[simp]
theorem cogenerator_comp_laxTensor
    (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    cogenerator (P ⊗ Q) ∘ₗ laxTensor P Q =
      cogenerator P ⊗ₗ cogenerator Q := by
  exact restrict_extend (Comonoid.tensor (comonoid P) (comonoid Q))
    (cogenerator P ⊗ₗ cogenerator Q)

/-! ## Executable equations -/

theorem laxUnit_head :
    M.head ((laxUnit.{uA, uB}).toFunA PUnit.unit) = PUnit.unit :=
  rfl

theorem laxUnit_children :
    M.children ((laxUnit.{uA, uB}).toFunA PUnit.unit) PUnit.unit =
      (laxUnit.{uA, uB}).toFunA PUnit.unit := by
  change M.children (unfoldShape _ _ _) _ = unfoldShape _ _ _
  rw [children_unfoldShape]
  rfl

@[simp]
theorem laxUnit_toFunB
    (vertex : M.Vertex ((laxUnit.{uA, uB}).toFunA PUnit.unit)) :
    (laxUnit.{uA, uB}).toFunB PUnit.unit vertex = PUnit.unit :=
  Subsingleton.elim _ _

@[simp]
theorem laxTensor_head (P : PFunctor.{uA₁, uB₁})
    (Q : PFunctor.{uA₂, uB₂})
    (left : (CofreeP P).A) (right : (CofreeP Q).A) :
    M.head ((laxTensor P Q).toFunA (left, right)) =
      (M.head left, M.head right) :=
  rfl

@[simp]
theorem laxTensor_children (P : PFunctor.{uA₁, uB₁})
    (Q : PFunctor.{uA₂, uB₂})
    (left : (CofreeP P).A) (right : (CofreeP Q).A)
    (direction : P.B (M.head left) × Q.B (M.head right)) :
    M.children ((laxTensor P Q).toFunA (left, right)) direction =
      (laxTensor P Q).toFunA
        (M.children left direction.1, M.children right direction.2) := by
  change M.children (unfoldShape _ _ _) _ = unfoldShape _ _ _
  rw [children_unfoldShape]
  rfl

@[simp]
theorem laxTensor_toFunB_root (P : PFunctor.{uA₁, uB₁})
    (Q : PFunctor.{uA₂, uB₂})
    (left : (CofreeP P).A) (right : (CofreeP Q).A) :
    (laxTensor P Q).toFunB (left, right)
        (.root ((laxTensor P Q).toFunA (left, right))) =
      (.root left, .root right) := by
  change unfoldDirection _ _ _ (.root _) = _
  rw [unfoldDirection_root]
  rfl

/-- Low-level recurrence for pulling a non-root vertex back through the
cofree laxator. Its explicit cast records the definitional mismatch between
the actual child of the unfolded tree and the unfolding of the two selected
children. Most consumers should use `laxTensor_childObj`, which packages and
hides this transport. -/
theorem laxTensor_toFunB_child (P : PFunctor.{uA₁, uB₁})
    (Q : PFunctor.{uA₂, uB₂})
    (left : (CofreeP P).A) (right : (CofreeP Q).A)
    (direction : P.B (M.head left) × Q.B (M.head right))
    (next : M.Vertex
      (M.children ((laxTensor P Q).toFunA (left, right)) direction)) :
    (laxTensor P Q).toFunB (left, right) (.child direction next) =
      let childEq := laxTensor_children P Q left right direction
      let pulled := (laxTensor P Q).toFunB
        (M.children left direction.1, M.children right direction.2)
        (cast (congrArg M.Vertex childEq) next)
      (.child direction.1 pulled.1, .child direction.2 pulled.2) := by
  change unfoldDirection
    (Comonoid.tensor (comonoid P) (comonoid Q))
    (cogenerator P ⊗ₗ cogenerator Q)
    (left, right) (.child direction next) = _
  rw [unfoldDirection.eq_def]
  rfl

/-- The synchronized child of the cofree laxator, packaged with its complete
backward vertex map. This is the stable, cast-free rewriting boundary for
consumers that recurse through `laxTensor`. -/
theorem laxTensor_childObj (P : PFunctor.{uA₁, uB₁})
    (Q : PFunctor.{uA₂, uB₂})
    (left : (CofreeP P).A) (right : (CofreeP Q).A)
    (direction : P.B (M.head left) × Q.B (M.head right)) :
    let combined := (laxTensor P Q).toFunA (left, right)
    let mappedChild := Lens.mapObj (laxTensor P Q)
      (⟨(M.children left direction.1,
          M.children right direction.2), id⟩ :
        (CofreeP P ⊗ CofreeP Q).Obj
          (M.Vertex (M.children left direction.1) ×
            M.Vertex (M.children right direction.2)))
    (⟨M.children combined direction, fun next =>
        (laxTensor P Q).toFunB (left, right) (.child direction next)⟩ :
      (CofreeP (P ⊗ Q)).Obj (M.Vertex left × M.Vertex right)) =
    ⟨mappedChild.1, fun next =>
      let pulled := mappedChild.2 next
      (.child direction.1 pulled.1, .child direction.2 pulled.2)⟩ := by
  dsimp only
  let childEq := laxTensor_children P Q left right direction
  apply Sigma.ext childEq
  apply Function.hfunext (congrArg M.Vertex childEq)
  intro leftVertex rightVertex hVertex
  have hcast : cast (congrArg M.Vertex childEq) leftVertex = rightVertex :=
    (cast_eq_iff_heq).2 hVertex
  subst rightVertex
  apply heq_of_eq
  change (laxTensor P Q).toFunB
      ((left, right) : (CofreeP P ⊗ CofreeP Q).A)
      (.child direction leftVertex) =
    let pulled := (laxTensor P Q).toFunB
      ((M.children left direction.1,
        M.children right direction.2) :
        (CofreeP P ⊗ CofreeP Q).A)
      (cast (congrArg M.Vertex childEq) leftVertex)
    (.child direction.1 pulled.1, .child direction.2 pulled.2)
  exact laxTensor_toFunB_child P Q left right direction leftVertex

/-! ## Naturality -/

/-- The binary comparison is natural in both generator polynomials.  Each
source/target pair shares only the universe pair required by `mapHom`; the two
tensor factors remain independent. -/
theorem laxTensorHom_natural
    {P P' : PFunctor.{uA₁, uB₁}} {Q Q' : PFunctor.{uA₂, uB₂}}
    (f : Lens P P') (g : Lens Q Q') :
    (Comonoid.Hom.tensor (mapHom f) (mapHom g)).comp
        (laxTensorHom P' Q') =
      (laxTensorHom P Q).comp (mapHom (f ⊗ₗ g)) := by
  apply hom_ext_cogenerator
  simp only [Comonoid.Hom.comp_toLens, Comonoid.Hom.tensor_toLens,
    mapHom_toLens, laxTensorHom_toLens]
  calc
    cogenerator (P' ⊗ Q') ∘ₗ
          (laxTensor P' Q' ∘ₗ (map f ⊗ₗ map g)) =
        (cogenerator (P' ⊗ Q') ∘ₗ laxTensor P' Q') ∘ₗ
          (map f ⊗ₗ map g) :=
      (Lens.comp_assoc _ _ _).symm
    _ = (cogenerator P' ⊗ₗ cogenerator Q') ∘ₗ
          (map f ⊗ₗ map g) := by rw [cogenerator_comp_laxTensor]
    _ = (cogenerator P' ∘ₗ map f) ⊗ₗ
          (cogenerator Q' ∘ₗ map g) :=
      (Lens.tensorMap_comp _ _ _ _).symm
    _ = (f ∘ₗ cogenerator P) ⊗ₗ
          (g ∘ₗ cogenerator Q) := by
      rw [cogenerator_comp_map, cogenerator_comp_map]
    _ = (f ⊗ₗ g) ∘ₗ (cogenerator P ⊗ₗ cogenerator Q) :=
      Lens.tensorMap_comp _ _ _ _
    _ = (f ⊗ₗ g) ∘ₗ
          (cogenerator (P ⊗ Q) ∘ₗ laxTensor P Q) := by
      rw [cogenerator_comp_laxTensor]
    _ = ((f ⊗ₗ g) ∘ₗ cogenerator (P ⊗ Q)) ∘ₗ laxTensor P Q :=
      (Lens.comp_assoc _ _ _).symm
    _ = (cogenerator (P' ⊗ Q') ∘ₗ map (f ⊗ₗ g)) ∘ₗ
          laxTensor P Q := by rw [cogenerator_comp_map]
    _ = cogenerator (P' ⊗ Q') ∘ₗ
          (map (f ⊗ₗ g) ∘ₗ laxTensor P Q) :=
      Lens.comp_assoc _ _ _

/-- Lens-level naturality of the binary lax-monoidal comparison inside each
fixed-universe polynomial category.  Cross-universe naturality requires a
heterogeneous retrofunctor-law API beyond the homogeneous `Comonoid.Hom`
boundary. -/
theorem laxTensor_natural
    {P P' : PFunctor.{uA₁, uB₁}} {Q Q' : PFunctor.{uA₂, uB₂}}
    (f : Lens P P') (g : Lens Q Q') :
    laxTensor P' Q' ∘ₗ (map f ⊗ₗ map g) =
      map (f ⊗ₗ g) ∘ₗ laxTensor P Q := by
  exact congrArg Comonoid.Hom.toLens (laxTensorHom_natural f g)

/-! ## Lax-monoidal coherence -/

/-- Left-unit coherence for the lax-monoidal comparison, at the level of
retrofunctors. -/
theorem laxTensorHom_unit_left (P : PFunctor.{uA, uB}) :
    ((Comonoid.Hom.tensor laxUnitHom.{uA, uB}
        (Comonoid.Hom.id (comonoid P))).comp
      (laxTensorHom X.{uA, uB} P)).comp
        (mapHom (Lens.Equiv.xTensor (P := P)).toLens) =
      (Comonoid.tensorUnitLeftIso (comonoid P)).hom := by
  apply hom_ext_cogenerator
  simp only [Comonoid.Hom.comp_toLens, Comonoid.Hom.tensor_toLens,
    Comonoid.Hom.id_toLens, mapHom_toLens, laxTensorHom_toLens,
    laxUnitHom_toLens, Comonoid.tensorUnitLeftIso_hom_toLens]
  calc
    cogenerator P ∘ₗ
          (map ((Lens.Equiv.xTensor (P := P)).toLens) ∘ₗ
            (laxTensor X.{uA, uB} P ∘ₗ
              (laxUnit.{uA, uB} ⊗ₗ Lens.id (CofreeP P)))) =
        ((Lens.Equiv.xTensor (P := P)).toLens ∘ₗ
          cogenerator (X.{uA, uB} ⊗ P)) ∘ₗ
            (laxTensor X.{uA, uB} P ∘ₗ
              (laxUnit.{uA, uB} ⊗ₗ Lens.id (CofreeP P))) := by
      rw [← Lens.comp_assoc, cogenerator_comp_map]
    _ = (Lens.Equiv.xTensor (P := P)).toLens ∘ₗ
          ((cogenerator (X.{uA, uB} ⊗ P) ∘ₗ
              laxTensor X.{uA, uB} P) ∘ₗ
            (laxUnit.{uA, uB} ⊗ₗ Lens.id (CofreeP P))) := by
      simp only [Lens.comp_assoc]
    _ = (Lens.Equiv.xTensor (P := P)).toLens ∘ₗ
          ((cogenerator X.{uA, uB} ⊗ₗ cogenerator P) ∘ₗ
            (laxUnit.{uA, uB} ⊗ₗ Lens.id (CofreeP P))) := by
      rw [cogenerator_comp_laxTensor]
    _ = (Lens.Equiv.xTensor (P := P)).toLens ∘ₗ
          ((cogenerator X.{uA, uB} ∘ₗ laxUnit.{uA, uB}) ⊗ₗ
            (cogenerator P ∘ₗ Lens.id (CofreeP P))) := by
      rw [Lens.tensorMap_comp]
    _ = (Lens.Equiv.xTensor (P := P)).toLens ∘ₗ
          ((Lens.unitComparison :
              Lens X.{max uA uB, max uA uB} X.{uA, uB}) ⊗ₗ
            cogenerator P) := by
      simp only [cogenerator_comp_laxUnit, Lens.comp_id]
    _ = cogenerator P ∘ₗ
          (Lens.Equiv.xTensor (P := CofreeP P)).toLens :=
      (Lens.xTensor_natural (cogenerator P)).symm

/-- Right-unit coherence for the lax-monoidal comparison, at the level of
retrofunctors. -/
theorem laxTensorHom_unit_right (P : PFunctor.{uA, uB}) :
    ((Comonoid.Hom.tensor (Comonoid.Hom.id (comonoid P))
        laxUnitHom.{uA, uB}).comp
      (laxTensorHom P X.{uA, uB})).comp
        (mapHom (Lens.Equiv.tensorX (P := P)).toLens) =
      (Comonoid.tensorUnitRightIso (comonoid P)).hom := by
  apply hom_ext_cogenerator
  simp only [Comonoid.Hom.comp_toLens, Comonoid.Hom.tensor_toLens,
    Comonoid.Hom.id_toLens, mapHom_toLens, laxTensorHom_toLens,
    laxUnitHom_toLens, Comonoid.tensorUnitRightIso_hom_toLens]
  calc
    cogenerator P ∘ₗ
          (map ((Lens.Equiv.tensorX (P := P)).toLens) ∘ₗ
            (laxTensor P X.{uA, uB} ∘ₗ
              (Lens.id (CofreeP P) ⊗ₗ laxUnit.{uA, uB}))) =
        ((Lens.Equiv.tensorX (P := P)).toLens ∘ₗ
          cogenerator (P ⊗ X.{uA, uB})) ∘ₗ
            (laxTensor P X.{uA, uB} ∘ₗ
              (Lens.id (CofreeP P) ⊗ₗ laxUnit.{uA, uB})) := by
      rw [← Lens.comp_assoc, cogenerator_comp_map]
    _ = (Lens.Equiv.tensorX (P := P)).toLens ∘ₗ
          ((cogenerator (P ⊗ X.{uA, uB}) ∘ₗ
              laxTensor P X.{uA, uB}) ∘ₗ
            (Lens.id (CofreeP P) ⊗ₗ laxUnit.{uA, uB})) := by
      simp only [Lens.comp_assoc]
    _ = (Lens.Equiv.tensorX (P := P)).toLens ∘ₗ
          ((cogenerator P ⊗ₗ cogenerator X.{uA, uB}) ∘ₗ
            (Lens.id (CofreeP P) ⊗ₗ laxUnit.{uA, uB})) := by
      rw [cogenerator_comp_laxTensor]
    _ = (Lens.Equiv.tensorX (P := P)).toLens ∘ₗ
          ((cogenerator P ∘ₗ Lens.id (CofreeP P)) ⊗ₗ
            (cogenerator X.{uA, uB} ∘ₗ laxUnit.{uA, uB})) := by
      rw [Lens.tensorMap_comp]
    _ = (Lens.Equiv.tensorX (P := P)).toLens ∘ₗ
          (cogenerator P ⊗ₗ
            (Lens.unitComparison :
              Lens X.{max uA uB, max uA uB} X.{uA, uB})) := by
      simp only [cogenerator_comp_laxUnit, Lens.comp_id]
    _ = cogenerator P ∘ₗ
          (Lens.Equiv.tensorX (P := CofreeP P)).toLens :=
      (Lens.tensorX_natural (cogenerator P)).symm

/-- Associativity coherence for the lax-monoidal comparison, at the level of
retrofunctors. -/
theorem laxTensorHom_assoc
    (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂})
    (R : PFunctor.{uA₃, uB₃}) :
    (((Comonoid.tensorAssocIso (comonoid P) (comonoid Q) (comonoid R)).hom.comp
        (Comonoid.Hom.tensor (Comonoid.Hom.id (comonoid P))
          (laxTensorHom Q R))).comp
      (laxTensorHom P (Q ⊗ R))) =
    (((Comonoid.Hom.tensor (laxTensorHom P Q)
        (Comonoid.Hom.id (comonoid R))).comp
      (laxTensorHom (P ⊗ Q) R)).comp
        (mapHom (Lens.Equiv.tensorAssoc
          (P := P) (Q := Q) (R := R)).toLens)) := by
  apply hom_ext_cogenerator
  simp only [Comonoid.Hom.comp_toLens, Comonoid.Hom.tensor_toLens,
    Comonoid.Hom.id_toLens, mapHom_toLens, laxTensorHom_toLens,
    Comonoid.tensorAssocIso_hom_toLens]
  calc
    cogenerator (P ⊗ (Q ⊗ R)) ∘ₗ
          (laxTensor P (Q ⊗ R) ∘ₗ
            ((Lens.id (CofreeP P) ⊗ₗ laxTensor Q R) ∘ₗ
              (Lens.Equiv.tensorAssoc
                (P := CofreeP P) (Q := CofreeP Q)
                (R := CofreeP R)).toLens)) =
        (cogenerator P ⊗ₗ (cogenerator Q ⊗ₗ cogenerator R)) ∘ₗ
          (Lens.Equiv.tensorAssoc
            (P := CofreeP P) (Q := CofreeP Q)
            (R := CofreeP R)).toLens := by
      rw [← Lens.comp_assoc, cogenerator_comp_laxTensor,
        ← Lens.comp_assoc, ← Lens.tensorMap_comp]
      simp only [cogenerator_comp_laxTensor, Lens.comp_id]
    _ = (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens ∘ₗ
          ((cogenerator P ⊗ₗ cogenerator Q) ⊗ₗ cogenerator R) :=
      Lens.tensorAssoc_natural (cogenerator P) (cogenerator Q) (cogenerator R)
    _ = (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens ∘ₗ
          (cogenerator ((P ⊗ Q) ⊗ R) ∘ₗ
            (laxTensor (P ⊗ Q) R ∘ₗ
              (laxTensor P Q ⊗ₗ Lens.id (CofreeP R)))) := by
      apply congrArg (fun lens =>
        (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens ∘ₗ lens)
      calc
        (cogenerator P ⊗ₗ cogenerator Q) ⊗ₗ cogenerator R =
            (cogenerator (P ⊗ Q) ∘ₗ laxTensor P Q) ⊗ₗ
              (cogenerator R ∘ₗ Lens.id (CofreeP R)) := by
          rw [cogenerator_comp_laxTensor]
          simp only [Lens.comp_id]
        _ = (cogenerator (P ⊗ Q) ⊗ₗ cogenerator R) ∘ₗ
              (laxTensor P Q ⊗ₗ Lens.id (CofreeP R)) :=
          Lens.tensorMap_comp _ _ _ _
        _ = (cogenerator ((P ⊗ Q) ⊗ R) ∘ₗ
              laxTensor (P ⊗ Q) R) ∘ₗ
              (laxTensor P Q ⊗ₗ Lens.id (CofreeP R)) := by
          rw [cogenerator_comp_laxTensor]
        _ = cogenerator ((P ⊗ Q) ⊗ R) ∘ₗ
              (laxTensor (P ⊗ Q) R ∘ₗ
                (laxTensor P Q ⊗ₗ Lens.id (CofreeP R))) :=
          Lens.comp_assoc _ _ _
    _ = cogenerator (P ⊗ (Q ⊗ R)) ∘ₗ
          (map ((Lens.Equiv.tensorAssoc
              (P := P) (Q := Q) (R := R)).toLens) ∘ₗ
            (laxTensor (P ⊗ Q) R ∘ₗ
              (laxTensor P Q ⊗ₗ Lens.id (CofreeP R)))) := by
      calc
        _ = ((Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens ∘ₗ
              cogenerator ((P ⊗ Q) ⊗ R)) ∘ₗ
              (laxTensor (P ⊗ Q) R ∘ₗ
                (laxTensor P Q ⊗ₗ Lens.id (CofreeP R))) :=
          (Lens.comp_assoc _ _ _).symm
        _ = (cogenerator (P ⊗ (Q ⊗ R)) ∘ₗ
              map ((Lens.Equiv.tensorAssoc
                (P := P) (Q := Q) (R := R)).toLens)) ∘ₗ
              (laxTensor (P ⊗ Q) R ∘ₗ
                (laxTensor P Q ⊗ₗ Lens.id (CofreeP R))) := by
          rw [cogenerator_comp_map]
        _ = _ := Lens.comp_assoc _ _ _

/-! ### Consumer-facing lens equations -/

/-- Lens-level left-unit coherence. -/
theorem laxTensor_unit_left (P : PFunctor.{uA, uB}) :
    map ((Lens.Equiv.xTensor (P := P)).toLens) ∘ₗ
        laxTensor X.{uA, uB} P ∘ₗ
        (laxUnit.{uA, uB} ⊗ₗ Lens.id (CofreeP P)) =
      (Lens.Equiv.xTensor (P := CofreeP P)).toLens := by
  exact congrArg Comonoid.Hom.toLens (laxTensorHom_unit_left P)

/-- Lens-level right-unit coherence. -/
theorem laxTensor_unit_right (P : PFunctor.{uA, uB}) :
    map ((Lens.Equiv.tensorX (P := P)).toLens) ∘ₗ
        laxTensor P X.{uA, uB} ∘ₗ
        (Lens.id (CofreeP P) ⊗ₗ laxUnit.{uA, uB}) =
      (Lens.Equiv.tensorX (P := CofreeP P)).toLens := by
  exact congrArg Comonoid.Hom.toLens (laxTensorHom_unit_right P)

/-- Lens-level associativity coherence. -/
theorem laxTensor_assoc
    (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂})
    (R : PFunctor.{uA₃, uB₃}) :
    laxTensor P (Q ⊗ R) ∘ₗ
        (Lens.id (CofreeP P) ⊗ₗ laxTensor Q R) ∘ₗ
        (Lens.Equiv.tensorAssoc
          (P := CofreeP P) (Q := CofreeP Q) (R := CofreeP R)).toLens =
      map ((Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens) ∘ₗ
        laxTensor (P ⊗ Q) R ∘ₗ
        (laxTensor P Q ⊗ₗ Lens.id (CofreeP R)) := by
  exact congrArg Comonoid.Hom.toLens (laxTensorHom_assoc P Q R)

end CofreeP
end PFunctor
