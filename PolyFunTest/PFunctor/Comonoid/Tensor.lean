/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Comonoid.Tensor

/-!
# Regression tests for tensor products of polynomial comonoids

The generic canaries keep the two comonoids' universe pairs independent.  The
concrete tests make the tensor counit, the middle-four backward map, componentwise
composition order, and the hidden-state action of tensor-product retrofunctors
computationally observable.  They also pin both directions and inverse laws of
the tensor unitors and associator, including an associator canary with three
independent universe pairs.
-/

@[expose] public section

universe uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PFunctor
namespace ComonoidTensorTest

/-! ## Heterogeneous API canaries -/

/-- Tensor products do not couple either input universe pair. -/
example (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Comonoid.{max uA₁ uA₂, max uB₁ uB₂} :=
  Comonoid.tensor C D

example (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (Comonoid.tensor C D).carrier = C.carrier ⊗ D.carrier := by
  simp

/-- The public equations expose the exact counit and comultiplication maps. -/
example (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (Comonoid.tensor C D).counit = Comonoid.tensorCounit C D :=
  Comonoid.tensor_counit C D

example (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    (Comonoid.tensor C D).comult = Comonoid.tensorComult C D :=
  Comonoid.tensor_comult C D

/-! ## Unit and coherence canaries -/

/-- The unit comonoid retains an independent position/direction universe pair,
including when its structural maps compare different copies of `X`. -/
example : Comonoid.{uA₁, uB₁} := Comonoid.unit

example : (Comonoid.unit.{uA₁, uB₁}).carrier = X := by
  simp

example :
    (Comonoid.unit.{uA₁, uB₁}).counit = Lens.unitComparison :=
  Comonoid.unit_counit

example :
    (Comonoid.unit.{uA₁, uB₁}).comult =
      Lens.compUnitMap ∘ₗ
        (Lens.unitComparison : Lens X.{uA₁, uB₁}
          X.{max uA₁ uB₁, uB₁}) :=
  Comonoid.unit_comult

/-- Both directions of the tensor unitors are comonoid morphisms whose
underlying maps are exactly the established polynomial-lens equivalences. -/
example (C : Comonoid.{uA₁, uB₁}) :
    (Comonoid.tensorUnitLeftIso C).hom.toLens =
      (Lens.Equiv.xTensor (P := C.carrier)).toLens := by
  simp

example (C : Comonoid.{uA₁, uB₁}) :
    (Comonoid.tensorUnitLeftIso C).inv.toLens =
      (Lens.Equiv.xTensor (P := C.carrier)).invLens := by
  simp

example (C : Comonoid.{uA₁, uB₁}) :
    (Comonoid.tensorUnitRightIso C).hom.toLens =
      (Lens.Equiv.tensorX (P := C.carrier)).toLens := by
  simp

example (C : Comonoid.{uA₁, uB₁}) :
    (Comonoid.tensorUnitRightIso C).inv.toLens =
      (Lens.Equiv.tensorX (P := C.carrier)).invLens := by
  simp

/-- The associator remains heterogeneous in all three input universe pairs,
and exposes both directions without transports. -/
example (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    (Comonoid.tensorAssocIso C D E).hom.toLens =
      (Lens.Equiv.tensorAssoc
        (P := C.carrier) (Q := D.carrier) (R := E.carrier)).toLens := by
  simp

example (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    (Comonoid.tensorAssocIso C D E).inv.toLens =
      (Lens.Equiv.tensorAssoc
        (P := C.carrier) (Q := D.carrier) (R := E.carrier)).invLens := by
  simp

/-- Category-theoretic inverse laws are available for each packaged
coherence isomorphism. -/
example (C : Comonoid.{uA₁, uB₁}) :
    (Comonoid.tensorUnitLeftIso C).hom.comp
        (Comonoid.tensorUnitLeftIso C).inv =
      Comonoid.Hom.id
        (Comonoid.tensor (Comonoid.unit.{uA₁, uB₁}) C) := by
  exact (Comonoid.tensorUnitLeftIso C).hom_inv_id

example (C : Comonoid.{uA₁, uB₁}) :
    (Comonoid.tensorUnitLeftIso C).inv.comp
        (Comonoid.tensorUnitLeftIso C).hom =
      Comonoid.Hom.id C := by
  exact (Comonoid.tensorUnitLeftIso C).inv_hom_id

example (C : Comonoid.{uA₁, uB₁}) :
    (Comonoid.tensorUnitRightIso C).inv.comp
        (Comonoid.tensorUnitRightIso C).hom =
      Comonoid.Hom.id C := by
  exact (Comonoid.tensorUnitRightIso C).inv_hom_id

example (C : Comonoid.{uA₁, uB₁}) :
    (Comonoid.tensorUnitRightIso C).hom.comp
        (Comonoid.tensorUnitRightIso C).inv =
      Comonoid.Hom.id
        (Comonoid.tensor C (Comonoid.unit.{uA₁, uB₁})) := by
  exact (Comonoid.tensorUnitRightIso C).hom_inv_id

example (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    (Comonoid.tensorAssocIso C D E).hom.comp
        (Comonoid.tensorAssocIso C D E).inv =
      Comonoid.Hom.id (Comonoid.tensor (Comonoid.tensor C D) E) := by
  exact (Comonoid.tensorAssocIso C D E).hom_inv_id

example (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂})
    (E : Comonoid.{uA₃, uB₃}) :
    (Comonoid.tensorAssocIso C D E).inv.comp
        (Comonoid.tensorAssocIso C D E).hom =
      Comonoid.Hom.id (Comonoid.tensor C (Comonoid.tensor D E)) := by
  exact (Comonoid.tensorAssocIso C D E).inv_hom_id

/-- Tensor products of retrofunctors retain the componentwise lens, identity,
and diagrammatic composition laws. -/
example {C₁ D₁ : Comonoid.{uA₁, uB₁}} {C₂ D₂ : Comonoid.{uA₂, uB₂}}
    (f : Comonoid.Hom C₁ D₁) (g : Comonoid.Hom C₂ D₂) :
    (Comonoid.Hom.tensor f g).toLens = f.toLens ⊗ₗ g.toLens := by
  simp

example (C : Comonoid.{uA₁, uB₁}) (D : Comonoid.{uA₂, uB₂}) :
    Comonoid.Hom.tensor (Comonoid.Hom.id C) (Comonoid.Hom.id D) =
      Comonoid.Hom.id (Comonoid.tensor C D) := by
  simp

example
    {C₁ D₁ E₁ : Comonoid.{uA₁, uB₁}}
    {C₂ D₂ E₂ : Comonoid.{uA₂, uB₂}}
    (f₁ : Comonoid.Hom C₁ D₁) (g₁ : Comonoid.Hom D₁ E₁)
    (f₂ : Comonoid.Hom C₂ D₂) (g₂ : Comonoid.Hom D₂ E₂) :
    Comonoid.Hom.tensor (f₁.comp g₁) (f₂.comp g₂) =
      (Comonoid.Hom.tensor f₁ f₂).comp (Comonoid.Hom.tensor g₁ g₂) :=
  Comonoid.Hom.tensor_comp f₁ g₁ f₂ g₂

/-! ## Observable backward-map and orientation behavior -/

/-- Three distinct states separate the source, intermediate, and final objects
of a two-arrow path. -/
inductive ThreeState where
  | source
  | middle
  | final
  deriving DecidableEq, Repr

/-- The tensor counit reconstructs both component identity arrows. -/
example :
    (Comonoid.tensor (stateComonoid ThreeState) (stateComonoid Bool)).counit.toFunB
        (.source, false) PUnit.unit = (.source, false) :=
  rfl

/-- The tensor comultiplication's backward map consumes a pair of two-step
paths and returns both final targets.  This detects the middle-four direction
permutation, not merely the forward object map. -/
example :
    (Comonoid.tensor (stateComonoid ThreeState) (stateComonoid Bool)).comult.toFunB
        (.source, false) ⟨(.middle, true), (.final, false)⟩ =
      (.final, false) :=
  rfl

/-- A one-object category whose arrows are Boolean words under concatenation.
Its noncommutative composition makes path order observable. -/
def listMonoidComonoid : Comonoid where
  carrier := purePower (List Bool)
  counit := (fun _ => PUnit.unit) ⇆ (fun _ _ => [])
  comult :=
    (fun _ => ⟨PUnit.unit, fun _ => PUnit.unit⟩) ⇆
      (fun _ directions =>
        (show List Bool from directions.1) ++
          (show List Bool from directions.2))
  counit_left := by
    refine Lens.ext _ _ (fun _ => rfl) (fun _ => ?_)
    funext direction
    exact List.nil_append direction
  counit_right := by
    refine Lens.ext _ _ (fun _ => rfl) (fun _ => ?_)
    funext direction
    exact List.append_nil direction
  coassoc := by
    refine Lens.ext _ _ (fun _ => rfl) (fun _ => ?_)
    funext direction
    change
      ((show List Bool from direction.1) ++
        (show List Bool from direction.2.1)) ++
          (show List Bool from direction.2.2) =
        (show List Bool from direction.1) ++
          ((show List Bool from direction.2.1) ++
            (show List Bool from direction.2.2))
    exact List.append_assoc direction.1 direction.2.1 direction.2.2

/-! ## Observable coherence maps -/

/-- The forward and inverse left unitors expose the exact placement and
removal of the unit direction. -/
example :
    (Comonoid.tensorUnitLeftIso listMonoidComonoid).hom.toLens.toFunB
        (PUnit.unit, PUnit.unit) [false, true] =
      (PUnit.unit, [false, true]) :=
  rfl

example :
    (Comonoid.tensorUnitLeftIso listMonoidComonoid).inv.toLens.toFunB
        PUnit.unit (PUnit.unit, [false, true]) = [false, true] :=
  rfl

/-- The forward and inverse right unitors place the unique unit direction on
the opposite side. -/
example :
    (Comonoid.tensorUnitRightIso listMonoidComonoid).hom.toLens.toFunB
        (PUnit.unit, PUnit.unit) [false, true] =
      ([false, true], PUnit.unit) :=
  rfl

example :
    (Comonoid.tensorUnitRightIso listMonoidComonoid).inv.toLens.toFunB
        PUnit.unit ([false, true], PUnit.unit) = [false, true] :=
  rfl

/-- The two associator directions perform opposite rebracketings on three
distinguishable direction components. -/
example :
    (Comonoid.tensorAssocIso listMonoidComonoid listMonoidComonoid
        listMonoidComonoid).hom.toLens.toFunB
      ((PUnit.unit, PUnit.unit), PUnit.unit)
      ([false], ([true], [])) = (([false], [true]), []) :=
  rfl

example :
    (Comonoid.tensorAssocIso listMonoidComonoid listMonoidComonoid
        listMonoidComonoid).inv.toLens.toFunB
      (PUnit.unit, (PUnit.unit, PUnit.unit))
      (([false], [true]), []) = ([false], ([true], [])) :=
  rfl

/-- Tensor composition is componentwise and outer-before-inner in each
noncommutative factor.  Swapping phases or crossing middle components changes
this result. -/
example :
    (Comonoid.tensor listMonoidComonoid listMonoidComonoid).comult.toFunB
        (PUnit.unit, PUnit.unit)
        ⟨([false], [true]), ([true], [false])⟩ =
      ([false, true], [true, false]) :=
  rfl

/-- A tensor of state-lens retrofunctors updates both hidden state components
independently. -/
def fstTensorHom : Comonoid.Hom
    (Comonoid.tensor
      (stateComonoid (ThreeState × Bool))
      (stateComonoid (Bool × Nat)))
    (Comonoid.tensor (stateComonoid ThreeState) (stateComonoid Bool)) :=
  Comonoid.Hom.tensor
    (Comonoid.Hom.ofStateLens (Lens.State.fst ThreeState Bool))
    (Comonoid.Hom.ofStateLens (Lens.State.fst Bool Nat))

/-- The forward map drops each hidden component. -/
example :
    fstTensorHom.toLens.toFunA ((.source, true), (false, 7)) =
      (.source, false) :=
  rfl

/-- The backward map preserves each hidden component while updating the two
visible states, pinning both tensor pairing and retrofunctor orientation. -/
example :
    fstTensorHom.toLens.toFunB ((.source, true), (false, 7)) (.final, true) =
      ((.final, true), (true, 7)) :=
  rfl

end ComonoidTensorTest
end PFunctor
