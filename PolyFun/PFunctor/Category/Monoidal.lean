/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Category
public import PolyFun.PFunctor.Lens.Coherence
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Monoidal structures on the category of lenses

The category of polynomials and lenses carries three monoidal structures (Niu–Spivak §3.10,
p. 65, and §6.3, pp. 202–213). A `MonoidalCategory` instance is keyed on its carrier, so each
structure gets its own carrier with the lens category on it, following `PFunctor/Category.lean`:

* `LensCat` is cartesian monoidal for the categorical product `*` with terminal object `1`
  (`CartesianMonoidalCategory`, Prop 3.56), built from the limit cones `prodFan` and
  `isTerminalOne`.
* `TensorCat` is `LensCat` with the parallel product `⊗` and unit `y`, a symmetric monoidal
  category (Prop 3.73).
* `CompCat.{u, v}` is `LensCat.{max u v, v}` with the composition product `◃` and unit `y`, a
  monoidal category (§6.3). The universe pair `{max u v, v}` is closed under `◃` and contains the
  counit target `y.{max uA uB, uB}` of a `PFunctor.Comonoid`.

Every coherence field of the `⊗` and `◃` structures is a lemma of `PFunctor/Lens/Coherence.lean`
and holds definitionally. Lens equivalences `≃ₗ` become isomorphisms through `isoOfEquiv`.
-/

@[expose] public section

universe u v uA uB

open CategoryTheory Limits

namespace PFunctor

/-! ## The cartesian structure on `LensCat` -/

namespace LensCat

/-- A lens equivalence is an isomorphism in `LensCat`. -/
abbrev isoOfEquiv {P Q : LensCat.{uA, uB}} (e : P.as ≃ₗ Q.as) : P ≅ Q :=
  ⟨e.toLens, e.invLens, e.left_inv, e.right_inv⟩

/-- `1` is terminal in `LensCat`. -/
def isTerminalOne : IsTerminal (LensCat.of (1 : PFunctor.{uA, uB})) :=
  IsTerminal.ofUniqueHom (fun _ => Lens.terminal) fun _ _ =>
    Lens.ext _ _ (fun _ => rfl) fun _ => funext fun d => d.elim

/-- The product cone `P * Q` with its two projections. -/
def prodFan (P Q : LensCat.{uA, uB}) : BinaryFan P Q :=
  BinaryFan.mk (P := LensCat.of (P.as * Q.as)) Lens.fst Lens.snd

/-- `P * Q` is the product of `P` and `Q` in `LensCat` (Niu–Spivak Prop 3.56). -/
def prodFanIsLimit (P Q : LensCat.{uA, uB}) : IsLimit (prodFan P Q) :=
  BinaryFan.IsLimit.mk _ (fun f g => Lens.prodPair f g) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ m h₁ h₂ => by
      rw [← h₁, ← h₂]
      exact (Lens.comp_fst_snd m).symm

/-- `LensCat` is cartesian monoidal for the categorical product `*` with unit `1`. -/
instance instCartesianMonoidalCategory : CartesianMonoidalCategory LensCat.{uA, uB} :=
  .ofChosenFiniteProducts ⟨_, isTerminalOne⟩ fun P Q => ⟨prodFan P Q, prodFanIsLimit P Q⟩

end LensCat

/-! ## The parallel product -/

-- The position and direction universes stay independent, as for `LensCat`.
set_option linter.checkUnivs false in
/-- The category of polynomials and lenses with the parallel product `⊗` as its monoidal
structure. -/
def TensorCat : Type max (uA + 1) (uB + 1) := PFunctor.{uA, uB}

namespace TensorCat

/-- Regard a polynomial functor as an object of `TensorCat`. -/
abbrev of (P : PFunctor.{uA, uB}) : TensorCat.{uA, uB} := P

/-- Regard an object of `TensorCat` as a polynomial functor. -/
abbrev as (P : TensorCat.{uA, uB}) : PFunctor.{uA, uB} := P

instance instCategory : Category TensorCat.{uA, uB} :=
  inferInstanceAs (Category LensCat.{uA, uB})

/-- A lens equivalence is an isomorphism in `TensorCat`. -/
abbrev isoOfEquiv {P Q : TensorCat.{uA, uB}} (e : P.as ≃ₗ Q.as) : P ≅ Q :=
  ⟨e.toLens, e.invLens, e.left_inv, e.right_inv⟩

instance instMonoidalCategoryStruct : MonoidalCategoryStruct TensorCat.{uA, uB} where
  tensorObj P Q := of (P.as ⊗ Q.as)
  whiskerLeft P _ _ g := Lens.id P.as ⊗ₗ g
  whiskerRight f Q := f ⊗ₗ Lens.id Q.as
  tensorHom f g := f ⊗ₗ g
  tensorUnit := of y
  associator P Q R := isoOfEquiv (Lens.Equiv.tensorAssoc (P := P.as) (Q := Q.as) (R := R.as))
  leftUnitor P := isoOfEquiv (Lens.Equiv.yTensor (P := P.as))
  rightUnitor P := isoOfEquiv (Lens.Equiv.tensorY (P := P.as))

/-- `(TensorCat, ⊗, y)` is a monoidal category; every law holds definitionally. -/
instance instMonoidalCategory : MonoidalCategory TensorCat.{uA, uB} :=
  .ofTensorHom
    (id_tensorHom_id := fun _ _ => rfl)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => rfl)
    (associator_naturality := fun _ _ _ => rfl)
    (leftUnitor_naturality := fun _ => rfl)
    (rightUnitor_naturality := fun _ => rfl)
    (pentagon := fun _ _ _ _ => rfl)
    (triangle := fun _ _ => rfl)

/-- `(TensorCat, ⊗, y)` is symmetric monoidal, with the braiding `tensorComm`. -/
instance instSymmetricCategory : SymmetricCategory TensorCat.{uA, uB} where
  braiding P Q := isoOfEquiv (Lens.Equiv.tensorComm P.as Q.as)
  braiding_naturality_right _ _ _ _ := rfl
  braiding_naturality_left _ _ := rfl
  hexagon_forward _ _ _ := rfl
  hexagon_reverse _ _ _ := rfl
  symmetry _ _ := rfl

end TensorCat

/-! ## The composition product -/

-- `CompCat.{u, v}` has positions in `max u v` and directions in `v`; the two parameters are
-- the independent position and direction universes of the polynomials it contains.
set_option linter.checkUnivs false in
/-- The category of polynomials and lenses with the composition product `◃` as its monoidal
structure, on the universe pair `{max u v, v}`, which `◃` preserves. -/
def CompCat : Type (max u v + 1) := PFunctor.{max u v, v}

namespace CompCat

/-- Regard a polynomial functor as an object of `CompCat`. -/
abbrev of (P : PFunctor.{max u v, v}) : CompCat.{u, v} := P

/-- Regard an object of `CompCat` as a polynomial functor. -/
abbrev as (P : CompCat.{u, v}) : PFunctor.{max u v, v} := P

instance instCategory : Category CompCat.{u, v} :=
  inferInstanceAs (Category LensCat.{max u v, v})

/-- A lens equivalence is an isomorphism in `CompCat`. -/
abbrev isoOfEquiv {P Q : CompCat.{u, v}} (e : P.as ≃ₗ Q.as) : P ≅ Q :=
  ⟨e.toLens, e.invLens, e.left_inv, e.right_inv⟩

instance instMonoidalCategoryStruct : MonoidalCategoryStruct CompCat.{u, v} where
  tensorObj P Q := of (P.as ◃ Q.as)
  whiskerLeft P _ _ g := Lens.id P.as ◃ₗ g
  whiskerRight f Q := f ◃ₗ Lens.id Q.as
  tensorHom f g := f ◃ₗ g
  tensorUnit := of y
  associator P Q R := isoOfEquiv (Lens.Equiv.compAssoc (P := P.as) (Q := Q.as) (R := R.as))
  leftUnitor P := isoOfEquiv (Lens.Equiv.yComp (P := P.as))
  rightUnitor P := isoOfEquiv (Lens.Equiv.compY (P := P.as))

/-- `(CompCat, ◃, y)` is a monoidal category; every law holds definitionally. -/
instance instMonoidalCategory : MonoidalCategory CompCat.{u, v} :=
  .ofTensorHom
    (id_tensorHom_id := fun _ _ => rfl)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => rfl)
    (associator_naturality := fun _ _ _ => rfl)
    (leftUnitor_naturality := fun _ => rfl)
    (rightUnitor_naturality := fun _ => rfl)
    (pentagon := fun _ _ _ _ => rfl)
    (triangle := fun _ _ => rfl)

end CompCat

end PFunctor
