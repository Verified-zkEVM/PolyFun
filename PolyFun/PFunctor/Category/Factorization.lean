/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Category.Monoidal
public import PolyFun.PFunctor.Lens.Factorization
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Vertical and cartesian lenses as morphism properties

A lens is *vertical* when it is bijective on positions and *cartesian* when it is bijective on
every direction fiber (Niu–Spivak Def 5.51, p. 158). `Lens/Factorization.lean` shows that these
two classes form an orthogonal factorization system (Prop 5.52, p. 159), for lenses between
polynomials in independent universe pairs. This file restates the single-pair case in Mathlib's
vocabulary on `LensCat.{uA, uB}`:

* `LensCat.vertical` and `LensCat.cartesian` are multiplicative `MorphismProperty`s;
* every lens factors as a vertical lens followed by a cartesian one (`HasFactorization`);
* a `Lens.DiagonalFiller` is a `CommSq.LiftStruct` (`diagonalFillerEquivLiftStruct`), so a
  vertical lens has the left lifting property against a cartesian one
  (`vertical_le_llp_cartesian`, `cartesian_le_rlp_vertical`);
* the isomorphisms of `LensCat` are exactly the lenses that are both vertical and cartesian
  (`isomorphisms_eq_vertical_inf_cartesian`).

A `MorphismProperty` lives in a single category, so every statement here fixes one universe
pair. The statements in `Lens/Factorization.lean` remain the general form.
-/

@[expose] public section

universe uA uB

open CategoryTheory MorphismProperty

namespace PFunctor

namespace LensCat

/-- Vertical lenses, bijective on positions, as a property of `LensCat` morphisms. -/
def vertical : MorphismProperty LensCat.{uA, uB} := fun _ _ f => Lens.IsVertical f

/-- Cartesian lenses, bijective on every direction fiber, as a property of `LensCat`
morphisms. -/
def cartesian : MorphismProperty LensCat.{uA, uB} := fun _ _ f => Lens.IsCartesian f

@[simp] theorem vertical_iff {P Q : LensCat.{uA, uB}} (f : P ⟶ Q) :
    vertical f ↔ Lens.IsVertical f := Iff.rfl

@[simp] theorem cartesian_iff {P Q : LensCat.{uA, uB}} (f : P ⟶ Q) :
    cartesian f ↔ Lens.IsCartesian f := Iff.rfl

instance : vertical.{uA, uB}.IsMultiplicative where
  id_mem P := Lens.IsVertical.id P.toPFunctor
  comp_mem _ _ hf hg := Lens.IsVertical.comp hg hf

instance : cartesian.{uA, uB}.IsMultiplicative where
  id_mem P := Lens.IsCartesian.id P.toPFunctor
  comp_mem _ _ hf hg := Lens.IsCartesian.comp hg hf

/-- Every lens factors through `Lens.factorMid` as a vertical lens followed by a cartesian
one. -/
instance : HasFactorization vertical.{uA, uB} cartesian.{uA, uB} where
  nonempty_mapFactorizationData f := ⟨{
    Z := of (Lens.factorMid f)
    i := Lens.factorVert f
    p := Lens.factorCart f
    fac := Lens.factorCart_comp_factorVert f
    hi := Lens.factorVert_isVertical f
    hp := Lens.factorCart_isCartesian f }⟩

/-- A diagonal filler of a commutative square of lenses is a lift of the same square in
`LensCat`. Both triangle equations are the same equations of lenses. -/
def diagonalFillerEquivLiftStruct {P Q R S : LensCat.{uA, uB}}
    {v : P ⟶ Q} {f : P ⟶ R} {c : R ⟶ S} {g : Q ⟶ S} (sq : CommSq f v c g) :
    Lens.DiagonalFiller v f c g ≃ sq.LiftStruct where
  toFun d := ⟨d.diagonal, d.comp_left, d.comp_right⟩
  invFun l := ⟨l.l, l.fac_left, l.fac_right⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A vertical lens has the left lifting property against a cartesian lens. -/
theorem hasLiftingProperty {P Q R S : LensCat.{uA, uB}} (v : P ⟶ Q) (c : R ⟶ S)
    (hv : Lens.IsVertical v) (hc : Lens.IsCartesian c) : HasLiftingProperty v c where
  sq_hasLift sq :=
    ⟨⟨diagonalFillerEquivLiftStruct sq (Lens.verticalCartesianFiller v _ c _ hv hc sq.w)⟩⟩

theorem vertical_le_llp_cartesian : vertical.{uA, uB} ≤ cartesian.llp :=
  fun _ _ _ hv _ _ _ hc => hasLiftingProperty _ _ hv hc

theorem cartesian_le_rlp_vertical : cartesian.{uA, uB} ≤ vertical.rlp :=
  fun _ _ _ hc _ _ _ hv => hasLiftingProperty _ _ hv hc

/-- A lens is an isomorphism in `LensCat` exactly when it is vertical and cartesian. -/
theorem isIso_iff_isVertical_and_isCartesian {P Q : LensCat.{uA, uB}} (f : P ⟶ Q) :
    IsIso f ↔ Lens.IsVertical f ∧ Lens.IsCartesian f := by
  rw [← Lens.exists_equiv_toLens_iff]
  constructor
  · intro _
    exact ⟨Iso.toLensEquiv (asIso f), rfl⟩
  · rintro ⟨e, rfl⟩
    exact (Iso.mk e).isIso_hom

theorem isomorphisms_eq_vertical_inf_cartesian :
    isomorphisms LensCat.{uA, uB} = vertical ⊓ cartesian := by
  ext _ _ f
  exact isIso_iff_isVertical_and_isCartesian f

end LensCat

end PFunctor
