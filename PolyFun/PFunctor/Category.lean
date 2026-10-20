/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Lens.Basic
public import PolyFun.PFunctor.Chart.Basic
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Categories of Polynomial Functors

Polynomial functors carry two different categorical structures on the *same*
objects: lenses and charts. A `Category` instance is keyed on its object type,
so both cannot be registered on `PFunctor` itself — instance search would pick
one arbitrarily and `≫` / `𝟙` would silently mean whichever won.

Each structure therefore gets its own carrier, a one-field structure over `PFunctor` in the
style of Mathlib's `CategoryTheory.Core`, so that instances and notation on a carrier do not
unfold to `PFunctor`:

* `PFunctor.LensCat`, with `Lens` as morphisms. This is the category **Poly**
  of Niu–Spivak.
* `PFunctor.ChartCat`, with `Chart` as morphisms.

The constructor `LensCat.of` / `ChartCat.of` moves a `PFunctor` into the chosen carrier, and the
projection `toPFunctor` moves back. They are mutually inverse by `rfl`, so a proof about a
polynomial functor transports to its categorical avatar by `rfl`.
`PFunctor/Category/Monoidal.lean` adds the cartesian structure on `LensCat` and the
carriers `TensorCat` and `CompCat` for the parallel and composition products.
-/

@[expose] public section

universe u v uA uB

open CategoryTheory

namespace PFunctor

/-! ## Lenses -/

-- The position and direction universes stay independent, exactly as they do
-- for `PFunctor` itself; the carrier only ever mentions them jointly.
set_option linter.checkUnivs false in
/-- `PFunctor` regarded as the category whose morphisms are lenses: the
category **Poly**. -/
structure LensCat : Type max (uA + 1) (uB + 1) where
  /-- Regard a polynomial functor as an object of `LensCat`. -/
  of ::
  /-- The polynomial functor underlying an object of `LensCat`. -/
  toPFunctor : PFunctor.{uA, uB}

namespace LensCat

@[reducible, deprecated (since := "2026-10-19")] alias as := toPFunctor

instance instCategory : Category LensCat.{uA, uB} where
  Hom P Q := Lens P.toPFunctor Q.toPFunctor
  id P := Lens.id P.toPFunctor
  comp f g := Lens.comp g f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_eq (P : LensCat.{uA, uB}) : 𝟙 P = Lens.id P.toPFunctor := rfl

@[simp] theorem comp_eq {P Q R : LensCat.{uA, uB}} (f : P ⟶ Q) (g : Q ⟶ R) :
    f ≫ g = Lens.comp g f := rfl

end LensCat

/-! ## Charts -/

-- Independent position and direction universes, as for `LensCat` above.
set_option linter.checkUnivs false in
/-- `PFunctor` regarded as the category whose morphisms are charts. -/
structure ChartCat : Type max (uA + 1) (uB + 1) where
  /-- Regard a polynomial functor as an object of `ChartCat`. -/
  of ::
  /-- The polynomial functor underlying an object of `ChartCat`. -/
  toPFunctor : PFunctor.{uA, uB}

namespace ChartCat

@[reducible, deprecated (since := "2026-10-19")] alias as := toPFunctor

instance instCategory : Category ChartCat.{uA, uB} where
  Hom P Q := Chart P.toPFunctor Q.toPFunctor
  id P := Chart.id P.toPFunctor
  comp f g := Chart.comp g f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_eq (P : ChartCat.{uA, uB}) : 𝟙 P = Chart.id P.toPFunctor := rfl

@[simp] theorem comp_eq {P Q R : ChartCat.{uA, uB}} (f : P ⟶ Q) (g : Q ⟶ R) :
    f ≫ g = Chart.comp g f := rfl

end ChartCat

end PFunctor
