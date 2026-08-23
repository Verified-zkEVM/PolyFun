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

Following the treatment of `CategoryTheory.Cat`, `RelCat`, `KleisliCat`, and
`PartialFun` in Mathlib, each structure therefore gets its own carrier:

* `PFunctor.LensCat`, with `Lens` as morphisms. This is the category **Poly**
  of Spivak–Niu.
* `PFunctor.ChartCat`, with `Chart` as morphisms.

`LensCat.of` / `ChartCat.of` move a `PFunctor` into the chosen carrier, and
`LensCat.as` / `ChartCat.as` move back. Both are definitional, so a proof about
a polynomial functor transports to its categorical avatar by `rfl`.
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
def LensCat : Type max (uA + 1) (uB + 1) := PFunctor.{uA, uB}

namespace LensCat

/-- Regard a polynomial functor as an object of `LensCat`. -/
abbrev of (P : PFunctor.{uA, uB}) : LensCat.{uA, uB} := P

/-- Regard an object of `LensCat` as a polynomial functor. -/
abbrev as (P : LensCat.{uA, uB}) : PFunctor.{uA, uB} := P

instance instCategory : Category LensCat.{uA, uB} where
  Hom P Q := Lens P.as Q.as
  id P := Lens.id P.as
  comp f g := Lens.comp g f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_eq (P : LensCat.{uA, uB}) : 𝟙 P = Lens.id P.as := rfl

@[simp] theorem comp_eq {P Q R : LensCat.{uA, uB}} (f : P ⟶ Q) (g : Q ⟶ R) :
    f ≫ g = Lens.comp g f := rfl

end LensCat

/-! ## Charts -/

-- Independent position and direction universes, as for `LensCat` above.
set_option linter.checkUnivs false in
/-- `PFunctor` regarded as the category whose morphisms are charts. -/
def ChartCat : Type max (uA + 1) (uB + 1) := PFunctor.{uA, uB}

namespace ChartCat

/-- Regard a polynomial functor as an object of `ChartCat`. -/
abbrev of (P : PFunctor.{uA, uB}) : ChartCat.{uA, uB} := P

/-- Regard an object of `ChartCat` as a polynomial functor. -/
abbrev as (P : ChartCat.{uA, uB}) : PFunctor.{uA, uB} := P

instance instCategory : Category ChartCat.{uA, uB} where
  Hom P Q := Chart P.as Q.as
  id P := Chart.id P.as
  comp f g := Chart.comp g f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_eq (P : ChartCat.{uA, uB}) : 𝟙 P = Chart.id P.as := rfl

@[simp] theorem comp_eq {P Q R : ChartCat.{uA, uB}} (f : P ⟶ Q) (g : Q ⟶ R) :
    f ≫ g = Chart.comp g f := rfl

end ChartCat

end PFunctor
