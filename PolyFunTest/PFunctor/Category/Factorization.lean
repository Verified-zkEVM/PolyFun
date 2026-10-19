/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Category.Factorization

/-!
# Consuming the vertical/cartesian morphism properties

These examples use Mathlib's lifting, factorization and composition API on `LensCat` through
`LensCat.vertical` and `LensCat.cartesian`, and check that the heterogeneous statements of
`Lens/Factorization.lean` still apply across independent universes.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.Category.Factorization

open CategoryTheory MorphismProperty _root_.PFunctor

/-! ## Mathlib's API on `LensCat` -/

example {P Q R S : LensCat.{0, 0}} {v : P ⟶ Q} {f : P ⟶ R} {c : R ⟶ S} {g : Q ⟶ S}
    (hv : Lens.IsVertical v) (hc : Lens.IsCartesian c) (sq : CommSq f v c g) :
    ∃ l : Q ⟶ R, v ≫ l = f ∧ l ≫ c = g := by
  have := LensCat.hasLiftingProperty v c hv hc
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

example {P Q R : LensCat.{0, 0}} (f : P ⟶ Q) (g : Q ⟶ R)
    (hf : LensCat.cartesian f) (hg : LensCat.cartesian g) : LensCat.cartesian (f ≫ g) :=
  LensCat.cartesian.comp_mem f g hf hg

example {P Q : LensCat.{0, 0}} (f : P ⟶ Q) :
    (factorizationData LensCat.vertical LensCat.cartesian f).i ≫
      (factorizationData LensCat.vertical LensCat.cartesian f).p = f :=
  (factorizationData LensCat.vertical LensCat.cartesian f).fac

example {P Q : LensCat.{0, 0}} (e : P.toPFunctor ≃ₗ Q.toPFunctor) :
    Lens.IsVertical e.toLens ∧ Lens.IsCartesian e.toLens :=
  (LensCat.isIso_iff_isVertical_and_isCartesian (LensCat.Iso.mk e).hom).mp
    (LensCat.Iso.mk e).isIso_hom

example {P Q : LensCat.{0, 0}} (f : P ⟶ Q) (hv : Lens.IsVertical f) (hc : Lens.IsCartesian f) :
    isomorphisms LensCat f := by
  rw [LensCat.isomorphisms_eq_vertical_inf_cartesian]
  exact ⟨hv, hc⟩

/-! ## The general statements at independent universes -/

example {P : PFunctor.{0, 1}} {Q : PFunctor.{1, 0}} {R : PFunctor.{2, 0}} {S : PFunctor.{0, 2}}
    (v : Lens P Q) (f : Lens P R) (c : Lens R S) (g : Lens Q S)
    (hv : v.IsVertical) (hc : c.IsCartesian) (comm : c ∘ₗ f = g ∘ₗ v) :
    Nonempty (Lens.DiagonalFiller v f c g) :=
  Lens.nonempty_diagonalFiller v f c g hv hc comm

end PolyFunTest.PFunctor.Category.Factorization
