/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Category.Monoidal
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Consuming the monoidal structures on lenses

These examples use theorems and tactics that Mathlib derives from the `CartesianMonoidalCategory`
instance on `LensCat`, the `SymmetricCategory` instance on `TensorCat`, and the
`MonoidalCategory` instance on `CompCat`:

* `unitors_equal`, a consequence of coherence;
* `SymmetricCategory.braiding_swap_eq_inv_braiding`;
* `CartesianMonoidalCategory.lift_fst` and `HasFiniteProducts`;
* the `monoidal` coherence tactic.

They also check that the Mathlib structure is the PolyFun one definitionally, and that the
carriers, being one-field structures, keep Mathlib's monoidal `⊗` unambiguous when PolyFun's scoped
notation is open.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.Category.Monoidal

open CategoryTheory MonoidalCategory Limits

/-! ## `LensCat` is cartesian monoidal -/

example : HasFiniteProducts _root_.PFunctor.LensCat.{0, 0} := inferInstance

example {P Q R : _root_.PFunctor.LensCat.{0, 0}} (f : P ⟶ Q) (g : P ⟶ R) :
    CartesianMonoidalCategory.lift f g ≫ CartesianMonoidalCategory.fst Q R = f :=
  CartesianMonoidalCategory.lift_fst f g

/-- The monoidal product of `LensCat` is the polynomial product `*`. -/
example (P Q : _root_.PFunctor.LensCat.{0, 0}) :
    P ⊗ Q = _root_.PFunctor.LensCat.of (_root_.PFunctor.prod P.toPFunctor Q.toPFunctor) := rfl

/-! ## `TensorCat` is symmetric monoidal -/

example : (λ_ (𝟙_ _root_.PFunctor.TensorCat.{0, 0})).hom =
    (ρ_ (𝟙_ _root_.PFunctor.TensorCat.{0, 0})).hom :=
  unitors_equal

example (P Q : _root_.PFunctor.TensorCat.{0, 0}) : (β_ Q P).hom = (β_ P Q).inv :=
  SymmetricCategory.braiding_swap_eq_inv_braiding P Q

example (P Q R S : _root_.PFunctor.TensorCat.{0, 0}) :
    (α_ P Q (R ⊗ S)).inv ≫ (α_ (P ⊗ Q) R S).inv =
      (P ◁ (α_ Q R S).inv) ≫ (α_ P (Q ⊗ R) S).inv ≫ ((α_ P Q R).inv ▷ S) := by
  monoidal

/-- The associator of `TensorCat` is the lens `tensorAssoc`. -/
example (P Q R : _root_.PFunctor.TensorCat.{0, 0}) :
    (α_ P Q R).hom = (_root_.PFunctor.Lens.Equiv.tensorAssoc (P := P.toPFunctor) (Q := Q.toPFunctor)
      (R := R.toPFunctor)).toLens := rfl

/-! ## `CompCat` is monoidal for the composition product -/

example : (λ_ (𝟙_ _root_.PFunctor.CompCat.{0, 0})).hom =
    (ρ_ (𝟙_ _root_.PFunctor.CompCat.{0, 0})).hom :=
  unitors_equal

example (P Q R S : _root_.PFunctor.CompCat.{0, 0}) :
    (α_ P Q (R ⊗ S)).inv ≫ (α_ (P ⊗ Q) R S).inv =
      (P ◁ (α_ Q R S).inv) ≫ (α_ P (Q ⊗ R) S).inv ≫ ((α_ P Q R).inv ▷ S) := by
  monoidal

/-- The monoidal product of `CompCat` is the composition product `◃`. -/
example (P Q : _root_.PFunctor.CompCat.{0, 0}) :
    P ⊗ Q = _root_.PFunctor.CompCat.of (_root_.PFunctor.comp P.toPFunctor Q.toPFunctor) := rfl

/-! ## Notation -/

section ScopedNotation

open scoped _root_.PFunctor

/-- With PolyFun's scoped notation open, `⊗` on carrier objects is Mathlib's monoidal product,
while `⊗` on polynomials is the parallel product. -/
example (P Q : _root_.PFunctor.TensorCat.{0, 0}) :
    (P ⊗ Q).toPFunctor = P.toPFunctor ⊗ Q.toPFunctor := rfl

example (P Q : _root_.PFunctor.CompCat.{0, 0}) :
    (P ⊗ Q).toPFunctor = P.toPFunctor ◃ Q.toPFunctor := rfl

end ScopedNotation

/-! ## Composition powers and the action of `◃` -/

/-- The monomial `Bool y^ Bool`. -/
abbrev boolMonomial : _root_.PFunctor.{0, 0} := _root_.PFunctor.monomial Bool Bool

/-- The split `P ◃^ (1 + 1) ≃ₗ P ◃^ 1 ◃ P ◃^ 1` has the reassociation as inverse. -/
example (x : (_root_.PFunctor.compNth boolMonomial 2).A) :
    (_root_.PFunctor.Lens.Equiv.compNthAdd boolMonomial 1 1).invLens.toFunA
      ((_root_.PFunctor.Lens.Equiv.compNthAdd boolMonomial 1 1).toLens.toFunA x) = x :=
  congrArg (fun l => _root_.PFunctor.Lens.toFunA l x)
    (_root_.PFunctor.Lens.Equiv.compNthAdd boolMonomial 1 1).left_inv

end PolyFunTest.PFunctor.Category.Monoidal
