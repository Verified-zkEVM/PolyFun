/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Lens.BangWSeely

/-!
# Examples for weakening, contraction and the Seely isomorphisms of `bangW`

The commutative comonoid instance on `TensorCat.of (bangW S P)` is found by instance search and
its comultiplication is contraction; weakening, contraction, the Seely isomorphism and the
comparison `bang P ≃ₗ bangW ℕ P` compute on a polynomial with one position and two directions.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.Lens.BangWSeely

open _root_.PFunctor CategoryTheory

/-- A polynomial with one position and two directions. -/
abbrev two : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

example (P : PFunctor.{0, 0}) : IsCommComonObj (TensorCat.of (bangW ℕ P)) := inferInstance

example (P : PFunctor.{0, 0}) : (ComonObj.comul : TensorCat.of (bangW ℚ≥0 P) ⟶ _) =
    Lens.bangWContr ℚ≥0 P := rfl

example (f g : Bool →₀ ℕ) : (Lens.bangWContr ℕ two).toFunB () (f, g) = f + g := rfl

example : (Lens.bangWWeak ℕ two).toFunB () PUnit.unit = 0 := rfl

example :
    (Lens.Equiv.seelyW ℕ two two).invLens.toFunB ((), ())
        (Finsupp.single (Sum.inl true) 2) = (Finsupp.single true 2, 0) := by
  simp [Lens.Equiv.seelyW]
  rfl

example :
    (Lens.Equiv.seelyW ℕ two two).toLens.toFunB ((), ()) (Finsupp.single true 2, 0) =
      Finsupp.single (Sum.inl true) 2 := by
  simp [Lens.Equiv.seelyW]

example :
    (Lens.Equiv.bangEquivBangW two).toLens.toFunB () (Finsupp.single true 2) =
      {true, true} := by
  simp only [Lens.Equiv.bangEquivBangW, Finsupp.toMultiset_single]
  decide

example (m : Multiset Bool) :
    (Lens.Equiv.bangEquivBangW two).toLens.toFunB ()
        ((Lens.Equiv.bangEquivBangW two).invLens.toFunB () m) = m := by
  simp [Lens.Equiv.bangEquivBangW]

end PolyFunTest.PFunctor.Lens.BangWSeely
