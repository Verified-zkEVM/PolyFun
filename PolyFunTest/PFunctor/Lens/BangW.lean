/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.BangW

/-!
# Finitely supported weights on lens directions

The public action uses additive weights on arbitrary direction types. The examples collect
weights from infinitely many possible directions into a single slot.
-/

public section

namespace PolyFunTest.PFunctor.Lens.BangW

open _root_.PFunctor

example (S : Type*) [Zero S] (P : PFunctor) (a : P.A) : (bangW S P).B a = (P.B a →₀ S) := rfl

example (S : Type*) [AddCommMonoid S] (P : LensCat) :
    (LensCat.bangWFunctor S).obj P = LensCat.of (bangW S P.toPFunctor) := rfl

example {S T : Type*} [AddCommMonoid S] [AddCommMonoid T] {P Q : PFunctor}
    (l : Lens P Q) (x : P.Obj (S →+ T)) (w : Q.B (l.toFunA x.fst) →₀ S) :
    Finsupp.liftAddHom x.snd ((Lens.bangWMap l).toFunB x.fst w) =
      Finsupp.liftAddHom (l.mapObj x).snd w :=
  Lens.liftAddHom_bangWMap l x w

/-- Every output coordinate reads input slot zero. -/
def readZero : Lens (purePower ℕ) (purePower ℕ) :=
  id ⇆ fun _ _ => 0

private theorem collectTwo {S : Type*} [AddCommMonoid S] (u v : S) :
    (Lens.bangWMap readZero).toFunB PUnit.unit (Finsupp.single 17 u + Finsupp.single 91 v) =
      Finsupp.single 0 (u + v) := by
  simp [Lens.bangWMap, readZero, Finsupp.mapDomain_add, Finsupp.single_add]

example :
    (Lens.bangWMap readZero).toFunB PUnit.unit
      (Finsupp.single 17 (3 : ℤ) + Finsupp.single 91 (-3)) = 0 := by
  rw [collectTwo]
  simp

end PolyFunTest.PFunctor.Lens.BangW
