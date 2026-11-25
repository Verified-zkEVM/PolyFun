/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Comonoid.StateTensor

/-!
# Regression tests for tensor products of state comonoids

The canaries pin the simp normal form of the isomorphism of a bijection and compute both maps
of the isomorphism of `Equiv.prodProdProdComm` at concrete states.
-/

@[expose] public section

universe u

namespace PFunctor
namespace ComonoidStateTensorTest

/-- The isomorphism of a bijection reads states through the bijection. -/
example {S T : Type u} (e : S ≃ T) (s : S) :
    Lens.State.get (Comonoid.stateEquivIso e).hom.toLens s = e s := by
  simp

/-- The isomorphism of `Equiv.prodProdProdComm` exchanges the middle states. -/
example :
    (Comonoid.stateEquivIso (_root_.Equiv.prodProdProdComm ℕ Bool ℤ Unit)).hom.toLens.toFunA
        ((1, true), (-1, ())) = ((1, -1), (true, ())) :=
  rfl

/-- Its direction map writes target states back through the inverse permutation. -/
example :
    (Comonoid.stateEquivIso (_root_.Equiv.prodProdProdComm ℕ Bool ℤ Unit)).hom.toLens.toFunB
        ((1, true), (-1, ())) ((2, -2), (false, ())) = ((2, false), (-2, ())) :=
  rfl

end ComonoidStateTensorTest
end PFunctor
