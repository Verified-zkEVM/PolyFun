/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Lens.DirMonad

/-!
# Examples for the comonad of a monad on directions

Regression tests for `PFunctor/Lens/DirMonad.lean`: co-Kleisli composites of lenses with
`Option`-valued backward maps, the comonad at `Option`, and the comparison with the multiset
exponential.
-/

@[expose] public section

namespace PolyFunTest.PFunctor.DirMonad

open CategoryTheory _root_.PFunctor

/-- Positions and directions both `Bool`. -/
abbrev qBool : PFunctor.{0, 0} := ⟨Bool, fun _ => Bool⟩

/-- A lens with a partial backward map: the direction `true` demands `false`, and `false` demands
nothing. -/
def partialLens : Lens (dirMonad Option qBool) qBool :=
  id ⇆ fun _ d => if d then some false else none

/-- A lens with a total backward map that negates the direction. -/
def negLens : Lens (dirMonad Option qBool) qBool :=
  id ⇆ fun _ d => some (!d)

example : (partialLens ∘ₗ Lens.dirMonadMap negLens ∘ₗ Lens.dirMonadComult Option qBool).toFunB
    true true = some true := by
  rw [Lens.dirMonad_cokleisli_comp]
  rfl

example : (partialLens ∘ₗ Lens.dirMonadMap negLens ∘ₗ Lens.dirMonadComult Option qBool).toFunB
    true false = none := rfl

example : Comonad LensCat.{0, 0} := LensCat.dirMonadComonad Option

example (X : LensCat.{0, 0}) :
    (LensCat.dirMonadMultisetIso.hom.app X).toFunA = id := rfl

end PolyFunTest.PFunctor.DirMonad
