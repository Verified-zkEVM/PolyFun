/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Comonoid

/-!
# Examples for comonoids in `(Poly, ◃, y)`

Regression tests: the state comonoid `S y^S` satisfies the comonoid laws (by
construction), is a state system, and its `n`-fold comultiplication `δ^{(n)}`
recovers the counit at `n = 0` and unfolds as expected.
-/

@[expose] public section

universe u v

namespace PFunctor

open CategoryTheory

variable {S : Type u}

/-- Retrofunctors form a category-shaped API with identity and composition. -/
example (C : Comonoid.{u, v}) : Comonoid.Hom C C := Comonoid.Hom.id C

example {C D E : Comonoid.{u, v}} (f : Comonoid.Hom C D)
    (g : Comonoid.Hom D E) :
    (f.comp g).toLens = g.toLens ∘ₗ f.toLens := rfl

example {C D E : Comonoid.{u, v}} (f : C ⟶ D) (g : D ⟶ E) :
    (f ≫ g).toLens = g.toLens ∘ₗ f.toLens := rfl

/-- Retrofunctors preserve the complete finite comultiplication ladder. -/
example {C D : Comonoid.{u, v}} (f : Comonoid.Hom C D) (n : ℕ) :
    D.comultN n ∘ₗ f.toLens = f.toLens.compNthMap n ∘ₗ C.comultN n :=
  f.map_comultN n

/-- Retrofunctors between state comonoids are precisely very-well-behaved
state lenses; the first projection supplies a concrete nontrivial example. -/
example {S T : Type u} :
    Comonoid.Hom (stateComonoid (S × T)) (stateComonoid S) :=
  Comonoid.Hom.ofStateLens (Lens.State.fst S T)

example {S T : Type u}
    (F : Comonoid.Hom (stateComonoid S) (stateComonoid T)) :
    Lens.State.IsVeryWellBehaved
      (show Lens.State S T from F.toLens) :=
  Comonoid.Hom.stateLens_isVeryWellBehaved F

/-- The state-comonoid equivalence has projection and round-trip simp laws. -/
example {S T : Type u} (L : Lens.State S T) [L.IsVeryWellBehaved] :
    (Comonoid.Hom.ofStateLens L).toLens = L := by simp

example {S T : Type u}
    (F : Comonoid.Hom (stateComonoid S) (stateComonoid T)) :
    (Comonoid.Hom.stateLensEquiv.symm (Comonoid.Hom.stateLensEquiv F)) = F := by
  simp

/-- Comonoids support independent position and direction universes. -/
example (C : Comonoid.{u, v}) : C.comultN 0 = C.counit := rfl

/-- The state comonoid's comultiplication is the transition lens. -/
example : (stateComonoid S).comult = Lens.fixState := rfl

/-- The state comonoid is a state system (Spivak–Niu Ex 7.22). -/
example : (stateComonoid S).IsStateSystem := isStateSystem_stateComonoid S

/-- `δ^{(0)}` is the counit. -/
example : (stateComonoid S).comultN 0 = (stateComonoid S).counit := rfl

/-- `δ^{(1)}` unfolds through the counit. -/
example :
    (stateComonoid S).comultN 1
      = (Lens.id _ ◃ₗ (stateComonoid S).counit) ∘ₗ Lens.fixState := rfl

/-- `δ^{(n+1)}` unfolds by one composition step. -/
example (n : ℕ) :
    (stateComonoid S).comultN (n + 1)
      = (Lens.id _ ◃ₗ (stateComonoid S).comultN n) ∘ₗ Lens.fixState := rfl

/-- A fully concrete instance: `Bool` states. -/
example : (stateComonoid Bool).IsStateSystem := isStateSystem_stateComonoid Bool

end PFunctor
