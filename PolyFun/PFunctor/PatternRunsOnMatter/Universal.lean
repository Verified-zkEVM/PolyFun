/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.PatternRunsOnMatter.Basic
public import PolyFun.PFunctor.Cofree.Universal
public import PolyFun.PFunctor.Free.Universal
public import PolyFun.PFunctor.SubstMonoid.Convolution

/-!
# Universal characterization of pattern running

Libkind--Spivak construct the interaction

`FreeP P ⊗ CofreeP Q ⇆ FreeP (P ⊗ Q)`

by currying the one-generator synchronized step, extending it from the free
substitution monoid into the convolution monoid
`[CofreeP Q, FreeP (P ⊗ Q)]`, and uncurrying. This file implements that
construction as `xi` and proves that it is exactly the independently
executable `FreeP.runOn`.

The universal construction retains independent position universes and the two
universes of `Q`. Its only constraint is that `P`'s direction universe is
`max qA qB`: `CofreeP Q` raises both carrier universes to that maximum, and
the homogeneous `SubstMonoid.Hom`/`FreeP.extend` boundary requires the free
source and convolution target to share it. The executable `runOn` itself has
no such constraint. No resizing or stronger square-universe restriction is
hidden here.

## Reference

* Libkind and Spivak, *Pattern Runs on Matter: The Free Monad Monad as a
  Module over the Cofree Comonad Comonad*, Section 3.2.
-/

@[expose] public section

universe pA pA' pB qA qB qA' qB' u

namespace PFunctor
namespace FreeP

/-- The one-generator synchronized step, curried into the convolution
carrier. -/
def xiGenerator (P : PFunctor.{pA, max qA qB})
    (Q : PFunctor.{qA, qB}) :
    Lens P (SubstMonoid.convolution (CofreeP.comonoid Q)
      (FreeP.substMonoid (P ⊗ Q))).carrier :=
  Lens.curry (FreeP.generator (P ⊗ Q) ∘ₗ
    (Lens.id P ⊗ₗ CofreeP.cogenerator Q))

/-- The substitution-monoid homomorphism induced from the synchronized
generator by the free universal property. -/
def xiHom (P : PFunctor.{pA, max qA qB})
    (Q : PFunctor.{qA, qB}) :
    SubstMonoid.Hom (FreeP.substMonoid P)
      (SubstMonoid.convolution (CofreeP.comonoid Q)
        (FreeP.substMonoid (P ⊗ Q))) :=
  FreeP.extend _ (xiGenerator P Q)

/-- The Libkind--Spivak interaction obtained by uncurrying the universal
substitution-monoid homomorphism. -/
def xi (P : PFunctor.{pA, max qA qB})
    (Q : PFunctor.{qA, qB}) :
    Lens (FreeP P ⊗ CofreeP Q) (FreeP (P ⊗ Q)) :=
  Lens.uncurry (xiHom P Q).toLens

/-- Running a one-node pattern is exactly the synchronized generator step.
This operational equation is fully heterogeneous. -/
theorem runOn_comp_generator (P : PFunctor.{pA, pB})
    (Q : PFunctor.{qA, qB}) :
    runOn P Q ∘ₗ
        (FreeP.generator P ⊗ₗ Lens.id (CofreeP Q)) =
      FreeP.generator (P ⊗ Q) ∘ₗ
        (Lens.id P ⊗ₗ CofreeP.cogenerator Q) := by
  rfl

/-- The universal interaction restricts to the synchronized generator step. -/
theorem xi_comp_generator (P : PFunctor.{pA, max qA qB})
    (Q : PFunctor.{qA, qB}) :
    xi P Q ∘ₗ
        (FreeP.generator P ⊗ₗ Lens.id (CofreeP Q)) =
      FreeP.generator (P ⊗ Q) ∘ₗ
        (Lens.id P ⊗ₗ CofreeP.cogenerator Q) := by
  rfl

/-- Strong operational characterization of the universal interaction.
It identifies the complete output object, including the backward map from
output paths to source pattern paths and matter vertices. -/
theorem runObj_eq_xi_mapObj (P : PFunctor.{pA, max qA qB})
    (Q : PFunctor.{qA, qB})
    (pattern : (FreeP P).A) (matter : (CofreeP Q).A) :
    runObj pattern matter =
      Lens.mapObj (xi P Q)
        (⟨(pattern, matter), id⟩ :
          (FreeP P ⊗ CofreeP Q).Obj
            (FreeM.Path pattern × M.Vertex matter)) := by
  induction pattern generalizing matter with
  | pure value =>
      cases value
      rfl
  | liftBind a rest ih =>
      let prepend (direction : P.B a × Q.B (M.head matter)) :
          FreeM.Path (rest direction.1) ×
              M.Vertex (M.children matter direction.2) →
            FreeM.Path (FreeM.liftBind a rest) × M.Vertex matter :=
        fun pulled =>
          ⟨FreeM.Path.cons a rest direction.1 pulled.1,
            M.Vertex.child direction.2 pulled.2⟩
      let middle : (FreeP (P ⊗ Q)).Obj
          (FreeM.Path (FreeM.liftBind a rest) × M.Vertex matter) :=
        FreeP.node (P := P ⊗ Q) (a, M.head matter) fun direction =>
          FreeP.relabel (prepend direction)
            (Lens.mapObj (xi P Q)
              (⟨(rest direction.1,
                  M.children matter direction.2), id⟩ :
                (FreeP P ⊗ CofreeP Q).Obj
                  (FreeM.Path (rest direction.1) ×
                    M.Vertex (M.children matter direction.2))))
      have hfirst : runObj (FreeM.liftBind a rest) matter = middle := by
        change FreeP.node (P := P ⊗ Q) (a, M.head matter) _ =
          FreeP.node (P := P ⊗ Q) (a, M.head matter) _
        congr 1
        funext direction
        exact congrArg
          (FreeP.relabel (prepend direction))
          (ih direction.1 (M.children matter direction.2))
      have hsecond : middle =
          Lens.mapObj (xi P Q)
            (⟨(FreeM.liftBind a rest, matter), id⟩ :
              (FreeP P ⊗ CofreeP Q).Obj
                (FreeM.Path (FreeM.liftBind a rest) ×
                  M.Vertex matter)) := by
        rfl
      exact hfirst.trans hsecond

/-- The executable synchronized traversal is exactly the paper's
internal-hom/convolution construction. -/
theorem runOn_eq_xi (P : PFunctor.{pA, max qA qB})
    (Q : PFunctor.{qA, qB}) :
    runOn P Q = xi P Q := by
  let hA : ∀ input,
      (runOn P Q).toFunA input = (xi P Q).toFunA input :=
    fun input =>
      congrArg Sigma.fst (runObj_eq_xi_mapObj P Q input.1 input.2)
  refine Lens.ext _ _ hA ?_
  intro input
  rcases input with ⟨pattern, matter⟩
  apply eq_of_heq
  have hraw : (runOn P Q).toFunB (pattern, matter) ≍
      (xi P Q).toFunB (pattern, matter) :=
    (Sigma.ext_iff.mp (runObj_eq_xi_mapObj P Q pattern matter)).2
  have hcast : (hA (pattern, matter) ▸
      (xi P Q).toFunB (pattern, matter)) ≍
      (xi P Q).toFunB (pattern, matter) :=
    eqRec_heq_self _ _
  exact hraw.trans hcast.symm

/-- The universal interaction is natural in both generators at the minimal
direction-universe ceilings required by its convolution construction. -/
theorem xi_natural
    {P : PFunctor.{pA, max qA qB}}
    {P' : PFunctor.{pA', max qA' qB'}}
    {Q : PFunctor.{qA, qB}} {Q' : PFunctor.{qA', qB'}}
    (f : Lens P P') (g : Lens Q Q') :
    xi P' Q' ∘ₗ (FreeP.map f ⊗ₗ CofreeP.map g) =
      FreeP.map (f ⊗ₗ g) ∘ₗ xi P Q := by
  rw [← runOn_eq_xi P' Q', ← runOn_eq_xi P Q]
  exact runOn_natural f g

end FreeP
end PFunctor
