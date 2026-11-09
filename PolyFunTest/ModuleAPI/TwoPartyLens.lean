/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.TwoParty.Lens.Iterate
public import PolyFun.Interaction.TwoParty.Lens.PublicCoin
public import PolyFun.Interaction.TwoParty.Lens.Swap

/-!
# Ordinary-import lens interaction client

Positions and source branches have independent universes. In particular, positions can contain
large types without increasing the move, output, or execution-monad universe.
-/

public section

universe u v w t
namespace PolyFunTest.ModuleAPI.TwoPartyLens
open PFunctor
open PFunctor.FreeM (PathAlong Path projectPathAlong)
open Interaction.TwoParty.Lens

variable {P : PFunctor.{v, w}} {l : Lens P rolePoly.{u}}
variable {m : Type u → Type u} [Monad m] [LawfulMonad m]

example (s : FreeM P PUnit.{u + 1}) {A B : PathAlong l s → Type u}
    (p : Focal l m s A) (c : Counterpart l m s B) :
    m ((tr : PathAlong l s) × A tr × B tr) := run s p c

example (s : FreeM P PUnit.{u + 1}) (tr : PathAlong (Lens.id P) s) :
    projectPathAlong (Lens.id P) s tr = tr := FreeM.projectPathAlong_id s tr

/-- Positions inhabit a universe strictly larger than moves. -/
@[expose] def largePositions : PFunctor.{u + 2, u} :=
  ⟨Type (u + 1), fun _ => PUnit.{u + 1}⟩

/-- Source positions carry types, while the monad still runs in `Type u`. -/
example (s : FreeM largePositions.{u} PUnit.{u + 1})
    (p : Focal (ofRoles (fun _ => .sender)) Id s (fun _ => PUnit.{u + 1}))
    (c : Counterpart (ofRoles (fun _ => .sender)) Id s (fun _ => PUnit.{u + 1})) :
    Id ((_tr : PathAlong (ofRoles (fun _ => .sender)) s) × PUnit.{u + 1} × PUnit.{u + 1}) :=
  run s p c

example {Q : PFunctor.{u, t}} (lens : Lens P Q)
    (s₁ : FreeM P PUnit.{1}) (s₂ : Path s₁ → FreeM P PUnit.{1})
    (tr : PathAlong lens s₁) (tail : PathAlong lens (s₂ (projectPathAlong lens s₁ tr))) :
    PathAlong.split lens s₁ s₂ (PathAlong.append lens s₁ s₂ tr tail) = ⟨tr, tail⟩ :=
  PathAlong.split_append lens s₁ s₂ tr tail

example {Q : PFunctor.{u, t}} (lens : Lens P Q)
    (s₁ : FreeM P PUnit.{1}) (s₂ : Path s₁ → FreeM P PUnit.{1})
    (A B : (tr : PathAlong lens s₁) →
      PathAlong lens (s₂ (projectPathAlong lens s₁ tr)) → Type u)
    (tr : PathAlong lens (s₁.append s₂))
    (x : PathAlong.LiftAppend lens s₁ s₂ (fun tr tail => A tr tail × B tr tail) tr) :
    PathAlong.liftAppendProdMk lens s₁ s₂ A B tr
      (PathAlong.liftAppendProd lens s₁ s₂ A B tr x) = x :=
  PathAlong.liftAppendProdMk_liftAppendProd lens s₁ s₂ A B tr x

example (s : FreeM P PUnit.{u + 1}) (n : Nat)
    (tr : PathAlong l (FreeM.replicate PUnit.unit s n)) :
    PathAlong.replicateJoin l PUnit.unit s n
      (PathAlong.replicateSplit l PUnit.unit s n tr) = tr :=
  PathAlong.replicateJoin_replicateSplit l PUnit.unit s n tr

example : swapLens (swapLens l) = l := swapLens_swapLens l

end PolyFunTest.ModuleAPI.TwoPartyLens
