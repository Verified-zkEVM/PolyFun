/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import PolyFun.GPFunctor.Free.Lens

/-!
# Grade Reindexing of the Free Graded Monad Along Monoid Homomorphisms

The structure-level relabeling [`GPFunctor.mapGrade`](../Basic.lean) requires no algebraic
structure; refining it to the free graded monad does, because the total grade of a tree is a
product. For a monoid homomorphism `φ : G →* H`, `GFreeM.mapGrade φ` reindexes a grade-`g`
tree over `P` into a grade-`φ g` tree over `P.mapGrade φ` — the underlying container and the
tree's data are unchanged; only the grades are pushed through `φ`. Each constructor carries
one `gcast` along `map_one` / `map_mul`.

Reindexing is functorial (`mapGrade_id`, `mapGrade_mapGrade`), a morphism of graded monad
structure up to `map_mul` transport (`mapGrade_bind`), invisible to grade erasure
(`erase_mapGrade`), and commutes with lens transport via the structure-level
[`Lens.mapGrade`](../Lens/Basic.lean) (`mapGrade_mapLens`).
-/

@[expose] public section

universe uG uH uA₁ uA₂ uB₁ uB₂ v

namespace GPFunctor

namespace GFreeM

variable {G : Type uG} {H : Type uH} [Monoid G] [Monoid H]
  {P : GPFunctor.{uG, uA₁, uB₁} G} {Q : GPFunctor.{uG, uA₂, uB₂} G} {α β : Type v}

/-! ## Reindexing -/

/-- Reindex the grades of a free graded tree along a monoid homomorphism: the tree is
unchanged, and its total grade is pushed through `φ`. -/
protected def mapGrade (φ : G →* H) :
    {g : G} → GFreeM P g α → GFreeM (P.mapGrade φ) (φ g) α
  | _, .pure x => gcast (map_one φ).symm (.pure x)
  | _, .roll (g := g') a r =>
      gcast (show (P.mapGrade φ).grade a * φ g' = φ (P.grade a * g') from
          (map_mul φ (P.grade a) g').symm)
        (GFreeM.roll (P := P.mapGrade φ) (g := φ g') a fun b => (r b).mapGrade φ)

@[simp]
lemma mapGrade_pure (φ : G →* H) (x : α) :
    (GFreeM.pure (P := P) x).mapGrade φ = gcast (map_one φ).symm (GFreeM.pure x) := rfl

@[simp]
lemma mapGrade_roll (φ : G →* H) {g : G} (a : P.A) (r : (b : P.B a) → GFreeM P g α) :
    (GFreeM.roll a r).mapGrade φ =
      gcast (show (P.mapGrade φ).grade a * φ g = φ (P.grade a * g) from
          (map_mul φ (P.grade a) g).symm)
        (GFreeM.roll (P := P.mapGrade φ) (g := φ g) a fun b => (r b).mapGrade φ) := rfl

/-- Grade casts push through `mapGrade` along `congrArg φ`. -/
@[simp]
lemma mapGrade_gcast (φ : G →* H) {g g' : G} (e : g = g') (x : GFreeM P g α) :
    (gcast e x).mapGrade φ = gcast (congrArg φ e) (x.mapGrade φ) := by
  subst e; rfl

/-! ## Functoriality -/

@[simp]
lemma mapGrade_id {g : G} (x : GFreeM P g α) :
    x.mapGrade (MonoidHom.id G) = x := by
  induction x using GFreeM.inductionOn with
  | pure x => exact gcast_rfl _ _
  | roll g a r ih =>
    exact (gcast_rfl _ _).trans (congrArg (GFreeM.roll a) (funext ih))

@[simp]
lemma mapGrade_mapGrade {K : Type*} [Monoid K] (φ : G →* H) (ψ : H →* K)
    {g : G} (x : GFreeM P g α) :
    (x.mapGrade φ).mapGrade ψ = x.mapGrade (ψ.comp φ) := by
  induction x using GFreeM.inductionOn with
  | pure x =>
    simp only [mapGrade_pure, mapGrade_gcast, gcast_gcast]
    rfl
  | roll g a r ih =>
    simp only [mapGrade_roll, mapGrade_gcast, gcast_gcast, ih]
    rfl

/-! ## Compatibility with the graded monad structure and the forgetful maps -/

/-- Reindexing is a morphism of graded monad structure, up to `map_mul` transport. -/
lemma mapGrade_bind (φ : G →* H) {g h : G} (x : GFreeM P g α) (f : α → GFreeM P h β) :
    (x.bind f).mapGrade φ =
      gcast (map_mul φ g h).symm ((x.mapGrade φ).bind fun a => (f a).mapGrade φ) := by
  induction x using GFreeM.inductionOn with
  | pure x =>
    simp only [bind_pure, mapGrade_gcast, mapGrade_pure, bind_gcast_left, gcast_gcast]
  | roll g a r ih =>
    simp only [bind_roll, mapGrade_gcast, mapGrade_roll, bind_gcast_left, roll_gcast,
      gcast_gcast, ih]

/-- Reindexing is invisible to grade erasure: the underlying plain tree is unchanged. -/
@[simp]
lemma erase_mapGrade (φ : G →* H) {g : G} (x : GFreeM P g α) :
    (x.mapGrade φ).erase = x.erase := by
  induction x using GFreeM.inductionOn with
  | pure x =>
    simp only [mapGrade_pure, erase_gcast]
    rfl
  | roll g a r ih =>
    simp only [mapGrade_roll, erase_gcast, erase_roll, ih]
    rfl

/-- Reindexing commutes with lens transport, via the structure-level `Lens.mapGrade`. -/
lemma mapGrade_mapLens (φ : G →* H) (l : Lens P Q) {g : G} (x : GFreeM P g α) :
    (x.mapLens l).mapGrade φ = (x.mapGrade φ).mapLens (l.mapGrade φ) := by
  induction x using GFreeM.inductionOn with
  | pure x => simp only [mapLens_pure, mapGrade_pure, mapLens_gcast]
  | roll g a r ih =>
    simp only [mapLens_roll, mapGrade_gcast, mapGrade_roll, mapLens_gcast, gcast_gcast, ih]
    rfl

end GFreeM

end GPFunctor
