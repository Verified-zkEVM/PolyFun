/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.GPFunctor.Free.Indexed
public import PolyFun.GPFunctor.Lens.Basic
public import PolyFun.IPFunctor.Free.Lens

/-!
# Transport of the Free Graded Monad Along Lenses

A graded lens `l : Lens P Q` acts on free graded trees: `GFreeM.mapLens` rewrites each
node's shape forward along `l.toFunA` and selects the source branch by pulling the runtime
response back along `l.toFunB`. Because grading is per-shape and `grade_eq` is propositional,
each node carries one `gcast` along `grade_eq` — for concrete lenses whose `grade_eq` holds
by `rfl`, the casts are definitionally invisible.

`mapLens` is functorial (`mapLens_id`, `mapLens_comp`), a morphism of graded monad
structure (`mapLens_bind`), and natural in both forgetful maps out of `GFreeM`:

* `erase_mapLens` — grade erasure intertwines `GFreeM.mapLens` with
  [`PFunctor.FreeM.mapLens`](../../PFunctor/Free/Basic.lean) along `l.toPLens`;
* `toFreeM₂From_mapLens` / `toFreeM₂_mapLens` — the accumulated-grade translation
  intertwines `GFreeM.mapLens` with [`FreeM₂.mapLens`](../../IPFunctor/Free/Lens.lean)
  along `l.toIPLens`.

On the interpretation side, `mapGM_mapLens` pulls a shape handler back along a lens: the
image handler's action is `gmap`ped along the backward response map and transported along
`grade_eq`.
-/

@[expose] public section

universe uG uA₁ uA₂ uA₃ uB uB₁ uB₂ uB₃ v w

namespace GPFunctor

namespace GFreeM

variable {G : Type uG} [Monoid G] {P : GPFunctor.{uG, uA₁, uB₁} G}
  {Q : GPFunctor.{uG, uA₂, uB₂} G} {R : GPFunctor.{uG, uA₃, uB₃} G} {α β : Type v}

open scoped GPFunctor.Lens

/-! ## Transport along a lens -/

/-- Transport a free graded tree along a lens: shapes map forward, the runtime response at
the image shape selects the source branch via the backward map, and each node transports
along `grade_eq` back to the source grade. -/
protected def mapLens (l : Lens P Q) : {g : G} → GFreeM P g α → GFreeM Q g α
  | _, .pure x => .pure x
  | _, .roll (g := g') a r =>
      gcast (congrArg (· * g') (l.grade_eq a).symm)
        (.roll (l.toFunA a) fun d => (r (l.toFunB a d)).mapLens l)

@[simp]
lemma mapLens_pure (l : Lens P Q) (x : α) :
    (GFreeM.pure (P := P) x).mapLens l = GFreeM.pure x := rfl

@[simp]
lemma mapLens_roll (l : Lens P Q) {g : G} (a : P.A) (r : (b : P.B a) → GFreeM P g α) :
    (GFreeM.roll a r).mapLens l =
      gcast (congrArg (· * g) (l.grade_eq a).symm)
        (GFreeM.roll (l.toFunA a) fun d => (r (l.toFunB a d)).mapLens l) := rfl

/-- Grade casts float out of `mapLens`. -/
@[simp]
lemma mapLens_gcast (l : Lens P Q) {g g' : G} (e : g = g') (x : GFreeM P g α) :
    (gcast e x).mapLens l = gcast e (x.mapLens l) := by
  subst e; rfl

@[simp]
lemma mapLens_id {g : G} (x : GFreeM P g α) :
    x.mapLens (Lens.id P) = x := by
  induction x using GFreeM.inductionOn with
  | pure x => rfl
  | roll g a r ih =>
    exact (gcast_rfl _ _).trans (congrArg (GFreeM.roll a) (funext ih))

@[simp]
lemma mapLens_comp (l : Lens Q R) (l' : Lens P Q) {g : G} (x : GFreeM P g α) :
    (x.mapLens l').mapLens l = x.mapLens (l ∘ₗ l') := by
  induction x using GFreeM.inductionOn with
  | pure x => rfl
  | roll g a r ih =>
    simp only [mapLens_roll, mapLens_gcast, gcast_gcast]
    exact congrArg (gcast _)
      (congrArg (GFreeM.roll (l.toFunA (l'.toFunA a))) (funext fun d => ih _))

/-- `mapLens` commutes with the functor map. -/
@[simp]
lemma mapLens_map (l : Lens P Q) (f : α → β) {g : G} (x : GFreeM P g α) :
    (x.map f).mapLens l = (x.mapLens l).map f := by
  induction x using GFreeM.inductionOn with
  | pure x => rfl
  | roll g a r ih =>
    simp only [map_roll, mapLens_roll, map_gcast]
    exact congrArg (gcast _)
      (congrArg (GFreeM.roll (l.toFunA a)) (funext fun d => ih _))

/-- Transport along a lens is a morphism of graded monad structure. Cast-free: both sides
live at the grade `g * h`. -/
lemma mapLens_bind (l : Lens P Q) {g h : G} (x : GFreeM P g α) (f : α → GFreeM P h β) :
    (x.bind f).mapLens l = (x.mapLens l).bind (fun a => (f a).mapLens l) := by
  induction x using GFreeM.inductionOn with
  | pure x => simp only [bind_pure, mapLens_gcast, mapLens_pure]
  | roll g a r ih =>
    simp only [bind_roll, mapLens_gcast, mapLens_roll, bind_gcast_left, gcast_gcast, ih]

/-! ## Naturality in the forgetful maps -/

/-- Grade erasure intertwines graded and plain lens transport. -/
@[simp]
lemma erase_mapLens (l : Lens P Q) {g : G} (x : GFreeM P g α) :
    (x.mapLens l).erase = x.erase.mapLens l.toPLens := by
  induction x using GFreeM.inductionOn with
  | pure x => rfl
  | roll g a r ih =>
    simp only [mapLens_roll, erase_gcast, erase_roll, PFunctor.FreeM.mapLens_roll]
    exact congrArg (PFunctor.FreeM.roll (l.toFunA a)) (funext fun d => ih _)

/-- The accumulated-grade translation intertwines graded and indexed lens transport,
relative to any starting accumulator. The Forded proof argument is shared between the two
sides, so the statement is transport-free. -/
theorem toFreeM₂From_mapLens (l : Lens P Q) (k : G) {g t : G}
    (x : GFreeM P g α) (e : k * g = t) :
    toFreeM₂From k (x.mapLens l) e = (toFreeM₂From k x e).mapLens l.toIPLens := by
  induction x generalizing k t with
  | pure x => rfl
  | roll a r ih =>
    simp only [mapLens_roll, toFreeM₂From_gcast, toFreeM₂From_roll,
      IPFunctor.FreeM₂.mapLens_roll, Lens.toIPLens_toFunA, Lens.toIPLens_toFunB,
      toIPFunctor_src, ih, ← IPFunctor.FreeM₂.mapLens_castPre, castPre_toFreeM₂From]

/-- The canonical accumulated-grade translation intertwines graded and indexed lens
transport. -/
theorem toFreeM₂_mapLens (l : Lens P Q) {g : G} (x : GFreeM P g α) :
    toFreeM₂ (x.mapLens l) = (toFreeM₂ x).mapLens l.toIPLens :=
  toFreeM₂From_mapLens l 1 x (one_mul g)

/-! ## Handler pullback through `mapGM` -/

section mapGM

variable {m : G → Type uB → Type w} [GradedMonad G m] [LawfulGradedMonad G m]
  {P : GPFunctor.{uG, uA₁, uB} G} {Q : GPFunctor.{uG, uA₂, uB} G} {α : Type uB}

/-- Interpreting a transported tree pulls the shape handler back along the lens: the image
handler's action is `gmap`ped along the backward response map and transported along
`grade_eq`. -/
theorem mapGM_mapLens (l : Lens P Q) (h : (a : Q.A) → m (Q.grade a) (Q.B a))
    {g : G} (x : GFreeM P g α) :
    (x.mapLens l).mapGM h =
      x.mapGM (fun a => gcast (l.grade_eq a).symm
        (GradedMonad.gmap (l.toFunB a) (h (l.toFunA a)))) := by
  induction x using GFreeM.inductionOn with
  | pure x => rfl
  | roll g a r ih =>
    simp only [mapLens_roll, mapGM_gcast, mapGM_roll, gbind_gcast_left, gbind_gmap, ih]

end mapGM

end GFreeM

end GPFunctor
