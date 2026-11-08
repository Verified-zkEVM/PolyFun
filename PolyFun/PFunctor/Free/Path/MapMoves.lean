/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

-- The map recurses through the runtime-path families of `Path.lean`.
import all PolyFun.PFunctor.Free.Path
public import PolyFun.PFunctor.Free.Path

/-!
# Runtime paths along two lenses on one tree

Two lenses `l : Lens P Q` and `l' : Lens P R` give two runtime-path types over the same tree
`s : FreeM P α`. A `PathAlong.MoveMap l l'` sends each runtime direction of `l` to one of `l'`
that selects the same source branch. `PathAlong.mapMoves` applies it along a whole runtime path,
and `projectPathAlong_mapMoves` shows that the shape path is unchanged.

A typical use forgets part of every move, for example the payload of a hidden message, while
keeping the tree: the forgetful path lies over the same shape path as the original.
-/

public section

universe uA uB uA₂ uB₂ uA₃ uB₃ v

namespace PFunctor.FreeM
variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {α : Type v}

-- Projection indices must reduce when descending to a source branch.
attribute [local implicit_reducible] Displayed.LocalMap.toHom
  Displayed.LocalMap.toHomFun projectPathAlongLocalMap projectPathAlong

namespace PathAlong

/-- A map of runtime directions from `l` to `l'` that selects the same source branch. -/
structure MoveMap (l : Lens P Q) (l' : Lens P R) where
  /-- The runtime direction of `l'` assigned to a runtime direction of `l`. -/
  map : (a : P.A) → Q.B (l.toFunA a) → R.B (l'.toFunA a)
  /-- Both directions select the same source branch. -/
  branch : ∀ a d, l'.toFunB a (map a d) = l.toFunB a d

/-- The identity move map. -/
@[expose] def MoveMap.id (l : Lens P Q) : MoveMap l l where
  map _ d := d
  branch _ _ := rfl

/-- Apply a move map at every node of a runtime path. -/
@[expose] def mapMoves {l : Lens P Q} {l' : Lens P R} (g : MoveMap l l') :
    (s : FreeM P α) → PathAlong l s → PathAlong l' s
  | .pure _, _ => ⟨⟩
  | .liftBind a rest, ⟨d, tr⟩ =>
    ⟨g.map a d, (congrArg (fun b => PathAlong l' (rest b)) (g.branch a d)).mpr
      (mapMoves g (rest (l.toFunB a d)) tr)⟩

/-- The identity move map leaves every runtime path unchanged. -/
@[simp] theorem mapMoves_id {l : Lens P Q} :
    (s : FreeM P α) → (tr : PathAlong l s) → mapMoves (MoveMap.id l) s tr = tr
  | .pure _, ⟨⟩ => rfl
  | .liftBind _ rest, ⟨d, tr⟩ => congrArg (Sigma.mk d) (mapMoves_id (rest _) tr)

end PathAlong

/-- Transporting the tail along an equality of source branches commutes with projection. -/
private theorem projectPathAlong_sigma_mpr {l' : Lens P R} {a : P.A}
    {rest : P.B a → FreeM P α} {b b' : P.B a} (e : b' = b)
    (x : PathAlong l' (rest b)) :
    (⟨b', projectPathAlong l' (rest b')
        ((congrArg (fun b => PathAlong l' (rest b)) e).mpr x)⟩ :
      (b : P.B a) × Path (rest b)) =
      ⟨b, projectPathAlong l' (rest b) x⟩ := by
  subst e
  rfl

/-- Mapping the moves of a runtime path preserves the shape path it projects to. -/
@[simp] theorem projectPathAlong_mapMoves {l : Lens P Q} {l' : Lens P R}
    (g : PathAlong.MoveMap l l') :
    (s : FreeM P α) → (tr : PathAlong l s) →
      projectPathAlong l' s (PathAlong.mapMoves g s tr) = projectPathAlong l s tr
  | .pure _, ⟨⟩ => rfl
  | .liftBind a rest, ⟨d, tr⟩ =>
    (projectPathAlong_sigma_mpr (rest := rest) (g.branch a d) _).trans
      (congrArg (Sigma.mk (l.toFunB a d)) (projectPathAlong_mapMoves g (rest _) tr))

end PFunctor.FreeM
