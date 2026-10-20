/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Free.Path

/-!
# Deprecated path-conversion contracts

Ordinary imports retain the recursive equations used by explicit unfolding in downstream proofs.
-/

@[expose] public section

set_option linter.deprecated false

open PFunctor

universe u v w x y

variable {P : PFunctor.{u, v}} {Q : PFunctor.{w, x}} {α : Type y}

-- Old explicit unfolding: the node equation closes without unfolding the preferred API.
example (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (d : Q.B (l.toFunA a)) (path : FreeM.Path ((rest (l.toFunB a d)).mapLens l)) :
    FreeM.mapLensPathToPathAlong l (.liftBind a rest) ⟨d, path⟩ =
      ⟨d, FreeM.mapLensPathToPathAlong l (rest (l.toFunB a d)) path⟩ := by
  simp only [FreeM.mapLensPathToPathAlong]

-- Old explicit unfolding in the opposite direction.
example (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (d : Q.B (l.toFunA a)) (path : FreeM.PathAlong l (rest (l.toFunB a d))) :
    FreeM.pathAlongToMapLensPath l (.liftBind a rest) ⟨d, path⟩ =
      ⟨d, FreeM.pathAlongToMapLensPath l (rest (l.toFunB a d)) path⟩ := by
  simp only [FreeM.pathAlongToMapLensPath]

-- Old equation application accepts paths indexed by the raw node constructor.
example (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (d : Q.B (l.toFunA a)) (path : FreeM.Path ((rest (l.toFunB a d)).mapLens l)) :
    FreeM.mapLensPathToPathAlong l (.liftBind a rest) ⟨d, path⟩ =
      ⟨d, FreeM.mapLensPathToPathAlong l (rest (l.toFunB a d)) path⟩ := by
  exact FreeM.mapLensPathToPathAlong_liftBind l a rest ⟨d, path⟩

example (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α)
    (d : Q.B (l.toFunA a)) (path : FreeM.PathAlong l (rest (l.toFunB a d))) :
    FreeM.pathAlongToMapLensPath l (.liftBind a rest) ⟨d, path⟩ =
      ⟨d, FreeM.pathAlongToMapLensPath l (rest (l.toFunB a d)) path⟩ := by
  exact FreeM.pathAlongToMapLensPath_liftBind l a rest ⟨d, path⟩

-- Old binder names and leaf equations remain usable together.
example (l : Lens P Q) (x : α) (path : FreeM.PathAlong l (.pure x)) :
    FreeM.pathAlongToMapLensPath (l := l) (s := .pure x) path = ⟨⟩ := by
  exact FreeM.pathAlongToMapLensPath_pure (l := l) (x := x) (path := path)

example (l : Lens P Q) (x : α) (path : FreeM.Path ((FreeM.pure x : FreeM P α).mapLens l)) :
    FreeM.mapLensPathToPathAlong (l := l) (s := .pure x) path = ⟨⟩ := by
  exact FreeM.mapLensPathToPathAlong_pure (l := l) (x := x) (path := path)

-- Old round-trip and output lemmas still rewrite expressions containing the old conversions.
example (l : Lens P Q) (s : FreeM P α) (path : FreeM.PathAlong l s) :
    FreeM.mapLensPathToPathAlong l s (FreeM.pathAlongToMapLensPath l s path) = path := by
  rw [FreeM.mapLensPathToPathAlong_toMapLensPath]

example (l : Lens P Q) (s : FreeM P α) (path : FreeM.Path (s.mapLens l)) :
    FreeM.pathAlongToMapLensPath l s (FreeM.mapLensPathToPathAlong l s path) = path := by
  rw [FreeM.pathAlongToMapLensPath_toPathAlong]

example (l : Lens P Q) (s : FreeM P α) (path : FreeM.PathAlong l s) :
    FreeM.output (s.mapLens l) (FreeM.pathAlongToMapLensPath l s path) =
      FreeM.outputAlong l s path := by
  rw [FreeM.output_mapLens_pathAlongToMapLensPath]

example (l : Lens P Q) (s : FreeM P α) (path : FreeM.Path (s.mapLens l)) :
    FreeM.outputAlong l s (FreeM.mapLensPathToPathAlong l s path) =
      FreeM.output (s.mapLens l) path := by
  rw [FreeM.outputAlong_mapLensPathToPathAlong]
