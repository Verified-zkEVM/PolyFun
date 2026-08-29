/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Control.Monad.Writer
public import PolyFun.Control.Monad.Hom

/-!
# Writer transformers on monad morphisms

This module gives `WriterT ω` its functorial action on PolyFun's bundled `MonadHom`.
It is separate from `PolyFun.Control.Monad.Hom` so consumers of the base morphism API
do not acquire Mathlib's Writer dependency unless they use it.
-/

@[expose] public section

universe u v w x

namespace WriterT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {ω α : Type u} [Monoid ω]

/-- `WriterT ω` is functorial on monad morphisms: the morphism acts on the underlying
computation while the returned value and accumulated output are left unchanged. -/
def mapHom (φ : m →ᵐ n) : WriterT ω m →ᵐ WriterT ω n where
  toFun _ x := WriterT.mk (φ x.run)
  toFun_pure' a := by
    apply WriterT.ext
    simp [WriterT.run_pure]
  toFun_bind' x y := by
    apply WriterT.ext
    simp only [WriterT.run_bind, WriterT.run_mk, MonadHom.mmap_bind]
    exact bind_congr fun aw => by
      simp only [MonadHom.mmap_map]

@[simp] lemma run_mapHom (φ : m →ᵐ n) (x : WriterT ω m α) :
    (WriterT.mapHom φ x).run = φ x.run := rfl

@[simp] theorem mapHom_id :
    WriterT.mapHom (ω := ω) (MonadHom.id m) = MonadHom.id (WriterT ω m) := by
  apply MonadHom.ext'
  intro α x
  rfl

variable {n' : Type u → Type x} [Monad n'] [LawfulMonad n']

@[simp] theorem mapHom_comp (G : n →ᵐ n') (F : m →ᵐ n) :
    WriterT.mapHom (ω := ω) (G ∘ₘ F) =
      WriterT.mapHom (ω := ω) G ∘ₘ WriterT.mapHom (ω := ω) F := by
  apply MonadHom.ext'
  intro α x
  rfl

end WriterT
