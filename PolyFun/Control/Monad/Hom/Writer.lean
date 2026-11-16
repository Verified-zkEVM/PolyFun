/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Control.Monad.Writer
public import PolyFun.Control.Monad.Hom

/-!
# Writer transformers on monad morphisms

This module gives `WriterT ω` its functorial action on PolyFun's bundled `MonadHom`.
It is separate from `PolyFun.Control.Monad.Hom` so consumers of the base morphism API
do not acquire Mathlib's Writer dependency unless they use it.

Two more morphisms change the output rather than the base monad: `WriterT.mapOutputHom f` maps
the accumulated output along a monoid hom `f`, and `WriterT.toStateTHom` reads an additive log
as the amount added to a running total in `StateT`.
-/

@[expose] public section

universe u v w x

namespace WriterT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {ω α : Type u}

/-- Erasing accumulated writer output is a monad morphism. Its laws do not require
associativity of the output operation because the output is discarded. -/
def eraseHom (empty : ω) (append : ω → ω → ω) :
    letI := WriterT.monad (M := m) empty append
    WriterT ω m →ᵐ m := by
  letI := WriterT.monad (M := m) empty append
  exact {
    toFun := fun _ x => Prod.fst <$> x.run
    toFun_pure' := fun a => by simp
    toFun_bind' := fun x f => by simp [map_bind, bind_map_left] }

@[simp] theorem eraseHom_apply (empty : ω) (append : ω → ω → ω)
    (x : WriterT ω m α) :
    eraseHom empty append x = Prod.fst <$> x.run := rfl

variable [Monoid ω]

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
    WriterT.mapHom (ω := ω) (G ∘ᵐ F) =
      WriterT.mapHom (ω := ω) G ∘ᵐ WriterT.mapHom (ω := ω) F := by
  apply MonadHom.ext'
  intro α x
  rfl

/-! ## Changing the output -/

section mapOutput

variable {M N : Type u} [Monoid M] [Monoid N]

/-- Mapping the accumulated output along a monoid hom is a monad morphism: the computation and its
returned value are unchanged. -/
def mapOutputHom (f : M →* N) : WriterT M m →ᵐ WriterT N m where
  toFun _ x := WriterT.mk (Prod.map _root_.id f <$> x.run)
  toFun_pure' a := by
    apply WriterT.ext
    simp
  toFun_bind' x y := by
    apply WriterT.ext
    simp [map_bind, bind_map_left]

@[simp] lemma run_mapOutputHom (f : M →* N) (x : WriterT M m α) :
    (mapOutputHom f x).run = Prod.map _root_.id f <$> x.run := rfl

end mapOutput

/-! ## An additive log as a running total -/

section toStateT

variable {κ : Type u} [AddMonoid κ]

/-- Read an additive log as the amount added to a running total: from the total `t`, a writer run
ends at `t` plus its log, added on the right. This is a monad morphism because addition is
associative and `0` is a right identity; it does not need commutativity. -/
def toStateTHom : WriterT (Multiplicative κ) m →ᵐ StateT κ m where
  toFun _ x := StateT.mk fun t => (fun p => (p.1, t + Multiplicative.toAdd p.2)) <$> x.run
  toFun_pure' a := by
    ext t
    simp
  toFun_bind' x y := by
    ext t
    simp [map_bind, bind_map_left, add_assoc]

@[simp] lemma run_toStateTHom (x : WriterT (Multiplicative κ) m α) (t : κ) :
    (toStateTHom x).run t = (fun p => (p.1, t + Multiplicative.toAdd p.2)) <$> x.run := rfl

end toStateT

end WriterT
