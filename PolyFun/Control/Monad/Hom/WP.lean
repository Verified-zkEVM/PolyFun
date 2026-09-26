/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Hom.IsMonadHom
public import Std.WP

/-!
# Transport of weakest preconditions along monad morphisms

A monad morphism `F : ∀ {α}, m α → n α` pulls a `WPMonad` interpretation of `n` back to `m`: a
program is interpreted by the transformer of its image. Because `F` preserves `pure` and `bind`,
the soundness inequalities transfer verbatim. This is how a free program acquires the semantics
of a handler (`FreeM.liftM` is a monad morphism), and how any monad interpreting into a
`vcgen`-ready stack inherits that stack's specifications. The unbundled form takes cslib's
`IsMonadHom` predicate; the bundled form takes PolyFun's `m →ᵐ n` and goes through
`MonadHom.isMonadHom`.

Nothing here is an instance: register the transported structure scoped or local at the
carrier where it is intended.
-/

public section

universe u v w w' z

open Std.WP Lean.Order

namespace MonadHom

section Pullback

variable {m : Type u → Type v} {n : Type u → Type w}
  {Pred : Type w'} {EPred : Type z} [Assertion Pred] [Assertion EPred]

/-- Pull back the interpretation of `n α` along any family of maps `m α → n α`. -/
@[expose, instance_reducible]
def transportWPOf (F : ∀ {α : Type u}, m α → n α) (α : Type u) [WP (n α) α Pred EPred] :
    WP (m α) α Pred EPred where
  wpTrans x := WP.wpTrans (F x)
  wp_trans_monotone x := WP.wp_trans_monotone (F x)

@[simp]
theorem transportWPOf_wp (F : ∀ {α : Type u}, m α → n α) {α : Type u} [WP (n α) α Pred EPred]
    (x : m α) (post : α → Pred) (epost : EPred) :
    (transportWPOf F α).wp x post epost = wp (F x) post epost :=
  rfl

end Pullback

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  {Pred : Type w'} {EPred : Type z} [Assertion Pred] [Assertion EPred]

/-- Pull back the interpretation of `n α` along a bundled monad morphism. -/
@[expose, instance_reducible]
def transportWP (F : m →ᵐ n) (α : Type u) [WP (n α) α Pred EPred] : WP (m α) α Pred EPred :=
  transportWPOf (fun x => F x) α

@[simp]
theorem transportWP_wp (F : m →ᵐ n) {α : Type u} [WP (n α) α Pred EPred] (x : m α)
    (post : α → Pred) (epost : EPred) :
    (F.transportWP α).wp x post epost = wp (F x) post epost :=
  rfl

/-- The interpretation transported along a monad morphism is a weakest-precondition monad
whenever the target is and the source is lawful. -/
@[expose, instance_reducible]
def transportWPMonadOf {F : ∀ {α : Type u}, m α → n α} (hf : Cslib.IsMonadHom m n F)
    [LawfulMonad m] [WPMonad n Pred EPred] : WPMonad m Pred EPred where
  toLawfulMonad := inferInstance
  toWP α := transportWPOf F α
  pure_le_wp_pure a post epost := by
    change post a ⊑ wp (F (pure a)) post epost
    rw [hf.map_pure]
    exact WPMonad.pure_le_wp_pure a post epost
  bind_le_wp_bind x f post epost := by
    change wp (F x) (fun a => wp (F (f a)) post epost) epost ⊑ wp (F (x >>= f)) post epost
    rw [hf.map_bind]
    exact WPMonad.bind_le_wp_bind (F x) (fun a => F (f a)) post epost

/-- The bundled form of `transportWPMonadOf`. -/
@[expose, instance_reducible]
def transportWPMonad (F : m →ᵐ n) [LawfulMonad m] [WPMonad n Pred EPred] :
    WPMonad m Pred EPred :=
  transportWPMonadOf F.isMonadHom

end MonadHom
