/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Hom
public import Std.Internal.Do

/-!
# Transport of weakest preconditions along monad morphisms

A monad morphism `F : m →ᵐ n` pulls a `WPMonad` interpretation of `n` back to `m`: a program is
interpreted by the transformer of its image. Because `F` preserves `pure` and `bind`, the
soundness inequalities transfer verbatim. This is how a free program acquires the semantics of a
handler (`FreeM.wpMonadOfHandler`), and how any monad interpreting into a `vcgen`-ready stack
inherits that stack's specifications. The unbundled form takes the two preservation equations
inline, so cslib's `IsMonadHom` predicate instantiates it once it lands.

Nothing here is an instance: register the transported structure scoped or local at the
carrier where it is intended.
-/

public section

universe u v w w' z

open Std.Internal.Do Lean.Order

namespace MonadHom

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  {Pred : Type w'} {EPred : Type z} [Assertion Pred] [Assertion EPred]

/-- Pull back the interpretation of `n α` along a monad morphism. -/
@[expose, instance_reducible]
def transportWP (F : m →ᵐ n) (α : Type u) [WP (n α) α Pred EPred] : WP (m α) α Pred EPred where
  wpTrans x := WP.wpTrans (F x)
  wp_trans_monotone x := WP.wp_trans_monotone (F x)

@[simp]
theorem transportWP_wp (F : m →ᵐ n) {α : Type u} [WP (n α) α Pred EPred] (x : m α)
    (post : α → Pred) (epost : EPred) :
    (F.transportWP α).wp x post epost = wp (F x) post epost :=
  rfl

/-- The transported interpretation is a weakest-precondition monad whenever the target is and
the source is lawful. -/
@[expose, instance_reducible]
def transportWPMonad (F : m →ᵐ n) [LawfulMonad m] [WPMonad n Pred EPred] :
    WPMonad m Pred EPred where
  toLawfulMonad := inferInstance
  toWP α := F.transportWP α
  pure_le_wp_pure a post epost := by
    change post a ⊑ wp (F (pure a)) post epost
    rw [F.mmap_pure]
    exact WPMonad.pure_le_wp_pure a post epost
  bind_le_wp_bind x f post epost := by
    change wp (F x) (fun a => wp (F (f a)) post epost) epost ⊑ wp (F (x >>= f)) post epost
    rw [F.mmap_bind]
    exact WPMonad.bind_le_wp_bind (F x) (fun a => F (f a)) post epost

/-- Transport along a function preserving `pure` and `bind`, with the two equations supplied
inline rather than bundled. -/
@[expose, instance_reducible]
def transportWPMonadOf (F : ∀ {α : Type u}, m α → n α)
    (hpure : ∀ {α : Type u} (a : α), F (pure a) = pure a)
    (hbind : ∀ {α β : Type u} (x : m α) (f : α → m β), F (x >>= f) = F x >>= fun a => F (f a))
    [LawfulMonad m] [WPMonad n Pred EPred] : WPMonad m Pred EPred where
  toLawfulMonad := inferInstance
  toWP α :=
    { wpTrans := fun x => WP.wpTrans (F x)
      wp_trans_monotone := fun x => WP.wp_trans_monotone (F x) }
  pure_le_wp_pure a post epost := by
    change post a ⊑ wp (F (pure a)) post epost
    rw [hpure]
    exact WPMonad.pure_le_wp_pure a post epost
  bind_le_wp_bind x f post epost := by
    change wp (F x) (fun a => wp (F (f a)) post epost) epost ⊑ wp (F (x >>= f)) post epost
    rw [hbind]
    exact WPMonad.bind_le_wp_bind (F x) (fun a => F (f a)) post epost

end MonadHom
