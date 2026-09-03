/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Algebra
public import ToCslib.Order.LeanOrder
public import Std.Internal.Do

/-!
# Ordered monad algebras as core weakest-precondition monads

Core's lattice-generic program logic (`Std.Internal.Do`, public as `Std.WP` from Lean v4.35)
interprets a monad through `WPMonad m Pred EPred`: a monotone predicate transformer per program,
sound for `pure` and `bind` up to `⊑`. An ordered monad algebra `MAlgOrdered m l` carries exactly
that data, with equations in place of the inequalities and no exception layer, so it yields a
`WPMonad m l EPost.Nil` once `ToCslib.Order.LeanOrder` makes Mathlib's `CompleteLattice l` an
`Assertion`. The construction is deliberately not an instance: install it at the base monad
(`letI` / `local instance`) and let core's `StateT`, `ReaderT`, `ExceptT`, and `OptionT`
instances lift it, which supplies honest exception postconditions where PolyFun's own
transformer lifts collapse failures to `⊥`.

Agreement is definitional: `wp` computed through the derived interpretation *is*
`MAlgOrdered.wp`, and core's `Triple` unfolds to `MAlgOrdered.Triple`. The module imports the
`Std.Internal.Do` root rather than its `WP` submodules so that the `@[spec]` database `vcgen`
consults — `Spec.bind` in particular, which lives in `Std.Internal.Do.Triple.SpecLemmas` — is
loaded wherever an instance built here is installed. The lattice operations
core's lemmas are stated with (`⊤`, `⊥`, `⊓`, `⊔` of `Lean.Order`) are Mathlib's on a bridged
carrier; the transfer lemmas below let `simp` move between the two spellings.
-/

public section

universe u v w

/-! ## Lattice operations across the bridge

`Std.Internal.Do.Order.Basic` defines `Lean.Order.top`, `meet`, and `join` from predicate-indexed
suprema; on a carrier whose `Lean.Order.CompleteLattice` comes from Mathlib they are Mathlib's
`⊤`, `⊓`, and `⊔`. -/

namespace MAlgOrdered

section LatticeTransfer

variable {α : Type u} [CompleteLattice α]

@[simp]
theorem top_eq_top : (Lean.Order.top : α) = ⊤ :=
  le_antisymm le_top (Lean.Order.le_top (⊤ : α))

@[simp]
theorem meet_eq_inf (x y : α) : Lean.Order.meet x y = x ⊓ y :=
  le_antisymm (le_inf (Lean.Order.meet_le_left x y) (Lean.Order.meet_le_right x y))
    (Lean.Order.le_meet _ x y inf_le_left inf_le_right)

@[simp]
theorem join_eq_sup (x y : α) : Lean.Order.join x y = x ⊔ y :=
  le_antisymm (Lean.Order.join_le x y _ le_sup_left le_sup_right)
    (sup_le (Lean.Order.left_le_join x y) (Lean.Order.right_le_join x y))

end LatticeTransfer

end MAlgOrdered

open Std.Internal.Do

namespace MAlgOrdered

variable {m : Type u → Type v} {l : Type u} [Monad m] [_root_.CompleteLattice l] [MAlgOrdered m l]

/-- The predicate-transformer interpretation of `m α` induced by an ordered monad algebra:
`MAlgOrdered.wp x post`, ignoring the empty exception postcondition. -/
@[expose, instance_reducible]
def toWP (α : Type u) : WP (m α) α l EPost.Nil where
  wpTrans x := ⟨fun post _ => MAlgOrdered.wp x post⟩
  wp_trans_monotone x _ _ _ _ _ hpost := wp_mono x hpost

@[simp]
theorem toWP_wp {α : Type u} (x : m α) (post : α → l) (epost : EPost.Nil) :
    (toWP (m := m) (l := l) α).wp x post epost = MAlgOrdered.wp x post :=
  rfl

/-- Core's triple through the derived interpretation is PolyFun's triple. -/
theorem toWP_triple_iff {α : Type u} (x : m α) (pre : l) (post : α → l) (epost : EPost.Nil) :
    @Std.Internal.Do.Triple l EPost.Nil (m α) α _ _ x (toWP α) pre post epost ↔
      MAlgOrdered.Triple pre x post := by
  let inst := toWP (m := m) (l := l) α
  exact ⟨fun h => h.le_wp, fun h => ⟨h⟩⟩

/-- An ordered monad algebra is a core weakest-precondition monad: its laws are the equations
`wp_pure` and `wp_bind` read as inequalities. Not an instance. -/
@[expose, instance_reducible]
def toWPMonad [LawfulMonad m] : WPMonad m l EPost.Nil where
  toLawfulMonad := inferInstance
  toWP := toWP
  pure_le_wp_pure x post _ := Lean.Order.PartialOrder.rel_of_eq (wp_pure x post).symm
  bind_le_wp_bind x f post _ := Lean.Order.PartialOrder.rel_of_eq (wp_bind x f post).symm

@[simp]
theorem toWPMonad_wp [LawfulMonad m] {α : Type u} (x : m α) (post : α → l) (epost : EPost.Nil) :
    (letI := toWPMonad (m := m) (l := l); Std.Internal.Do.wp x post epost) =
      MAlgOrdered.wp x post :=
  rfl

/-- The derived interpretation is conjunctive at `x` whenever the algebra's `wp x` preserves
binary meets of postconditions. -/
theorem wpConjunctiveOf {α : Type u} (x : m α)
    (h : ∀ Q₁ Q₂ : α → l,
      MAlgOrdered.wp x Q₁ ⊓ MAlgOrdered.wp x Q₂ ≤ MAlgOrdered.wp x fun a => Q₁ a ⊓ Q₂ a) :
    @WPConjunctive (m α) α l EPost.Nil _ _ (toWP α) x := by
  let inst := toWP (m := m) (l := l) α
  refine ⟨fun Q₁ Q₂ _ _ => ?_⟩
  change Lean.Order.meet (MAlgOrdered.wp x Q₁) (MAlgOrdered.wp x Q₂) ≤
    MAlgOrdered.wp x (Lean.Order.meet Q₁ Q₂)
  rw [meet_eq_inf]
  refine _root_.le_trans (h Q₁ Q₂) (wp_mono x fun a => ?_)
  rw [Lean.Order.meet_apply, meet_eq_inf]

end MAlgOrdered
