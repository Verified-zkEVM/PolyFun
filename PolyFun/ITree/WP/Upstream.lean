/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Algebra.WP
public import PolyFun.Control.Monad.Support.WP
public import PolyFun.ITree.WP.Bind
public import PolyFun.ITree.WP.Support

/-!
# Interaction-tree readings as core weakest-precondition interpretations

A monotone per-operation spec `Φ` induces two ordered monad algebras on interaction trees, one per
reading: a tree of lattice values reads the total or partial correctness of returning its value.
Through `MAlgOrdered.toWPMonad` they become exact core interpretations, `ITree.wpMonadTotal` and
`ITree.wpMonadPartial`, whose `wp` is the reading (`ITree.wpMonadTotal_wp`,
`ITree.wpMonadPartial_wp`).

The support readings of `PolyFun.Control.Monad.Support.WP` apply to interaction trees through
`ITree.instExactMonadAttach`. The demonic reading is partial correctness under the demonic spec,
and the angelic reading is total correctness under the angelic spec
(`ITree.toWPMonadDemonic_wp_eq_wpPartial`, `ITree.toWPMonadAngelic_wp_eq_wpTotal`).

As for free programs, none of these is a global instance: install the one intended, scoped or
local.
-/

@[expose] public section

universe uA uB uα

open Std.WP PFunctor

namespace ITree

variable {F : PFunctor.{uA, uB}}

section Algebras

variable {l : Type uα} [CompleteLattice l] (Φ : OpSpec F l) (hΦ : Φ.Monotone)

/-- The ordered monad algebra of the total reading: a tree of lattice values reads the total
correctness of returning its value. -/
@[instance_reducible]
def mAlgOrderedTotal : MAlgOrdered (ITree F) l where
  μ t := wpTotal Φ t id
  μ_pure x := wpTotal_pure hΦ x
  μ_bind_mono f g h x := by
    change wpTotal Φ (x >>= f) id ≤ wpTotal Φ (x >>= g) id
    rw [wpTotal_bind hΦ, wpTotal_bind hΦ]
    exact wpTotal_mono hΦ h x

/-- The ordered monad algebra of the partial reading. -/
@[instance_reducible]
def mAlgOrderedPartial : MAlgOrdered (ITree F) l where
  μ t := wpPartial Φ t id
  μ_pure x := wpPartial_pure hΦ x
  μ_bind_mono f g h x := by
    change wpPartial Φ (x >>= f) id ≤ wpPartial Φ (x >>= g) id
    rw [wpPartial_bind hΦ, wpPartial_bind hΦ]
    exact wpPartial_mono hΦ h x

/-- Total correctness as a core interpretation of interaction trees. -/
@[instance_reducible]
def wpMonadTotal : WPMonad (ITree F) l EStack⟨⟩ :=
  letI := mAlgOrderedTotal Φ hΦ
  MAlgOrdered.toWPMonad

/-- Partial correctness as a core interpretation of interaction trees. -/
@[instance_reducible]
def wpMonadPartial : WPMonad (ITree F) l EStack⟨⟩ :=
  letI := mAlgOrderedPartial Φ hΦ
  MAlgOrdered.toWPMonad

/-- The total interpretation's `wp` is the total reading. -/
theorem wpMonadTotal_wp {α : Type uα} (t : ITree F α) (post : α → l) (epost : EStack⟨⟩) :
    ((wpMonadTotal Φ hΦ).toWP α).wp t post epost = wpTotal Φ t post := by
  change wpTotal Φ (t >>= fun a => pure (post a)) id = _
  rw [wpTotal_bind hΦ]
  congr 1
  funext a
  exact wpTotal_pure hΦ (post a)

/-- The partial interpretation's `wp` is the partial reading. -/
theorem wpMonadPartial_wp {α : Type uα} (t : ITree F α) (post : α → l) (epost : EStack⟨⟩) :
    ((wpMonadPartial Φ hΦ).toWP α).wp t post epost = wpPartial Φ t post := by
  change wpPartial Φ (t >>= fun a => pure (post a)) id = _
  rw [wpPartial_bind hΦ]
  congr 1
  funext a
  exact wpPartial_pure hΦ (post a)

/-- The total interpretation is exact. -/
instance instExactWPMonadWpMonadTotal :
    @ExactWPMonad (ITree F) l EStack⟨⟩ _ _ _ (wpMonadTotal Φ hΦ) :=
  letI := mAlgOrderedTotal Φ hΦ
  MAlgOrdered.instExactWPMonadToWPMonad

/-- The partial interpretation is exact. -/
instance instExactWPMonadWpMonadPartial :
    @ExactWPMonad (ITree F) l EStack⟨⟩ _ _ _ (wpMonadPartial Φ hΦ) :=
  letI := mAlgOrderedPartial Φ hΦ
  MAlgOrdered.instExactWPMonadToWPMonad

end Algebras

section Support

variable {α : Type uα}

/-- On interaction trees, the demonic support reading is partial correctness under the demonic
spec. -/
theorem toWPMonadDemonic_wp_eq_wpPartial (t : ITree F α) (post : α → Prop) (epost : EStack⟨⟩) :
    ((MonadAttach.toWPMonadDemonic (m := ITree F)).toWP α).wp t post epost =
      wpPartial (OpSpec.demonic F) t post := by
  rw [MonadAttach.toWPMonadDemonic_wp]
  exact propext wpPartial_demonic_iff_allOutputs.symm

/-- On interaction trees, the angelic support reading is total correctness under the angelic
spec. -/
theorem toWPMonadAngelic_wp_eq_wpTotal (t : ITree F α) (post : α → Prop) (epost : EStack⟨⟩) :
    ((MonadAttach.toWPMonadAngelic (m := ITree F)).toWP α).wp t post epost =
      wpTotal (OpSpec.angelic F) t post := by
  rw [MonadAttach.toWPMonadAngelic_wp]
  exact propext wpTotal_angelic_iff_someOutput.symm

end Support

end ITree
