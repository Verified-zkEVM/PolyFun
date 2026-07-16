/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Bisim.CrossSignature
public import PolyFun.ITree.Sim.Facts

/-! # Event-renaming facts for relational interaction trees

This module connects the core `ITree.CrossSignatureWeakBisim` relation to pure
event renaming. It is kept outside `Bisim.CrossSignature` so the core
relational theory does not acquire a public dependency on the complete
simulation law surface.
-/

@[expose] public section

universe uEA uEB uFA uFB uα

namespace ITree

namespace EventSignatureRel

/-- The graph relation induced by a polynomial-functor lens.

A target reply is related precisely to the source reply obtained by pulling
it back along the lens. -/
def ofLens {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
    (φ : PFunctor.Lens E F) : EventSignatureRel E F where
  event a b := b = φ.toFunA a
  reply a b hab x y := by
    subst b
    exact x = φ.toFunB a y

end EventSignatureRel

namespace CrossSignatureWeakBisim

variable {E : PFunctor.{uEA, uEB}} {F : PFunctor.{uFA, uFB}}
  {α : Type uα}

/-- Every tree is related to its pure event-renaming by the lens's graph
relation. -/
theorem mapSpec (φ : PFunctor.Lens E F) (t : ITree E α) :
    CrossSignatureWeakBisim (EventSignatureRel.ofLens φ) Eq t (ITree.mapSpec φ t) := by
  refine coinduct (EventSignatureRel.ofLens φ) Eq
    (fun x y => ∃ t : ITree E α, x = t ∧ y = ITree.mapSpec φ t) ?_
    ⟨t, rfl, rfl⟩
  rintro x y ⟨t, hxt, hyt⟩
  subst x
  subst y
  rcases ht : shape' t with ⟨sh, c⟩
  cases sh with
  | pure r =>
      have ht' : t = ITree.pure r := by
        apply PFunctor.M.eq_of_dest_eq
        change shape' t = shape' (ITree.pure r)
        rw [ht, shape'_pure]
        congr 1
        funext z
        exact z.elim
      subst t
      rw [ITree.mapSpec_pure]
      exact ⟨_, _, .refl _, .refl _,
        CrossSignatureWeakBisim.HeadMatch.pure r r rfl (shape'_pure r) (shape'_pure r)⟩
  | step =>
      have ht' : t = ITree.step (c PUnit.unit) := by
        apply PFunctor.M.eq_of_dest_eq
        change shape' t = shape' (ITree.step (c PUnit.unit))
        rw [ht, shape'_step]
      subst t
      rw [ITree.mapSpec_step]
      exact ⟨_, _, .refl _, .refl _,
        CrossSignatureWeakBisim.HeadMatch.tau _ _ (shape'_step _) (shape'_step _)
          ⟨c PUnit.unit, rfl, rfl⟩⟩
  | query a =>
      have ht' : t = ITree.query a c := by
        apply PFunctor.M.eq_of_dest_eq
        change shape' t = shape' (ITree.query a c)
        rw [ht, shape'_query]
      subst t
      rw [ITree.mapSpec_query]
      refine ⟨_, _, .refl _, .refl _, ?_⟩
      refine CrossSignatureWeakBisim.HeadMatch.query a (φ.toFunA a) rfl c
        (fun y => ITree.mapSpec φ (c (φ.toFunB a y)))
        (shape'_query a c) (shape'_query _ _) ?_
      intro x y hxy
      subst x
      exact ⟨c (φ.toFunB a y), rfl, rfl⟩

end CrossSignatureWeakBisim

end ITree
