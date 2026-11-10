/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.WP.Bind
public import PolyFun.ITree.WP.Bisim

/-!
# Interaction-tree weakest preconditions through ordinary imports

The total and partial readings, their fixed-point characterizations, the sandwich, the exact
`bind` laws and weak-bisimulation invariance are usable from a module that imports them without
`import all`, at independent universes.
-/

public section

universe uA uB uα uβ w

namespace PolyFunTest.ModuleAPI.ITreeWP

variable {F : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {l : Type w} [CompleteLattice l]
  {Φ : PFunctor.OpSpec F l}

example (hΦ : Φ.Monotone) (post : α → l) (t : ITree F α) :
    ITree.wpTotal Φ t post = (ITree.wpStep hΦ post).lfp t :=
  ITree.wpTotal_eq_lfp hΦ t

example (hΦ : Φ.Monotone) (post : α → l) (t : ITree F α) :
    ITree.wpPartial Φ t post = (ITree.wpStep hΦ post).gfp t :=
  ITree.wpPartial_eq_gfp hΦ t

example (post : α → l) : ITree.wpTotal Φ (ITree.diverge : ITree F α) post = ⊥ :=
  ITree.wpTotal_diverge

example (post : α → l) : ITree.wpPartial Φ (ITree.diverge : ITree F α) post = ⊤ :=
  ITree.wpPartial_diverge

example {post : α → l} {R : ITree F α → l} (hR : ITree.wpStepFun Φ post R = R) (t : ITree F α) :
    ITree.wpTotal Φ t post ≤ R t ∧ R t ≤ ITree.wpPartial Φ t post :=
  ITree.wpTotal_le_le_wpPartial hR t

example (hΦ : Φ.Monotone) (post : α → l) (t : ITree F α) :
    ITree.wpTotal Φ t post ≤ ITree.wpPartial Φ t post :=
  ITree.wpTotal_le_wpPartial hΦ t

example (hΦ : Φ.Monotone) (t : ITree F α) (k : α → ITree F β) (post : β → l) :
    ITree.wpTotal Φ (ITree.bind t k) post =
      ITree.wpTotal Φ t fun a => ITree.wpTotal Φ (k a) post :=
  ITree.wpTotal_bind' hΦ k post t

example (hΦ : Φ.Monotone) (t : ITree F α) (k : α → ITree F β) (post : β → l) :
    ITree.wpPartial Φ (ITree.bind t k) post =
      ITree.wpPartial Φ t fun a => ITree.wpPartial Φ (k a) post :=
  ITree.wpPartial_bind' hΦ k post t

example (hΦ : Φ.Monotone) {post : α → l} {t s : ITree F α} (h : ITree.WeakBisim t s) :
    ITree.wpPartial Φ t post = ITree.wpPartial Φ s post :=
  ITree.WeakBisim.wpPartial_eq hΦ h

end PolyFunTest.ModuleAPI.ITreeWP
