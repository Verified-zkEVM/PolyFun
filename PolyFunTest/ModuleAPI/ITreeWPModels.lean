/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.WP.Models
public import PolyFun.ITree.WP.Upstream

/-!
# Interaction-tree readings across models, through ordinary imports

The agreements with `wpFold` and `ITree.denote`, the core interpretations and their identification
with the support readings are usable from a module that imports them without `import all`, at
independent universes.
-/

public section

universe uA uB uα w

open Std.WP

namespace PolyFunTest.ModuleAPI.ITreeWPModels

variable {F : PFunctor.{uA, uB}} {α : Type uα}

example {l : Type w} [CompleteLattice l] {Φ : PFunctor.OpSpec F l} (hΦ : Φ.Monotone)
    (x : PFunctor.FreeM F α) (post : α → l) :
    ITree.wpTotal Φ (PFunctor.FreeM.toITree x) post = PFunctor.FreeM.wpFold Φ x post :=
  ITree.wpTotal_toITree hΦ x post

example {l : Type w} [CompleteLattice l] (alg : PFunctor.Resumption.ContinuousAlgebra F l)
    (post : α → l) (t : ITree F α) :
    ITree.denote post alg t = ITree.wpTotal alg.toOpSpec t post :=
  ITree.denote_eq_wpTotal alg post t

example {l : Type uα} [CompleteLattice l] {Φ : PFunctor.OpSpec F l} (hΦ : Φ.Monotone)
    (t : ITree F α) (post : α → l) :
    ((ITree.wpMonadPartial Φ hΦ).toWP α).wp t post () = ITree.wpPartial Φ t post :=
  ITree.wpMonadPartial_wp Φ hΦ t post ()

example (t : ITree F α) (post : α → Prop) :
    ((MonadAttach.toWPMonadAngelic (m := ITree F)).toWP α).wp t post () =
      ITree.wpTotal (PFunctor.OpSpec.angelic F) t post :=
  ITree.toWPMonadAngelic_wp_eq_wpTotal t post ()

example {l : Type w} [CompleteLattice l] {Φ : PFunctor.OpSpec F l} (hΦ : Φ.Monotone)
    (t : ITree F α) (post : α → ULift.{uα} l) :
    ITree.wpTotal Φ.ulift t post = ⟨ITree.wpTotal Φ t fun a => (post a).down⟩ :=
  ITree.wpTotal_ulift hΦ t post

end PolyFunTest.ModuleAPI.ITreeWPModels
