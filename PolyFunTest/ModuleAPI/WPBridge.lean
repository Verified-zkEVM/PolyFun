/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Algebra.WP
public import PolyFun.Control.Monad.Support.WP

/-!
# Ordinary-import canaries for the core weakest-precondition bridges

An ordinary consumer of the program-logic kernel sees the bridges into core's `Std.WP` stack at
these shapes: the ordered-algebra interpretation `MAlgOrdered.toWPMonad` and the demonic support
interpretation `MonadAttach.toWPMonadDemonic` are `WPMonad`s at the empty exception stack
`EStack⟨⟩`, their `wp` agreement equations apply without unfolding either construction, and
core's triple through the algebra bridge is PolyFun's triple.
-/

public section

namespace PolyFunTest.ModuleAPI.WPBridge

open Std.WP MonadAttach

universe u v

section Algebra

variable {m : Type u → Type v} {l : Type u} [Monad m] [LawfulMonad m] [_root_.CompleteLattice l]
  [MAlgOrdered m l]

example : WPMonad m l EStack⟨⟩ := MAlgOrdered.toWPMonad

example {α : Type u} (x : m α) (post : α → l) (epost : EStack⟨⟩) :
    (letI := MAlgOrdered.toWPMonad (m := m) (l := l); Std.WP.wp x post epost) =
      MAlgOrdered.wp x post :=
  MAlgOrdered.toWPMonad_wp x post epost

example {α : Type u} (x : m α) (pre : l) (post : α → l) (epost : EStack⟨⟩) :
    @Std.WP.Triple l EStack⟨⟩ (m α) α _ _ x (MAlgOrdered.toWP α) pre post epost ↔
      MAlgOrdered.Triple pre x post :=
  MAlgOrdered.toWP_triple_iff x pre post epost

end Algebra

section Support

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]

example : WPMonad m Prop EStack⟨⟩ := toWPMonadDemonic

example {α : Type u} (x : m α) (post : α → Prop) (epost : EStack⟨⟩) :
    ((toWPMonadDemonic (m := m)).toWP α).wp x post epost = AllOutputs post x :=
  toWPMonadDemonic_wp x post epost

end Support

end PolyFunTest.ModuleAPI.WPBridge
