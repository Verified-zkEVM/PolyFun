/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.PFunctor.Free.WP

/-!
# Ordinary-import canaries for per-operation specs

A spec lifted along `ULift` unfolds by `rfl`, and its fold is the lifted fold of the original
spec. The comparison of specs and the agreement of `wpFold` with CSLib's `foldFreeM` apply with
positions, directions, results, the carrier and its lift in independent universes. A spec valued
in `Type` lifts to an ordered monad algebra at every result universe.
-/

universe uA uB v w w'

namespace PolyFunTest.ModuleAPI.OpSpec

open _root_.PFunctor PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v} {l : Type w}

example (Φ : OpSpec P l) (a : P.A) (k : P.B a → ULift.{w'} l) :
    Φ.ulift a k = ⟨Φ a fun b => (k b).down⟩ :=
  rfl

example (Φ : OpSpec P l) (x : FreeM P α) (post : α → ULift.{w'} l) :
    wpFold Φ.ulift x post = ⟨wpFold Φ x fun a => (post a).down⟩ :=
  wpFold_ulift Φ x post

example (Φ : OpSpec P l) (x : FreeM P α) (post : α → l) :
    wpFold Φ x post = FreeM.foldFreeM post Φ x :=
  wpFold_eq_foldFreeM Φ x post

example [Preorder l] {Φ Ψ : OpSpec P l} (hΨ : Ψ.Monotone) (h : ∀ a k, Φ a k ≤ Ψ a k)
    (x : FreeM P α) (post : α → l) : wpFold Φ x post ≤ wpFold Ψ x post :=
  wpFold_le_wpFold_of_le hΨ h x post

example {L : Type} [CompleteLattice L] (Φ : OpSpec P L) (hΦ : Φ.Monotone) :
    MAlgOrdered (FreeM P) (ULift.{v} L) :=
  Φ.ulift.toMAlgOrdered hΦ.ulift

end PolyFunTest.ModuleAPI.OpSpec
