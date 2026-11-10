/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.WP.Models

/-! # One spec across program models

Each example pins one agreement between models:
* on a finite program, both interaction-tree readings are the fold `wpFold`, which reads every
  answer of a query;
* a continuous algebra's denotation is its total reading, and both send silent divergence to `⊥`;
* a resumption's denotation is the total reading of its interaction tree, and on a finite program
  the denotation, the readings, the fold and CSLib's `foldFreeM` agree;
* a `Prop` spec lifted along `ULift` reads as the lifted reading.
-/

@[expose] public section

namespace PolyFunTest.ITreeWPModelsExamples

open PFunctor OmegaCompletePartialOrder

/-- One operation, a coin flip answered by a Boolean. -/
@[reducible] def CoinE : PFunctor.{0, 0} where
  A := PUnit
  B _ := Bool

/-- A finite program: flip once, return `1` on heads and `0` on tails. -/
def flipNat : FreeM CoinE Nat :=
  FreeM.liftBind PUnit.unit fun b => Pure.pure (if b then 1 else 0)

/-- On a finite program, total correctness of its tree is the fold. -/
example (post : Nat → Prop) :
    ITree.wpTotal (OpSpec.demonic CoinE) (FreeM.toITree flipNat) post =
      FreeM.wpFold (OpSpec.demonic CoinE) flipNat post :=
  ITree.wpTotal_toITree OpSpec.demonic_mono flipNat post

/-- On a finite program the readings agree: partial correctness is the same fold. -/
example (post : Nat → Prop) :
    ITree.wpPartial (OpSpec.demonic CoinE) (FreeM.toITree flipNat) post =
      ITree.wpTotal (OpSpec.demonic CoinE) (FreeM.toITree flipNat) post := by
  rw [ITree.wpPartial_toITree OpSpec.demonic_mono, ITree.wpTotal_toITree OpSpec.demonic_mono]

/-- The fold reads both answers: the flip satisfies `· ≤ 1` but not `· = 1`. -/
example : FreeM.wpFold (OpSpec.demonic CoinE) flipNat (· ≤ 1) ∧
    ¬ FreeM.wpFold (OpSpec.demonic CoinE) flipNat (· = 1) := by
  refine ⟨fun b => ?_, fun h => ?_⟩
  · cases b <;> simp [FreeM.wpFold_pure]
  · have h0 := h false
    simp [FreeM.wpFold_pure] at h0

/-- A constant continuous algebra: every query reads `True`. -/
def constAlg : Resumption.ContinuousAlgebra CoinE Prop :=
  fun _ => ContinuousHom.const True

/-- The continuous denotation is the total reading of the algebra. -/
example (post : Nat → Prop) (t : ITree CoinE Nat) :
    ITree.denote post constAlg t = ITree.wpTotal constAlg.toOpSpec t post :=
  ITree.denote_eq_wpTotal constAlg post t

/-- Both send silent divergence to `⊥`, even under an algebra that accepts every query. -/
example (post : Nat → Prop) :
    ¬ ITree.denote post constAlg (ITree.diverge : ITree CoinE Nat) := by
  rw [ITree.denote_eq_wpTotal, ITree.wpTotal_diverge]
  exact fun h => h

/-- A resumption's denotation is the total reading of its interaction tree. -/
example (post : Nat → Prop) (r : Resumption CoinE Nat) :
    Resumption.denote post constAlg r = ITree.wpTotal constAlg.toOpSpec r.toITree post :=
  Resumption.denote_eq_wpTotal constAlg post r

/-- The models agree in a triangle: on a finite program, the continuous denotation of its tree is
the total reading, which is the fold, which is CSLib's `foldFreeM`. That is also what the
resumption route gives (`Resumption.denote_toResumption`). -/
example (post : Nat → Prop) :
    ITree.denote post constAlg (FreeM.toITree flipNat) =
      Resumption.denote post constAlg (FreeM.toResumption flipNat) := by
  rw [ITree.denote_eq_wpTotal, ITree.wpTotal_toITree constAlg.toOpSpec_monotone,
    FreeM.wpFold_eq_foldFreeM, Resumption.denote_toResumption]
  rfl

/-- A `Prop` spec lifted to a larger universe reads as the lifted `Prop` reading: silent
divergence still fails total correctness. -/
example : ITree.wpTotal (OpSpec.demonic CoinE).ulift (ITree.diverge : ITree CoinE Nat)
    (fun _ => ⟨True⟩) = (⟨False⟩ : ULift.{1} Prop) := by
  rw [ITree.wpTotal_ulift OpSpec.demonic_mono, ITree.wpTotal_diverge]
  rfl

end PolyFunTest.ITreeWPModelsExamples
