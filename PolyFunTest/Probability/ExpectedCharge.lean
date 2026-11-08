/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.ExpectedCharge

/-!
# Expected charge of free programs

Regression tests for the expected-charge reading over a fair coin. They cover:

* a program whose expected number of calls is below its worst case;
* the expected charge as the integral of the charge of the completed path, and the expected query
  count;
* expected-cost transfer through a handler that implements a fair flip by two flips.
-/

public section

open MeasureTheory PFunctor PFunctor.FreeM
open scoped ENNReal

namespace PolyFunTest.Probability.ExpectedCharge

/-- One operation whose answer is a bit. -/
@[expose, reducible] def Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A fair coin: half the mass on each answer. -/
@[expose, reducible]
noncomputable def fair : (a : Coin.A) → Measure (Coin.B a) :=
  fun _ => (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance (a : Coin.A) : IsProbabilityMeasure (fair a) :=
  ⟨by simp [fair, ENNReal.inv_two_add_inv_two]⟩

/-- One flip. -/
@[expose] def flip : FreeM Coin Bool := FreeM.lift (P := Coin) ()

/-- Flip, and flip again only after `true`: one call or two. -/
@[expose] def flipAgain : FreeM Coin Bool := do
  let b ← flip
  if b = true then flip else pure false

/-! ## Expected and worst-case charge -/

/-- The expected number of calls of `flipAgain` is one and a half. -/
example : wpFold (OpSpec.expectedCharge fair fun _ => 1) flipAgain (fun _ => 0) = 1 + 2⁻¹ := by
  simp [flipAgain, flip, wpFold_bind]

/-- The expected charge is at most the worst-case charge. -/
example :
    wpFold (OpSpec.expectedCharge fair fun _ => 1) flipAgain (fun _ => 0) ≤
      cost (fun _ => 1) flipAgain :=
  wpFold_expectedCharge_le_cost fair (fun _ => 1) flipAgain

/-- Leaf costs split off over discrete answers. -/
example (post : Bool → ℝ≥0∞) :
    wpFold (OpSpec.expectedCharge fair fun _ => 1) flipAgain post =
      wpFold (OpSpec.expectedCharge fair fun _ => 1) flipAgain (fun _ => 0) +
        ∫⁻ r, post r ∂measureFold fair flipAgain :=
  wpFold_expectedCharge_eq_add_lintegral fair _ flipAgain Measurable.of_discrete

/-! ## The charge of the completed path -/

/-- The expected charge is the integral of the charge of the completed path. -/
example : ∫⁻ s, s ∂measureFold fair (withPathCharge (fun _ => 1) flipAgain) = 1 + 2⁻¹ := by
  rw [lintegral_measureFold_withPathCharge fair]
  simp [flipAgain, flip, wpFold_bind]

section QueryCount

/-- The fair coin as the answer measures of the interface. -/
noncomputable instance fairAnswers : Coin.AnswerMeasure := ⟨fair, inferInstance⟩

/-- The expected query count is the expected unit charge. -/
example : expectedQueryCount flipAgain = 1 + 2⁻¹ := by
  rw [expectedQueryCount_eq_wpFold (P := Coin)]
  change wpFold (OpSpec.expectedCharge fair fun _ => 1) flipAgain (fun _ => 0) = _
  simp [flipAgain, flip, wpFold_bind]

end QueryCount

/-! ## Expected-cost transfer -/

/-- A fair flip implemented by the exclusive or of two fair flips. -/
@[expose] def xorFlip : (a : Coin.A) → FreeM Coin (Coin.B a) := fun _ => do
  let b ← flip
  let c ← flip
  pure (xor b c)

/-- The implementation makes two calls. -/
example (a : Coin.A) :
    wpFold (OpSpec.expectedCharge fair fun _ => 1) (xorFlip a) (fun _ => 0) = 2 := by
  simp [xorFlip, flip, wpFold_bind, ENNReal.inv_two_add_inv_two, one_add_one_eq_two]

/-- Every simulated call costs two calls in expectation. -/
example (x : FreeM Coin Bool) (post : Bool → ℝ≥0∞) :
    wpFold (OpSpec.expectedCharge fair fun _ => 1) (x.liftM xorFlip) post ≤
      wpFold (OpSpec.expectedCharge (fun a => measureFold fair (xorFlip a)) fun _ => 2) x post :=
  wpFold_expectedCharge_liftM_le fair (fun _ => 1) xorFlip (fun _ => 2) (fun _ => by
    simp [xorFlip, flip, wpFold_bind, ENNReal.inv_two_add_inv_two, one_add_one_eq_two]) x post

/-- The exact form charges each simulated call the expected charge of its implementation. -/
example (x : FreeM Coin Bool) (post : Bool → ℝ≥0∞) :
    wpFold (OpSpec.expectedCharge fair fun _ => 1) (x.liftM xorFlip) post =
      wpFold (OpSpec.expectedCharge (fun a => measureFold fair (xorFlip a))
        fun a => wpFold (OpSpec.expectedCharge fair fun _ => 1) (xorFlip a) fun _ => 0) x post :=
  wpFold_expectedCharge_liftM fair (fun _ => 1) xorFlip x post

end PolyFunTest.Probability.ExpectedCharge
