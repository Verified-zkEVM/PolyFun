/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.Expectation

/-!
# Expectations of free programs

Regression tests for the integration spec `OpSpec.lintegral`, its agreement with the measure fold,
and the expectation algebras over `ℝ≥0∞`, the carrier that the generic program-logic tests
otherwise model with `ℕ∞` on a deterministic monad.

The universe tests instantiate the algebras over answers in `Type 1`, at results in `Type 1`
through `ULift`, and the fold lemmas at results in `Type 2`.
-/

public section

open MeasureTheory PFunctor PFunctor.FreeM
open scoped ENNReal

namespace PolyFunTest.Probability.Expectation

/-- One operation whose answer is a bit. -/
@[expose, reducible] def Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A coin that always answers `true`. -/
@[expose, reducible]
noncomputable def alwaysTrue : (a : Coin.A) → Measure (Coin.B a) := fun _ => Measure.dirac true

/-- A fair coin: half the mass on each answer. -/
@[expose, reducible]
noncomputable def fair : (a : Coin.A) → Measure (Coin.B a) :=
  fun _ => (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance (a : Coin.A) : IsProbabilityMeasure (fair a) :=
  ⟨by simp [fair, ENNReal.inv_two_add_inv_two]⟩

/-- One flip. -/
@[expose] def flip : FreeM Coin Bool := FreeM.lift (P := Coin) ()

/-- Two flips, returning whether both came up `true`. -/
@[expose] def bothTrue : FreeM Coin Bool := do
  let b ← flip
  let c ← flip
  pure (b && c)

/-! ## The fold and the measure fold -/

/-- An event probability computed by the fold: both flips of a fair coin come up `true` with
probability one quarter. -/
example : measureFold fair bothTrue {true} = 2⁻¹ * 2⁻¹ := by
  rw [measureFold_apply_eq_wpFold fair bothTrue (measurableSet_singleton true)]
  simp [bothTrue, flip, wpFold_bind]

/-- The fold bounds the integral for every postcondition and answer measures. -/
example {A : PFunctor.{0, 0}} [∀ a, MeasurableSpace (A.B a)] (ν : (a : A.A) → Measure (A.B a))
    (x : FreeM A Bool) (post : Bool → ℝ≥0∞) :
    ∫⁻ r, post r ∂measureFold ν x ≤ wpFold (OpSpec.lintegral ν) x post :=
  lintegral_measureFold_le_wpFold ν x post

/-- Countable answer types with measurable singletons are discrete, so the fold is the integral. -/
example {A : PFunctor.{0, 0}} [∀ a, MeasurableSpace (A.B a)] [∀ a, Countable (A.B a)]
    [∀ a, MeasurableSingletonClass (A.B a)] (ν : (a : A.A) → Measure (A.B a)) (x : FreeM A ℕ)
    (post : ℕ → ℝ≥0∞) :
    ∫⁻ r, post r ∂measureFold ν x = wpFold (OpSpec.lintegral ν) x post :=
  lintegral_measureFold_eq_wpFold ν x Measurable.of_discrete

/-- The fold lemma holds at results in `Type 2`. -/
example {α : Type 2} [MeasurableSpace α] (x : FreeM Coin α) {post : α → ℝ≥0∞}
    (hpost : Measurable post) :
    ∫⁻ r, post r ∂measureFold fair x = wpFold (OpSpec.lintegral fair) x post :=
  lintegral_measureFold_eq_wpFold fair x hpost

/-- Substitution is pullback: the integral against the measure fold of a simulated program is the
integral against the source program's measure fold under the implementations' measure folds. -/
example (handler : (a : Coin.A) → FreeM Coin (Coin.B a)) (x : FreeM Coin Bool)
    (post : Bool → ℝ≥0∞) :
    ∫⁻ r, post r ∂measureFold fair (x.liftM handler) =
      ∫⁻ r, post r ∂measureFold (fun a => measureFold fair (handler a)) x := by
  rw [lintegral_measureFold_eq_wpFold fair _ Measurable.of_discrete,
    lintegral_measureFold_eq_wpFold (fun a => measureFold fair (handler a)) _
      Measurable.of_discrete, wpFold_liftM, OpSpec.lintegral_pullback fair handler]

/-! ## The expectation algebra -/

/-- The expectation of a postcondition after one flip of a coin that always answers `true` is the
postcondition at `true`. -/
example (post : Bool → ℝ≥0∞) :
    (expectationAlgebra alwaysTrue).μ (flip >>= fun b => pure (post b)) = post true := by
  rw [expectationAlgebra_μ_bind_pure alwaysTrue _ Measurable.of_discrete, flip,
    measureFold_lift (P := Coin)]
  exact lintegral_dirac true post

/-- Under subprobability answers, the expectation of the constant `1` is at most `1`, so the
algebra restricts to the probability carrier. -/
example (program : FreeM Coin Bool) :
    (expectationAlgebra alwaysTrue).μ (program >>= fun _ => pure 1) ≤ 1 :=
  expectationAlgebra_μ_bind_const_le_one alwaysTrue program

noncomputable example : MAlgOrdered (FreeM Coin) (Set.Iic (1 : ℝ≥0∞)) :=
  probabilityAlgebra alwaysTrue

/-! ## The algebra of the measure semantics -/

/-- The fair coin as the answer measures of the interface. -/
noncomputable instance fairAnswers : Coin.AnswerMeasure := ⟨fair, inferInstance⟩

/-- The expectation algebra of the measure semantics is the algebra of the integration spec. -/
example : ExpectationWP.algebra (FreeM Coin) = expectationAlgebra fair :=
  ExpectationWP.algebra_freeM

/-- Under the measure semantics, the expectation of `bothTrue` as an indicator is one quarter. -/
example :
    (ExpectationWP.algebra (FreeM Coin)).μ (bothTrue >>= fun b => pure (if b then 1 else 0)) =
      2⁻¹ * 2⁻¹ := by
  rw [ExpectationWP.algebra_freeM (P := Coin)]
  change (expectationAlgebra fair).μ _ = _
  rw [expectationAlgebra_μ fair]
  simp [bothTrue, flip, wpFold_bind]

/-! ## Universes -/

/-- One operation whose answer is a bit in `Type 1`. -/
@[expose, reducible] def CoinU : PFunctor.{0, 1} := ⟨Unit, fun _ => ULift.{1} Bool⟩

/-- The expectation algebra over answers in `Type 1`, at results in `Type`. -/
noncomputable example (ν : (a : CoinU.A) → Measure (CoinU.B a)) :
    MAlgOrdered (FreeM CoinU) ℝ≥0∞ :=
  expectationAlgebra ν

/-- A flip with answers in `Type 1` observed at results in `Type`. -/
example (post : Bool → ℝ≥0∞) :
    (expectationAlgebra fun _ : CoinU.A => Measure.dirac (ULift.up true)).μ
        (FreeM.liftBind (P := CoinU) () fun b => pure (post b.down)) =
      post true := by
  rw [expectationAlgebra_μ (P := CoinU)]
  simp [wpFold_bind']

/-- The lifted expectation algebra on programs with values in `Type 1`. -/
noncomputable example : MAlgOrdered (FreeM.{1} Coin) (ULift.{1} ℝ≥0∞) :=
  expectationAlgebraULift fair

/-- One flip, with its result lifted to `Type 1`. -/
@[expose] def flipU : FreeM.{1} Coin (ULift.{1} Bool) :=
  FreeM.liftBind (P := Coin) () fun b => pure (ULift.up b)

/-- The lifted expectation of a fair flip. -/
example (post : Bool → ℝ≥0∞) :
    (expectationAlgebraULift fair).μ (flipU >>= fun b => pure ⟨post b.down⟩) =
      ⟨2⁻¹ * post true + 2⁻¹ * post false⟩ := by
  rw [expectationAlgebraULift_μ_bind_pure fair]
  simp [flipU, wpFold_bind']

/-- The lifted expectation algebra of the measure semantics, at values in `Type 1`, is the algebra
of the lifted integration spec. -/
example :
    ExpectationWP.algebraULift (FreeM.{1} Coin) =
      (expectationAlgebraULift fair : MAlgOrdered (FreeM.{1} Coin) (ULift.{1} ℝ≥0∞)) :=
  ExpectationWP.algebraULift_freeM

/-- The generic lifted expectation algebra applies to any lawful semantics at values in `Type 1`. -/
noncomputable example : MAlgOrdered (FreeM.{1} Coin) (ULift.{1} ℝ≥0∞) :=
  ExpectationWP.algebraULift (FreeM.{1} Coin)

end PolyFunTest.Probability.Expectation
