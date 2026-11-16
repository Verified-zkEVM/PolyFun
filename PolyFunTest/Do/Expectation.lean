/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.WP
public import PolyFun.Control.Do.Spec

/-!
# The expectation readings of free programs on core's `vcgen`

Checks for `PolyFun.PFunctor.Free.Measure.WP` and the rules of `PolyFun.PFunctor.Free.Do` that
apply to it:

* under `open scoped PFunctor.FreeM.Expectation`, `vcgen` closes a call by `Spec.lift_lower`
  alone, which states its precondition as the integral against the answer measure. It decomposes
  binds, `if`, the constructor spelling `FreeM.liftBind` and a `StateT` stack over free programs,
  with an explicit `StateT.lift` (`Spec.lift_StateT`) and an inserted `monadLift`;
* after a call followed by more program, `vcgen` stops at the integral of the call: the remaining
  condition is pinned with `guard_target` on two flips of a fair coin, and the exact `wp` equations
  finish it;
* with the pointwise rules `Spec.lift_expectation_iInf` and `Spec.liftBind_expectation_iInf`
  registered locally, `vcgen` descends through every call;
* under `open scoped PFunctor.FreeM.UpperExpectation`, the dual reading states the upper bound on
  the same two flips, and the triple bounds the integral against the output measure;
* both readings are exact in their scopes, and a call over answers in `Type 1` is read in its
  constructor spelling.
-/

@[expose] public section

open MeasureTheory Std.WP PFunctor PFunctor.FreeM OrderDual
open scoped ENNReal

set_option experimental.vcgen true

namespace PolyFunTest.Do.Expectation

/-- One operation whose answer is a bit. -/
abbrev Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A fair coin: half the mass on each answer. -/
noncomputable def fair : (a : Coin.A) → Measure (Coin.B a) :=
  fun _ => (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance (a : Coin.A) : IsProbabilityMeasure (fair a) :=
  ⟨by simp [fair, ENNReal.inv_two_add_inv_two]⟩

/-- The fair coin as the answer measures of the interface. -/
noncomputable instance : Coin.AnswerMeasure := ⟨fair, inferInstance⟩

/-- The integral against a fair flip is the average of the two answers. -/
theorem lintegral_fair (f : Bool → ℝ≥0∞) :
    ∫⁻ b, f b ∂AnswerMeasure.toMeasure (P := Coin) () = 2⁻¹ * f true + 2⁻¹ * f false := by
  change ∫⁻ b, f b ∂fair () = _
  simp [fair, lintegral_add_measure]

/-- Two flips, returning whether both came up `true`. -/
def bothTrue : FreeM Coin Bool := do
  let b ← FreeM.lift (P := Coin) ()
  let c ← FreeM.lift (P := Coin) ()
  pure (b && c)

/-- The indicator of `true`. -/
def ind (b : Bool) : ℝ≥0∞ := if b then 1 else 0

/-! ## The expectation reading -/

section Lower

open scoped PFunctor.FreeM.Expectation

variable {P : PFunctor.{0, 0}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]

/- A call alone: `Spec.lift_lower` is exact, and `vcgen` closes the triple. -/
example (a : P.A) (Q : P.B a → ℝ≥0∞) :
    ⦃ ∫⁻ b, Q b ∂AnswerMeasure.toMeasure a ⦄ FreeM.lift a ⦃ Q ⦄ := by
  vcgen

/- A call followed by a pure step: the remaining condition compares two integrals. -/
example (a : P.A) (f : P.B a → ℕ) (Q : ℕ → ℝ≥0∞) :
    ⦃ ∫⁻ b, Q (f b) ∂AnswerMeasure.toMeasure a ⦄ (do let b ← FreeM.lift a; pure (f b)) ⦃ Q ⦄ := by
  vcgen
  simp only [binderNameHint, ExactWPMonad.wp_pure, Lean.Order.rel_eq_le, le_refl]

/- A branch on the answer. -/
example (a : P.A) (p : P.B a → Bool) (Q : ℕ → ℝ≥0∞) :
    ⦃ ∫⁻ b, (if p b then Q 1 else Q 2) ∂AnswerMeasure.toMeasure a ⦄
      (do let b ← FreeM.lift a; if p b then pure 1 else pure 2) ⦃ Q ⦄ := by
  vcgen
  simp only [binderNameHint, ExactWPMonad.wp_ite, ExactWPMonad.wp_pure, Lean.Order.rel_eq_le,
    le_refl]

/- A node in constructor spelling, decomposed by `Spec.liftBind_lower`. -/
example (a : P.A) (f : P.B a → ℕ) (Q : ℕ → ℝ≥0∞) :
    ⦃ ∫⁻ b, Q (f b) ∂AnswerMeasure.toMeasure a ⦄ FreeM.liftBind a (fun b => pure (f b))
      ⦃ Q ⦄ := by
  vcgen
  simp only [ExactWPMonad.wp_pure, Lean.Order.rel_eq_le, le_refl]

/- A `StateT` stack over free programs: an explicit `StateT.lift`, a state update, and a call
lifted by the inserted `monadLift`. `vcgen` stops at the integral of the first call, and the exact
equations of the `StateT` reading and of the expectation reading finish the condition. -/
example (a : P.A) (f : P.B a → ℕ) (Q : ℕ → ℕ → ℝ≥0∞) :
    ⦃ fun s => ∫⁻ b, ∫⁻ c, Q (f b) (s + f b + f c) ∂AnswerMeasure.toMeasure a
        ∂AnswerMeasure.toMeasure a ⦄
      (do
        let b ← StateT.lift (FreeM.lift a)
        modify (· + f b)
        let c ← (FreeM.lift a : FreeM P (P.B a))
        modify (· + f c)
        pure (f b) : StateT ℕ (FreeM P) ℕ)
    ⦃ Q ⦄ := by
  vcgen
  simp only [binderNameHint, Lean.Order.rel_eq_le, StateT.wp_apply_eq, StateT.run_bind,
    StateT.run_modify, StateT.run_monadLift, StateT.run_pure, monadLift_self, ExactWPMonad.wp_bind,
    ExactWPMonad.wp_pure, Expectation.wp_lift, le_refl]

/- **Where `vcgen` stops.** On two flips of a fair coin, `vcgen` steps the first call and stops at
its integral: the weakest precondition of the rest stays under the binder. The exact `wp` equations
then compute the probability that both flips come up `true`. -/
example : ⦃ 2⁻¹ * 2⁻¹ ⦄ bothTrue ⦃ ind ⦄ := by
  vcgen [bothTrue]
  simp only [binderNameHint]
  guard_target = Lean.Order.PartialOrder.rel (2⁻¹ * 2⁻¹ : ℝ≥0∞)
    (∫⁻ b : Coin.B (), wp (do let c ← FreeM.lift (P := Coin) (); pure (b && c)) ind
      Lean.Order.bot ∂AnswerMeasure.toMeasure (P := Coin) ())
  simp only [Lean.Order.rel_eq_le, ExactWPMonad.wp_bind, ExactWPMonad.wp_pure,
    Expectation.wp_lift (P := Coin)]
  rw [lintegral_fair, lintegral_fair, lintegral_fair]
  simp [ind]

/-- Over discrete answers, the lower-bound triple bounds the event's probability from below. -/
example (h : ⦃ 2⁻¹ * 2⁻¹ ⦄ bothTrue ⦃ ind ⦄) : 2⁻¹ * 2⁻¹ ≤ ∫⁻ r, ind r ∂evalDist bothTrue :=
  Expectation.le_lintegral_evalDist_of_triple Measurable.of_discrete h

/-- The reading is exact in its scope. -/
example : ExactWPMonad (FreeM P) ℝ≥0∞ EStack⟨⟩ := inferInstance

/-- Over discrete answers, the interpretation of the expectation algebra of the measure semantics
is the scoped reading. -/
example [∀ a, DiscreteMeasurableSpace (P.B a)] :
    @MAlgOrdered.toWPMonad (FreeM P) ℝ≥0∞ _ _ (ExpectationWP.algebra (FreeM P)) _ =
      Expectation.instWPMonad :=
  ExpectationWP.toWPMonad_algebra_freeM

end Lower

/-! ## The pointwise rules -/

section Pointwise

open scoped PFunctor.FreeM.Expectation

attribute [local spec high] Spec.lift_expectation_iInf Spec.liftBind_expectation_iInf

variable {P : PFunctor.{0, 0}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]

/- With the pointwise rules, `vcgen` descends through both calls, one condition per pair of
answers. -/
example (a : P.A) (f : P.B a → ℕ) (Q : ℕ → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ n, c ≤ Q n) :
    ⦃ c ⦄ (do let b ← FreeM.lift a; let d ← FreeM.lift a; pure (f b + f d)) ⦃ Q ⦄ := by
  vcgen
  exact h _

/- The constructor spelling descends the same way. -/
example (a : P.A) (f : P.B a → ℕ) (Q : ℕ → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ n, c ≤ Q n) :
    ⦃ c ⦄ FreeM.liftBind a (fun b => FreeM.liftBind a fun d => pure (f b + f d)) ⦃ Q ⦄ := by
  vcgen
  exact h _

end Pointwise

/-! ## The upper expectation reading -/

section Upper

open scoped PFunctor.FreeM.UpperExpectation

variable {P : PFunctor.{0, 0}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]

/- A call alone: `Spec.lift_upper` states the precondition as the integral, in the dual order. -/
example (a : P.A) (Q : P.B a → ℝ≥0∞ᵒᵈ) :
    ⦃ toDual (∫⁻ b, ofDual (Q b) ∂AnswerMeasure.toMeasure a) ⦄ FreeM.lift a ⦃ Q ⦄ := by
  vcgen

/- A branch on the answer, in the dual order. -/
example (a : P.A) (p : P.B a → Bool) (Q : ℕ → ℝ≥0∞) :
    ⦃ toDual (∫⁻ b, (if p b then Q 1 else Q 2) ∂AnswerMeasure.toMeasure a) ⦄
      (do let b ← FreeM.lift a; if p b then pure 1 else pure 2) ⦃ fun n => toDual (Q n) ⦄ := by
  vcgen
  simp only [binderNameHint, ExactWPMonad.wp_ite, ExactWPMonad.wp_pure, apply_ite ofDual,
    ofDual_toDual, Lean.Order.rel_eq_le, le_refl]

/- A `StateT` stack over free programs, in the dual order. -/
example (a : P.A) (f : P.B a → ℕ) (Q : ℕ → ℕ → ℝ≥0∞) :
    ⦃ fun s => toDual (∫⁻ b, Q (f b) (s + f b) ∂AnswerMeasure.toMeasure a) ⦄
      (do
        let b ← StateT.lift (FreeM.lift a)
        modify (· + f b)
        pure (f b) : StateT ℕ (FreeM P) ℕ)
    ⦃ fun n s => toDual (Q n s) ⦄ := by
  vcgen
  simp only [binderNameHint, StateT.wp_apply_eq, StateT.run_bind, StateT.run_modify,
    StateT.run_pure, ExactWPMonad.wp_bind, ExactWPMonad.wp_pure, ofDual_toDual,
    Lean.Order.rel_eq_le, le_refl]

/- **An upper bound through the dual.** Both flips of a fair coin come up `true` with probability
at most one quarter. `vcgen` stops at the integral of the first call, in the dual order. -/
theorem bothTrue_upper : ⦃ toDual (2⁻¹ * 2⁻¹ : ℝ≥0∞) ⦄ bothTrue ⦃ fun r => toDual (ind r) ⦄ := by
  vcgen [bothTrue]
  simp only [binderNameHint]
  guard_target = Lean.Order.PartialOrder.rel (toDual (2⁻¹ * 2⁻¹ : ℝ≥0∞))
    (toDual (∫⁻ b : Coin.B (), ofDual (wp (do let c ← FreeM.lift (P := Coin) (); pure (b && c))
      (fun r => toDual (ind r)) Lean.Order.bot) ∂AnswerMeasure.toMeasure (P := Coin) ()))
  simp only [ofDual_toDual, Lean.Order.rel_eq_le, ExactWPMonad.wp_bind, ExactWPMonad.wp_pure,
    UpperExpectation.wp_lift (P := Coin)]
  rw [lintegral_fair, lintegral_fair, lintegral_fair]
  simp [ind]

/-- The upper-bound triple bounds the event's probability under the output measure. -/
example : ∫⁻ r, ind r ∂evalDist bothTrue ≤ 2⁻¹ * 2⁻¹ :=
  UpperExpectation.lintegral_evalDist_le_of_triple bothTrue_upper

/-- The dual reading is exact in its scope. -/
example : ExactWPMonad (FreeM P) ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ := inferInstance

end Upper

/-! ## Answers in another universe -/

section Universe

open scoped PFunctor.FreeM.Expectation

/-- One operation whose answer is a bit in `Type 1`. -/
abbrev CoinU : PFunctor.{0, 1} := ⟨Unit, fun _ => ULift.{1} Bool⟩

variable [∀ a, MeasurableSpace (CoinU.B a)] [CoinU.AnswerMeasure]

/- Programs with values in `Type` over answers in `Type 1` read a call in its constructor spelling.
-/
example (Q : Bool → ℝ≥0∞) :
    ⦃ ∫⁻ b, Q b.down ∂AnswerMeasure.toMeasure (P := CoinU) () ⦄
      (FreeM.liftBind (P := CoinU) () fun b => pure b.down) ⦃ Q ⦄ := by
  vcgen
  simp only [ExactWPMonad.wp_pure, Lean.Order.rel_eq_le, le_refl]

end Universe

end PolyFunTest.Do.Expectation
