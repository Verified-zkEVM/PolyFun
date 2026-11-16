/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.Deterministic
public import PolyFun.Control.Monad.Measure.SemanticsVia
public import PolyFun.Control.Monad.Measure.WithFailure
public import PolyFun.PFunctor.Free.Measure.EvalDist

/-!
# Measure semantics of optional and exceptional computations

Regression tests for the `OptionT` and `ExceptT` instances of `EvalDistSemantics`, the failure
laws, and the bundled semantics `SemanticsVia`. A fair coin guarded on heads fails with
probability one half, and `prFail_bind_eq_add_lintegral_of_discrete` computes that failure from
its prefix and continuation. The transformer instances name no universe beyond those of the base
monad, so they apply above `Type`.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal

namespace PolyFunTest.Probability.Transformers

/-! ## Failure laws over an abstract monad -/

section generic

variable {m : Type → Type} [AlternativeMonad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m] {α β : Type}

example : prFail (failure : m α) = 1 := by simp

example (p : Prop) [Decidable p] : prFail (guard p : m Unit) = if p then 0 else 1 := by simp

example [MeasurableSpace β] (f : α → m β) : evalDist ((failure : m α) >>= f) = 0 := by simp

example (p : α → Prop) : prEvent (p <$> (failure : m α)) = 0 := by simp

end generic

/-! ## A guarded fair coin -/

/-- One operation whose answer is a bit. -/
@[expose, reducible] def Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A fair coin: uniform answers on the two-point type. -/
noncomputable instance : Coin.AnswerMeasure := AnswerMeasure.uniformOfFiniteNonempty Coin

/-- One flip. -/
@[expose] def flip : FreeM Coin Bool := FreeM.lift (P := Coin) ()

/-- Flip a coin and fail unless it lands heads. -/
@[expose] def heads : OptionT (FreeM Coin) Unit := do
  let b ← OptionT.lift flip
  guard (b = true)

example : LawfulEvalDistSemantics (OptionT (FreeM Coin)) := inferInstance

example : LawfulFailureEvalDistSemantics (OptionT (FreeM Coin)) := inferInstance

example : evalDist (OptionT.lift flip) = uniformOn Set.univ := by
  rw [OptionT.evalDist_lift, flip, FreeM.evalDist_lift (P := Coin)]
  rfl

/-- Each face of the coin has mass one half. -/
theorem evalDist_flip_singleton (b : Bool) : evalDist flip {b} = 2⁻¹ := by
  rw [flip, FreeM.evalDist_lift (P := Coin)]
  change (uniformOn Set.univ : Measure Bool) {b} = 2⁻¹
  rw [uniformOn_univ, Measure.count_singleton]
  simp

/-- A lifted draw adds no failure. -/
example : prFail (OptionT.lift flip) = 0 := by
  rw [OptionT.prFail_lift]
  exact prFail_eq_zero_of_lossless flip

/-- The guard passes exactly on heads. -/
example : prEvent ((fun _ ↦ True) <$> heads) = 2⁻¹ := by
  rw [heads, map_bind, OptionT.prEvent_bind_guard,
    prEvent_congr flip _ (fun b ↦ b = true) fun _ ↦ iff_of_eq (and_true _),
    prEvent_eq_evalDist_singleton, evalDist_flip_singleton]

/-- The guarded coin fails with probability one half, computed from the failure of its prefix
and of its continuation. -/
example : prFail heads = 2⁻¹ := by
  rw [heads, prFail_bind_eq_add_lintegral_of_discrete, OptionT.prFail_lift,
    prFail_eq_zero_of_lossless flip, zero_add, OptionT.evalDist_lift, lintegral_fintype]
  simp [evalDist_flip_singleton]

/-- The failure completion puts the failure probability on `none`. -/
example : evalDistWithFailure heads {none} = prFail heads :=
  evalDistWithFailure_none_eq_prFail heads

/-- The run of a guarded draw is the event of the guard. -/
example :
    (evalDist (do let b ← flip; (guard (b = true) : OptionT (FreeM Coin) Unit).run)).dropNone
        Set.univ = 2⁻¹ := by
  rw [OptionT.dropNone_evalDist_run_bind_guard_apply_univ, bind_pure_comp]
  change prEvent ((fun b ↦ b = true) <$> flip) = 2⁻¹
  rw [prEvent_eq_evalDist_singleton, evalDist_flip_singleton]

/-! ## Exceptional computations -/

section exceptT

example : LawfulEvalDistSemantics (ExceptT ℕ Option) := inferInstance

example : evalDist (throw 0 : ExceptT ℕ Option ℕ) = 0 := by simp

example (x : ℕ) : evalDist (pure x : ExceptT ℕ Option ℕ) = Measure.dirac x := by simp

example :
    evalDist (liftM flip : ExceptT Unit (FreeM Coin) Bool) = evalDist flip := by simp

example : prFail (throw 0 : ExceptT ℕ Option ℕ) = 1 := by
  simp [prFail_eq_defect, Measure.defect]

end exceptT

/-! ## Bundled semantics -/

section semanticsVia

example (program : FreeM Coin Bool) :
    (SemanticsVia.ofEvalDistSemantics (FreeM Coin)).evalDist program = evalDist program := rfl

example (program : FreeM Coin Bool) :
    (SemanticsVia.ofEvalDistSemantics (FreeM Coin)).prFail program = 0 := by
  rw [SemanticsVia.ofEvalDistSemantics_prFail, prFail_eq_zero_of_lossless]

example :
    (SemanticsVia.optionT (FreeM Coin)).evalDist heads = (evalDist heads.run).dropNone := by
  simp

example (mx : ExceptT ℕ Option ℕ) :
    (SemanticsVia.exceptT ℕ Option).evalDist mx = evalDist mx := rfl

end semanticsVia

/-! ## Universes -/

example : LawfulEvalDistSemantics (OptionT Option.{1}) := inferInstance

example : LawfulFailureEvalDistSemantics (OptionT Id.{2}) := inferInstance

example : LawfulEvalDistSemantics (ExceptT (ULift.{1} ℕ) Option.{1}) := inferInstance

example {α : Type 1} (mx : Option α) : prFail (OptionT.lift mx) = prFail mx :=
  OptionT.prFail_lift mx

example {α : Type 1} : prFail (failure : OptionT Id α) = 1 := prFail_failure

end PolyFunTest.Probability.Transformers
