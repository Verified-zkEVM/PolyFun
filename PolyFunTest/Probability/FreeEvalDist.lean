/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.EvalDistEq
public import PolyFun.PFunctor.Free.Measure.EvalDist

/-!
# Measure semantics of free programs

Regression tests for the `EvalDistSemantics` instance of `PFunctor.FreeM P`, over a fair coin and
across universes.

The instances name the universe of the results, so they apply at results in any universe,
independently of the universes of the operations and answers. The tests instantiate them at
results below, at and above the answer universe, and at an explicit universe list. An instance
whose result universe were tied to the answer universe would fail the tests at results in `Type`
over answers in `Type 1`, which is where `prEvent` lives.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor

namespace PolyFunTest.Probability.FreeEvalDist

/-! ## A fair coin -/

/-- One operation whose answer is a bit. -/
@[expose, reducible] def Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- A fair coin: uniform answers on the two-point type. -/
noncomputable instance : Coin.AnswerMeasure := AnswerMeasure.uniformOfFiniteNonempty Coin

/-- One flip. -/
@[expose] def flip : FreeM Coin Bool := FreeM.lift (P := Coin) ()

example : LawfulEvalDistSemantics (FreeM Coin) := inferInstance

example : evalDist flip = uniformOn Set.univ := FreeM.evalDist_lift (P := Coin) ()

/-- Programs over discrete answers never fail. -/
example (program : FreeM Coin Bool) : prFail program = 0 := prFail_eq_zero_of_lossless program

example (program : FreeM Coin Bool) : IsProbabilityMeasure (evalDist program) := inferInstance

/-- Independent flips denote the product measure. -/
example :
    evalDist (do let x ← flip; let y ← flip; return (x, y)) =
      (uniformOn Set.univ : Measure Bool).prod (uniformOn Set.univ) := by
  rw [evalDist_pair, flip, FreeM.evalDist_lift (P := Coin)]
  rfl

/-- Replacing a continuation by one equal in distribution preserves the distribution. -/
example {f g : Bool → FreeM Coin Bool} (h : ∀ b, EvalDistEq (f b) (g b)) :
    EvalDistEq (flip >>= f) (flip >>= g) :=
  EvalDistEq.bind_right flip h

/-! ## Universes -/

section Universes

variable {P : PFunctor.{0, 1}} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]

noncomputable example : EvalDistSemantics (FreeM.{0, 0, 1} P) := inferInstance

noncomputable example : EvalDistSemantics (FreeM.{1, 0, 1} P) := inferInstance

noncomputable example : EvalDistSemantics (FreeM.{2, 0, 1} P) := inferInstance

/-- The instance has exactly the universe parameters of `FreeM`: results, operations and answers,
in that order. -/
noncomputable example : EvalDistSemantics (FreeM.{2, 0, 1} P) :=
  FreeM.instEvalDistSemanticsFreeM.{2, 0, 1}

example : LawfulPureEvalDistSemantics (FreeM.{0, 0, 1} P) := inferInstance

/-- Event probabilities of programs whose answers live in `Type 1`. -/
example (program : FreeM P Prop) : prEvent program ≤ 1 := prEvent_le_one program

example (program : FreeM P Bool) : EvalDistEq program program := EvalDistEq.rfl

/-- Failure probabilities at results in `Type 2`. -/
example {α : Type 2} (program : FreeM P α) : prFail program ≤ 1 := prFail_le_one program

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

example : LawfulEvalDistSemantics (FreeM.{0, 0, 1} P) := inferInstance

example : LawfulEvalDistSemantics (FreeM.{2, 0, 1} P) := inferInstance

example : LosslessEvalDistSemantics (FreeM.{0, 0, 1} P) := inferInstance

example {α : Type 2} (program : FreeM P α) : prFail program = 0 :=
  prFail_eq_zero_of_lossless program

end Universes

end PolyFunTest.Probability.FreeEvalDist
