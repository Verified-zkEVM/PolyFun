/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Batteries.Control.AlternativeMonad

/-!
# Lifting `guard`, `optional` and `Option.elimM`

Batteries' `LawfulAlternativeLift` states that a monad lift preserves `failure` and `<|>`
(`monadLift_failure`, `monadLift_orElse`). Together with core's `LawfulMonadLift` it lifts the
derived combinators `guard` and `optional`, and `Option.elimM` lifts along every lawful monad lift.
The statements are about `monadLift`; core's `liftM` is an abbreviation of it.
-/

@[expose] public section

universe u v w

variable {m : Type u → Type v} {n : Type u → Type w} {α β : Type u}

/-- A lift that preserves `pure` and `failure` preserves `guard`. -/
@[simp]
theorem monadLift_guard {m : Type → Type v} {n : Type → Type w} [AlternativeMonad m]
    [AlternativeMonad n] [MonadLift m n] [LawfulAlternativeLift m n] [LawfulMonadLift m n]
    (p : Prop) [Decidable p] :
    monadLift (guard p : m Unit) = (guard p : n Unit) := by
  simp only [guard, apply_ite (f := monadLift), liftM_pure, monadLift_failure]

/-- A lawful lift that preserves `<|>` preserves `optional`. -/
@[simp]
theorem monadLift_optional [AlternativeMonad m] [AlternativeMonad n]
    [LawfulMonad m] [LawfulMonad n] [MonadLift m n] [LawfulAlternativeLift m n]
    [LawfulMonadLift m n]
    (x : m α) : monadLift (optional x) = optional (monadLift x : n α) := by
  simp only [optional, monadLift_orElse, liftM_map, liftM_pure]

namespace Option

/-- A lawful lift commutes with `Option.elimM`. -/
@[simp]
theorem monadLift_elimM [Monad m] [Monad n] [MonadLift m n] [LawfulMonadLift m n] (x : m (Option α)) (y : m β) (z : α → m β) :
      monadLift (Option.elimM x y z) =
        Option.elimM (monadLift x : n (Option α)) (monadLift y) (fun x => monadLift (z x)) :=
  (monadLift_bind _ _).trans (by congr; funext x; cases x <;> rfl)

end Option
