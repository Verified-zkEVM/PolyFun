/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.Bounded

/-!
# Bounded folds over a fixed interaction position

Many finite interactive programs repeatedly ask the same typed query, fold each
answer into an accumulator, and return a readout. This file packages that syntax,
its countdown-state `DynComputation`, and a bounded-implementation theorem.
It is generic in the polynomial functor and contains no oracle, probability, or
complexity policy.
-/

@[expose] public section

universe uA uB uState uOutput

namespace PFunctor
namespace DynSystem.DynComputation

variable {p : PFunctor.{uA, uB}} {state : Type uState} {output : Type uOutput}

/-- Ask `position` along every available branch for up to `rounds` rounds,
folding each answer into `accumulator`.
The supplied index counts down: the first answer receives `rounds - 1` and the
last answer receives `0`. -/
def boundedFoldProgram (position : p.A)
    (step : state → ℕ → p.B position → state) (readout : state → output) :
    ℕ → state → FreeM p output
  | 0, accumulator => FreeM.pure (readout accumulator)
  | rounds + 1, accumulator =>
      FreeM.liftBind position fun answer =>
        boundedFoldProgram position step readout rounds (step accumulator rounds answer)

@[simp] theorem boundedFoldProgram_zero (position : p.A)
    (step : state → ℕ → p.B position → state) (readout : state → output)
    (accumulator : state) :
    boundedFoldProgram position step readout 0 accumulator =
      FreeM.pure (readout accumulator) := rfl

@[simp] theorem boundedFoldProgram_succ (position : p.A)
    (step : state → ℕ → p.B position → state) (readout : state → output)
    (rounds : ℕ) (accumulator : state) :
    boundedFoldProgram position step readout (rounds + 1) accumulator =
      FreeM.liftBind position fun answer =>
        boundedFoldProgram position step readout rounds (step accumulator rounds answer) := rfl

/-- The construction parameter is a branchwise query upper bound. It need not
be minimal when a reachable query has no possible answer. -/
theorem isTotalRollBound_boundedFoldProgram (position : p.A)
    (step : state → ℕ → p.B position → state) (readout : state → output)
    (rounds : ℕ) (accumulator : state) :
    (boundedFoldProgram position step readout rounds accumulator).IsTotalRollBound rounds := by
  induction rounds generalizing accumulator with
  | zero => trivial
  | succ rounds induction =>
    exact ⟨Nat.succ_pos rounds, fun answer ↦ induction (step accumulator rounds answer)⟩

/-- A hidden-state machine for `boundedFoldProgram`. Its state is the remaining
round counter paired with the accumulator. -/
@[reducible] def boundedFold (position : p.A)
    (step : state → ℕ → p.B position → state) (readout : state → output)
    (rounds : ℕ) : DynComputation p state output :=
  ofStep (S := Fin (rounds + 1) × state)
    (fun current =>
      if _isDone : (current.1 : ℕ) = 0 then
        Sum.inl (readout current.2)
      else
        Sum.inr ⟨position, fun answer =>
          (⟨(current.1 : ℕ) - 1,
            lt_of_le_of_lt (Nat.sub_le _ _) current.1.isLt⟩,
            step current.2 ((current.1 : ℕ) - 1) answer)⟩)
    (fun initial => (Fin.last rounds, initial))

theorem view_boundedFold_zero (position : p.A)
    (step : state → ℕ → p.B position → state) (readout : state → output)
    (rounds : ℕ) {current : Fin (rounds + 1) × state}
    (isDone : (current.1 : ℕ) = 0) :
    (boundedFold position step readout rounds).view current =
      Sum.inl (readout current.2) := by
  rw [view_ofStep, dif_pos isDone]

theorem view_boundedFold_succ (position : p.A)
    (step : state → ℕ → p.B position → state) (readout : state → output)
    (rounds : ℕ) {current : Fin (rounds + 1) × state}
    (notDone : ¬(current.1 : ℕ) = 0) :
    (boundedFold position step readout rounds).view current =
      Sum.inr ⟨position, fun answer =>
        (⟨(current.1 : ℕ) - 1,
          lt_of_le_of_lt (Nat.sub_le _ _) current.1.isLt⟩,
          step current.2 ((current.1 : ℕ) - 1) answer)⟩ := by
  rw [view_ofStep, dif_neg notDone]

/-- Unrolling from a state with `remaining` rounds gives the corresponding fold
program whenever the supplied fuel is sufficient. -/
theorem unroll_boundedFold (position : p.A)
    (step : state → ℕ → p.B position → state) (readout : state → output)
    (rounds : ℕ) :
    ∀ (remaining fuel : ℕ) (withinRounds : remaining ≤ rounds) (accumulator : state),
      remaining ≤ fuel →
      (boundedFold position step readout rounds).unroll fuel
          (⟨remaining, Nat.lt_succ_of_le withinRounds⟩, accumulator) =
        FreeM.map some
          (boundedFoldProgram position step readout remaining accumulator)
  | 0, fuel, _, accumulator, _ => by
      rw [(boundedFold position step readout rounds).unroll_return fuel _
        (readout accumulator)
        (view_boundedFold_zero position step readout rounds rfl)]
      rfl
  | remaining + 1, 0, _, _, enoughFuel => absurd enoughFuel (by omega)
  | remaining + 1, fuel + 1, withinRounds, accumulator, enoughFuel => by
      rw [(boundedFold position step readout rounds).unroll_query_succ fuel _
        position _ (view_boundedFold_succ position step readout rounds
          (current := ⟨_, accumulator⟩) (by simp))]
      exact congrArg (FreeM.liftBind position)
        (funext fun answer =>
          unroll_boundedFold position step readout rounds remaining fuel
            (by omega) (step accumulator remaining answer) (by omega))

/-- The countdown-state fold machine implements the fold program at its declared
interaction fuel. -/
theorem implementsWithin_boundedFold (position : p.A)
    (step : state → ℕ → p.B position → state) (readout : state → output)
    (rounds : ℕ) :
    (boundedFold position step readout rounds).ImplementsWithin
      (fun initial ↦ boundedFoldProgram position step readout rounds initial) rounds :=
  fun initial => unroll_boundedFold position step readout rounds
    rounds rounds le_rfl initial le_rfl

end DynSystem.DynComputation
end PFunctor
