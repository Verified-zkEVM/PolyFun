/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.Bounded
public import PolyFun.PFunctor.Free.Fold

/-!
# Bounded realizations of finite free-monad folds

Many finite interactive programs repeatedly ask the same typed query, fold each
answer into an accumulator, and return a final readout. `FreeM.foldr` packages
that syntax; this file supplies the corresponding countdown-state
`DynComputation` and its bounded-implementation theorem. It is generic in the
polynomial functor and contains no oracle, probability, or complexity policy.
-/

@[expose] public section

universe uA uB uState uOutput

namespace PFunctor

variable {p : PFunctor.{uA, uB}} {state : Type uState} {output : Type uOutput}

namespace FreeM

/-- A right fold whose every step asks one fixed query has `rounds` as a
branchwise query upper bound. The bound need not be minimal when a reachable
query has no possible answer. -/
theorem isTotalRollBound_foldr_lift (position : p.A)
    (step : state → ℕ → p.B position → state)
    (readout : state → output) (rounds : ℕ) (accumulator : state) :
    (FreeM.foldr position step readout rounds accumulator).IsTotalRollBound rounds := by
  induction rounds generalizing accumulator with
  | zero =>
      rw [FreeM.foldr_zero]
      exact FreeM.isTotalRollBound_pure (readout accumulator) 0
  | succ rounds induction =>
      rw [FreeM.foldr_succ]
      simp only [← FreeM.liftBind_eq]
      exact ⟨Nat.succ_pos rounds, fun answer ↦ induction (step accumulator rounds answer)⟩

end FreeM

namespace DynSystem.DynComputation

/-- A hidden-state machine for a fixed-query `FreeM.foldr`. Its state is the
remaining round counter paired with the accumulator. -/
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

/-- Unrolling from a state with `remaining` rounds gives the corresponding
right fold followed by the final readout whenever the supplied fuel is
sufficient. -/
theorem unroll_boundedFold (position : p.A)
    (step : state → ℕ → p.B position → state) (readout : state → output)
    (rounds : ℕ) :
    ∀ (remaining fuel : ℕ) (withinRounds : remaining ≤ rounds) (accumulator : state),
      remaining ≤ fuel →
      (boundedFold position step readout rounds).unroll fuel
          (⟨remaining, Nat.lt_succ_of_le withinRounds⟩, accumulator) =
        FreeM.foldr position step (some ∘ readout) remaining accumulator
  | 0, fuel, _, accumulator, _ => by
      rw [(boundedFold position step readout rounds).unroll_return fuel _
        (readout accumulator)
        (view_boundedFold_zero position step readout rounds rfl)]
      simp only [FreeM.foldr_zero, Function.comp_apply, FreeM.pure_eq_pure]
  | remaining + 1, 0, _, _, enoughFuel => absurd enoughFuel (by omega)
  | remaining + 1, fuel + 1, withinRounds, accumulator, enoughFuel => by
      rw [(boundedFold position step readout rounds).unroll_query_succ fuel _
        position _ (view_boundedFold_succ position step readout rounds
          (current := ⟨_, accumulator⟩) (by simp)),
        FreeM.foldr_succ]
      simp only [← FreeM.liftBind_eq]
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
      (fun initial ↦ FreeM.foldr position step readout rounds initial) rounds := by
  intro initial
  rw [FreeM.map_foldr]
  exact unroll_boundedFold position step readout rounds
    rounds rounds le_rfl initial le_rfl

end DynSystem.DynComputation
end PFunctor
