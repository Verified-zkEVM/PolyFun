/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import PolyFun.PFunctor.Free.Basic

/-!
# Finite interaction folds in the free polynomial monad

`FreeM.foldl` and `FreeM.foldr` repeatedly ask one fixed query, update an
accumulator from each answer, and apply a final readout. The supplied natural
number index increases from `0` for `foldl` and decreases to `0` for `foldr`.
They are built from `Fin.foldlM` and `Fin.foldrM`; the map laws fuse
postprocessing into the final readout.
-/

@[expose] public section

universe uA uB uState uOutput uOutput₂

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {state : Type uState}
  {output : Type uOutput} {output₂ : Type uOutput₂}

/-- Repeatedly ask `position`, folding its answers into an accumulator from
index `0` upwards, then apply `readout` to the final accumulator. -/
def foldl (position : P.A) (step : state → Nat → P.B position → state)
    (readout : state → output) (rounds : Nat) (accumulator : state) :
    FreeM P output :=
  FreeM.map readout <| Fin.foldlM rounds
    (fun current round =>
      (FreeM.lift position).bind fun answer => pure (step current round answer))
    accumulator

/-- `FreeM.foldl` is the fixed-query specialization of `Fin.foldlM`, followed
by the final readout. -/
theorem foldl_eq_map_fin_foldlM (position : P.A)
    (step : state → Nat → P.B position → state) (readout : state → output)
    (rounds : Nat) (accumulator : state) :
    foldl position step readout rounds accumulator =
      FreeM.map readout (Fin.foldlM rounds
        (fun current round =>
          (FreeM.lift position).bind fun answer => pure (step current round answer))
        accumulator) :=
  rfl

@[simp, freeM_unfold]
theorem foldl_zero (position : P.A) (step : state → Nat → P.B position → state)
    (readout : state → output) (accumulator : state) :
    foldl position step readout 0 accumulator = pure (readout accumulator) :=
  by simp only [foldl, Fin.foldlM_zero, FreeM.map_pure]

@[simp, freeM_unfold]
theorem foldl_succ (position : P.A) (step : state → Nat → P.B position → state)
    (readout : state → output) (rounds : Nat) (accumulator : state) :
    foldl position step readout (rounds + 1) accumulator =
      (FreeM.lift position).bind fun answer =>
        foldl position
          (fun current round nextAnswer => step current (round + 1) nextAnswer)
          readout rounds (step accumulator 0 answer) := by
  rw [foldl, Fin.foldlM_succ]
  simp only [Fin.val_zero]
  rw [FreeM.monad_bind_def, FreeM.map_bind]
  simp only [FreeM.liftBind_bind, FreeM.pure_bind]
  apply congrArg (fun next => (FreeM.lift position).bind next)
  funext answer
  rw [foldl]
  congr 2

/-- Repeatedly ask `position`, folding its answers into an accumulator from
index `rounds - 1` down to `0`, then apply `readout` to the final accumulator. -/
def foldr (position : P.A) (step : state → Nat → P.B position → state)
    (readout : state → output) (rounds : Nat) (accumulator : state) :
    FreeM P output :=
  FreeM.map readout <| Fin.foldrM rounds
    (fun round current =>
      (FreeM.lift position).bind fun answer => pure (step current round answer))
    accumulator

/-- `FreeM.foldr` is the fixed-query specialization of `Fin.foldrM`, followed
by the final readout. -/
theorem foldr_eq_map_fin_foldrM (position : P.A)
    (step : state → Nat → P.B position → state) (readout : state → output)
    (rounds : Nat) (accumulator : state) :
    foldr position step readout rounds accumulator =
      FreeM.map readout (Fin.foldrM rounds
        (fun round current =>
          (FreeM.lift position).bind fun answer => pure (step current round answer))
        accumulator) :=
  rfl

@[simp, freeM_unfold]
theorem foldr_zero (position : P.A) (step : state → Nat → P.B position → state)
    (readout : state → output) (accumulator : state) :
    foldr position step readout 0 accumulator = pure (readout accumulator) :=
  by simp only [foldr, Fin.foldrM_zero, FreeM.map_pure]

@[simp, freeM_unfold]
theorem foldr_succ (position : P.A) (step : state → Nat → P.B position → state)
    (readout : state → output) (rounds : Nat) (accumulator : state) :
    foldr position step readout (rounds + 1) accumulator =
      (FreeM.lift position).bind fun answer =>
        foldr position step readout rounds (step accumulator rounds answer) := by
  rw [foldr, Fin.foldrM_succ_last]
  simp only [Fin.val_last]
  rw [FreeM.monad_bind_def, FreeM.map_bind]
  simp only [FreeM.liftBind_bind, FreeM.pure_bind]
  apply congrArg (fun next => (FreeM.lift position).bind next)
  funext answer
  rw [foldr]
  congr 2

/-- Mapping the result of a left interaction fold is equivalent to composing
the map into its final readout. -/
@[simp]
theorem map_foldl (f : output → output₂) (position : P.A)
    (step : state → Nat → P.B position → state) (readout : state → output)
    (rounds : Nat) (accumulator : state) :
    FreeM.map f (foldl position step readout rounds accumulator) =
      foldl position step (f ∘ readout) rounds accumulator := by
  induction rounds generalizing accumulator step with
  | zero => simp only [foldl_zero, FreeM.map_pure, Function.comp_apply]
  | succ rounds induction =>
      rw [foldl_succ, foldl_succ, FreeM.map_lift_bind]
      exact congrArg (fun next => (FreeM.lift position).bind next)
        (funext fun answer => induction _ _)

/-- Mapping the result of a right interaction fold is equivalent to composing
the map into its final readout. -/
@[simp]
theorem map_foldr (f : output → output₂) (position : P.A)
    (step : state → Nat → P.B position → state) (readout : state → output)
    (rounds : Nat) (accumulator : state) :
    FreeM.map f (foldr position step readout rounds accumulator) =
      foldr position step (f ∘ readout) rounds accumulator := by
  induction rounds generalizing accumulator with
  | zero => simp only [foldr_zero, FreeM.map_pure, Function.comp_apply]
  | succ rounds induction =>
      rw [foldr_succ, foldr_succ, FreeM.map_lift_bind]
      exact congrArg (fun next => (FreeM.lift position).bind next)
        (funext fun answer => induction _)

end PFunctor.FreeM
