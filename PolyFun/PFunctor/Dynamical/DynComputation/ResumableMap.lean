/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.History

/-!
# Resumable execution under input and result maps

Input reindexing changes only initialization. Mapping a result preserves every
residual state, query and time coordinate, and maps returned chunks pointwise.
The laws apply to joint histories as well as single bounded observations.
-/

public section

namespace PFunctor.DynSystem.DynComputation

universe u uA uB uα uβ uγ

variable {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} {γ : Type uγ}

/-- Input reindexing leaves execution from a retained state unchanged. -/
theorem unrollChunk_contramapInput (machine : DynComputation.{u} P α β) (f : γ → α)
    (fuel : Nat) (state : machine.State) :
    (machine.contramapInput f).unrollChunk fuel state = machine.unrollChunk fuel state := by
  induction fuel generalizing state with
  | zero =>
    rw [(machine.contramapInput f).unrollChunk_zero, machine.unrollChunk_zero,
      contramapInput_view]
    cases machine.view state <;> rfl
  | succ fuel ih =>
    rw [(machine.contramapInput f).unrollChunk_succ, machine.unrollChunk_succ,
      contramapInput_view]
    cases machine.view state with
    | inl _ => rfl
    | inr query =>
      cases query with
      | mk a next => exact congrArg (FreeM.liftBind a) (funext fun answer => ih (next answer))

/-- Input reindexing leaves a resumed chunk unchanged. -/
theorem resumeChunk_contramapInput (machine : DynComputation.{u} P α β) (f : γ → α)
    (fuel : Nat) (chunk : Chunk machine.State β) :
    (machine.contramapInput f).resumeChunk fuel chunk = machine.resumeChunk fuel chunk := by
  cases chunk with
  | done value => rfl
  | paused state => exact machine.unrollChunk_contramapInput f fuel state

/-- Reindexing the input leaves every retained history coordinate unchanged. -/
theorem unrollHistory_contramapInput (machine : DynComputation.{u} P α β) (f : γ → α)
    (fuel : Nat) (state : machine.State) :
    (machine.contramapInput f).unrollHistory fuel state = machine.unrollHistory fuel state := by
  induction fuel with
  | zero =>
    simp only [unrollHistory_zero, unrollChunk_contramapInput]
  | succ fuel ih =>
    simp only [unrollHistory_succ, ih, resumeChunk_contramapInput]

/-- Mapping returned values commutes with bounded execution and retains suspended states. -/
theorem unrollChunk_mapResult (machine : DynComputation.{u} P α β) (f : β → γ)
    (fuel : Nat) (state : machine.State) :
    (machine.mapResult f).unrollChunk fuel state =
      FreeM.map (Chunk.map id f) (machine.unrollChunk fuel state) := by
  induction fuel generalizing state with
  | zero =>
    simp only [unrollChunk_zero, mapResult_view]
    cases machine.view state <;> rfl
  | succ fuel ih =>
    simp only [unrollChunk_succ, mapResult_view]
    cases machine.view state with
    | inl _ => rfl
    | inr query =>
      cases query with
      | mk a next => exact congrArg (FreeM.liftBind a) (funext fun answer => ih (next answer))

/-- Mapping the final value also commutes with resuming a saved chunk. -/
theorem resumeChunk_mapResult (machine : DynComputation.{u} P α β) (f : β → γ)
    (fuel : Nat) (chunk : Chunk machine.State β) :
    (machine.mapResult f).resumeChunk fuel (chunk.map id f) =
      FreeM.map (Chunk.map id f) (machine.resumeChunk fuel chunk) := by
  cases chunk with
  | done value => rfl
  | paused state => exact machine.unrollChunk_mapResult f fuel state

/-- A result map acts on every time coordinate of a joint execution history. -/
theorem unrollHistory_mapResult (machine : DynComputation.{u} P α β) (f : β → γ)
    (fuel : Nat) (state : machine.State) :
    (machine.mapResult f).unrollHistory fuel state =
      FreeM.map (fun history i => (history i).map id f) (machine.unrollHistory fuel state) := by
  induction fuel with
  | zero =>
    simp only [unrollHistory_zero, unrollChunk_mapResult, FreeM.map_map, Function.comp_def]
  | succ fuel ih =>
    rw [unrollHistory_succ, unrollHistory_succ, ih]
    simp only [← FreeM.bind_eq_bind, FreeM.bind_map, FreeM.map_bind]
    congr 1
    funext history
    dsimp only [Function.comp_def]
    rw [resumeChunk_mapResult]
    simp only [FreeM.map_map]
    congr 1
    funext next i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.comp_apply, Fin.snoc_last]
    · simp only [Function.comp_apply, Fin.snoc_castSucc]

end PFunctor.DynSystem.DynComputation
