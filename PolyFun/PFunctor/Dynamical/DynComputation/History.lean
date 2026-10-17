/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.Resumable
public import Mathlib.Data.Fin.Tuple.Basic

/-!+# Finite histories of residual execution

`unrollHistory` records the initialized zero-fuel observation and every subsequent
chunk. It extends a history by resuming its last chunk for one query, so previous
effects are never replayed. Returned values persist through the remaining time
coordinates. This is an observation of the resumable runner, with the same final
chunk, rather than an additional machine representation.
-/

public section

namespace PFunctor.DynSystem.DynComputation

universe uState uA uB uα uβ

variable {P : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

/-- Record all residual observations through the supplied query budget. -/
@[expose] def unrollHistory (machine : DynComputation.{uState} P α β) :
    (fuel : Nat) → machine.State → FreeM P (Fin (fuel + 1) → Chunk machine.State β)
  | 0, state => FreeM.map (fun chunk _ => chunk) (machine.unrollChunk 0 state)
  | fuel + 1, state => do
    let history ← machine.unrollHistory fuel state
    FreeM.map (Fin.snoc history) (machine.resumeChunk 1 (history (Fin.last fuel)))

/-- The initial history observes a terminal value even without query fuel. -/
theorem unrollHistory_zero (machine : DynComputation.{uState} P α β)
    (state : machine.State) :
    machine.unrollHistory 0 state =
      FreeM.map (fun chunk _ => chunk) (machine.unrollChunk 0 state) := rfl

/-- Extending a history resumes its retained chunk, including an absorbing return. -/
theorem unrollHistory_succ (machine : DynComputation.{uState} P α β)
    (fuel : Nat) (state : machine.State) :
    machine.unrollHistory (fuel + 1) state =
      (machine.unrollHistory fuel state >>= fun history =>
        FreeM.map (Fin.snoc history) (machine.resumeChunk 1 (history (Fin.last fuel)))) := rfl

/-- The last recorded observation is exactly the ordinary bounded runner's residual. -/
theorem map_unrollHistory_last (machine : DynComputation.{uState} P α β)
    (fuel : Nat) (state : machine.State) :
    FreeM.map (fun history => history (Fin.last fuel)) (machine.unrollHistory fuel state) =
      machine.unrollChunk fuel state := by
  induction fuel with
  | zero => simp [unrollHistory, FreeM.map_eq_map, Functor.map_map, id_map']
  | succ fuel ih =>
    rw [unrollHistory_succ]
    simp only [FreeM.map_eq_map, map_bind, Functor.map_map, Fin.snoc_last,
      id_map']
    rw [← bind_map_left, ← FreeM.map_eq_map, ih, unrollChunk_add]

/-- A terminal machine produces a constant history without performing any query. -/
theorem unrollHistory_of_view_return (machine : DynComputation.{uState} P α β)
    {state : machine.State} {value : β} (h : machine.view state = .inl value) (fuel : Nat) :
    machine.unrollHistory fuel state = .pure (fun _ => .done value) := by
  induction fuel with
  | zero => simp [unrollHistory_zero, unrollChunk_zero, h]
  | succ fuel ih =>
    rw [unrollHistory_succ, ih]
    change FreeM.pure (Fin.snoc (α := fun _ => Chunk machine.State β)
      (fun _ : Fin (fuel + 1) => Chunk.done value) (Chunk.done value)) = _
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Fin.snoc_last _ _
    · exact Fin.snoc_castSucc _ _ _

end PFunctor.DynSystem.DynComputation
