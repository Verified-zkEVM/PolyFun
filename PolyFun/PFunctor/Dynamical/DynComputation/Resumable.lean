/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation.Bounded

/-!
# Resumable bounded execution

A chunk either returns a value or retains the exact residual machine state. Terminal
observation costs no fuel. The syntactic API keeps the state, input, result, position,
and direction universes independent. Interpretation aligns state, result, and direction
universes because the handler's monad must carry the residual state as well as responses.
-/

public section

namespace PFunctor.DynSystem.DynComputation

universe u v w uState uA uB uα uβ

/-- A completed return value or the exact state at which execution paused. -/
inductive Chunk (S : Type uState) (β : Type uβ) where
  | done (value : β)
  | paused (state : S)

/-- Forget the residual state, recovering PolyFun's bounded-run observation. -/
@[expose] def Chunk.result {S : Type uState} {β : Type uβ} : Chunk S β → Option β
  | .done value => some value
  | .paused _ => none

section Syntax

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

/-- A finite free program which retains the residual state when its budget is exhausted. -/
@[expose] def unrollChunk (machine : DynComputation.{uState} p α β) :
    Nat → machine.State → FreeM p (Chunk machine.State β)
  | 0, state => match machine.view state with
    | .inl value => .pure (.done value)
    | .inr _ => .pure (.paused state)
  | fuel + 1, state => match machine.view state with
    | .inl value => .pure (.done value)
    | .inr ⟨position, next⟩ =>
      .liftBind position (fun answer => unrollChunk machine fuel (next answer))

theorem unrollChunk_result (machine : DynComputation.{uState} p α β) (fuel : Nat)
    (state : machine.State) :
    FreeM.map Chunk.result (unrollChunk machine fuel state) = machine.unroll fuel state := by
  induction fuel generalizing state with
  | zero =>
    cases h : machine.view state <;> simp [unrollChunk, DynComputation.unroll, Chunk.result, h]
  | succ fuel ih =>
    cases h : machine.view state with
    | inl value => simp [unrollChunk, DynComputation.unroll, Chunk.result, h]
    | inr query =>
      rcases query with ⟨position, next⟩
      simp only [unrollChunk, DynComputation.unroll, h]
      change FreeM.liftBind position (fun answer =>
        FreeM.map Chunk.result (unrollChunk machine fuel (next answer))) = _
      congr 1
      funext answer
      exact ih (next answer)

/-- Resume a paused computation without invoking any of its already performed queries. -/
@[expose] def resumeChunk (machine : DynComputation.{uState} p α β) (fuel : Nat) :
    Chunk machine.State β → FreeM p (Chunk machine.State β)
  | .done value => .pure (.done value)
  | .paused state => unrollChunk machine fuel state

theorem unrollChunk_add (machine : DynComputation.{uState} p α β) (first second : Nat)
    (state : machine.State) :
    (unrollChunk machine first state >>= resumeChunk machine second) =
      unrollChunk machine (first + second) state := by
  induction first generalizing state with
  | zero =>
    cases h : machine.view state with
    | inl value => cases second <;> simp [unrollChunk, resumeChunk, h]
    | inr query => simp [unrollChunk, resumeChunk, h]
  | succ first ih =>
    cases h : machine.view state with
    | inl value => simp [unrollChunk, resumeChunk, Nat.succ_add, h]
    | inr query =>
      rcases query with ⟨position, next⟩
      simp only [unrollChunk, h, Nat.succ_add]
      change FreeM.liftBind position (fun answer =>
        unrollChunk machine first (next answer) >>= resumeChunk machine second) = _
      congr 1
      funext answer
      exact ih (next answer)

theorem unrollChunk_zero (machine : DynComputation.{uState} p α β)
    (state : machine.State) :
    machine.unrollChunk 0 state = match machine.view state with
      | .inl value => .pure (.done value)
      | .inr _ => .pure (.paused state) := rfl

theorem unrollChunk_succ (machine : DynComputation.{uState} p α β)
    (fuel : Nat) (state : machine.State) :
    machine.unrollChunk (fuel + 1) state = match machine.view state with
      | .inl value => .pure (.done value)
      | .inr ⟨position, next⟩ =>
        .liftBind position (fun answer => machine.unrollChunk fuel (next answer)) := rfl

@[simp] theorem resumeChunk_done (machine : DynComputation.{uState} p α β)
    (fuel : Nat) (value : β) : machine.resumeChunk fuel (.done value) = .pure (.done value) := rfl

@[simp] theorem resumeChunk_paused (machine : DynComputation.{uState} p α β)
    (fuel : Nat) (state : machine.State) :
    machine.resumeChunk fuel (.paused state) = machine.unrollChunk fuel state := rfl

end Syntax

section Interpretation

variable {p : PFunctor.{uA, u}} {α : Type uα} {β : Type u}

/-- Interpret one bounded chunk through any monadic handler, including Lean IO. -/
def runChunk {m : Type u → Type v} [Monad m] (machine : DynComputation.{u} p α β)
    (handler : Handler m p) (fuel : Nat) (state : machine.State) :
    m (Chunk machine.State β) := (unrollChunk machine fuel state).liftM handler

theorem runChunk_result {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (machine : DynComputation.{u} p α β) (handler : Handler m p)
    (fuel : Nat) (state : machine.State) :
    Chunk.result <$> runChunk machine handler fuel state = machine.runWith handler fuel state := by
  rw [runChunk, ← FreeM.liftM_map, ← FreeM.map_eq_map, unrollChunk_result]
  rfl

theorem runChunk_add {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (machine : DynComputation.{u} p α β) (handler : Handler m p)
    (first second : Nat) (state : machine.State) :
    (runChunk machine handler first state >>= fun result =>
      (resumeChunk machine second result).liftM handler) =
        runChunk machine handler (first + second) state := by
  rw [runChunk, ← FreeM.liftM_bind, unrollChunk_add]
  rfl

/-- Transporting the target monad commutes with interpretation of a chunk. -/
theorem runChunk_natural {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Monad n] (machine : DynComputation.{u} p α β)
    (handler : Handler m p) (transform : m →ᵐ n) (fuel : Nat) (state : machine.State) :
    transform (machine.runChunk handler fuel state) =
      machine.runChunk (Handler.mapTarget (fun value => transform value) handler) fuel state :=
  FreeM.liftM_natural handler transform _

end Interpretation

end PFunctor.DynSystem.DynComputation
