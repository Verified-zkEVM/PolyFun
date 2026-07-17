/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Resumption.Truncate

/-! # Finite resumption truncation examples -/

@[expose] public section

open PFunctor

namespace PFunctor.Resumption

universe uA uB uβ

def truncateUniverseCanary {p : PFunctor.{uA, uB}} {β : Type uβ}
    (k : ℕ) (computation : Resumption p β) : FreeM p (Option β) :=
  truncate k computation

def oneQueryTree : Resumption X Nat :=
  query PUnit.unit fun _ => pure 7

example : truncate 0 oneQueryTree = FreeM.pure none := by
  simp [oneQueryTree]

example : truncate 1 oneQueryTree =
    FreeM.liftBind PUnit.unit fun _ => FreeM.pure (some 7) := by
  simp [oneQueryTree]

example : (truncate 1 oneQueryTree).IsTotalRollBound 1 :=
  isTotalRollBound_truncate 1 oneQueryTree

/-- A nontrivial interface whose two answers select different continuations. -/
def branchP : PFunctor.{0, 0} := monomial Bool Bool

def secondProgram : Bool → FreeM branchP Nat
  | false => FreeM.pure 3
  | true => FreeM.liftBind true fun second : Bool =>
      FreeM.pure (if second = true then 11 else 12)

def twoLevelProgram : FreeM branchP Nat :=
  FreeM.liftBind false secondProgram

def twoLevelTree : Resumption branchP Nat :=
  FreeM.toResumption twoLevelProgram

@[simp] theorem dest_twoLevelTree : dest twoLevelTree =
    Sum.inr ⟨false, fun first : Bool =>
      FreeM.toResumption (secondProgram first)⟩ := by
  unfold twoLevelTree twoLevelProgram
  exact FreeM.dest_toResumption_liftBind (p := branchP) false secondProgram

example : truncate 0 twoLevelTree = FreeM.pure none := by
  rw [truncate_zero, dest_twoLevelTree]

/-- At one query, the short branch returns while the long branch has an
observable cutoff leaf. -/
example : truncate 1 twoLevelTree =
    FreeM.liftBind false fun first : Bool =>
      FreeM.pure (if first = true then none else some 3) := by
  rw [truncate_succ, dest_twoLevelTree]
  change FreeM.liftBind false
      (fun first : Bool => truncate 0 (FreeM.toResumption (secondProgram first))) = _
  congr 1
  funext first
  cases first with
  | false => simp [secondProgram]
  | true =>
      rw [truncate_zero]
      unfold secondProgram
      rw [FreeM.dest_toResumption_liftBind]
      change FreeM.pure none = FreeM.pure none
      rfl

theorem twoLevelProgram_bound : twoLevelProgram.IsTotalRollBound 2 := by
  unfold twoLevelProgram
  rw [FreeM.liftBind_eq, FreeM.isTotalRollBound_lift_bind_iff]
  refine ⟨by omega, fun first => ?_⟩
  cases first
  · simp [secondProgram]
  · unfold secondProgram
    rw [FreeM.liftBind_eq, FreeM.isTotalRollBound_lift_bind_iff]
    refine ⟨by omega, fun second => ?_⟩
    simp

example : truncate 2 twoLevelTree = FreeM.map some twoLevelProgram :=
  truncate_toResumption_eq_map_some twoLevelProgram_bound

example : truncate 2 twoLevelTree = FreeM.map some twoLevelProgram ↔
    twoLevelTree = FreeM.toResumption twoLevelProgram ∧
      twoLevelProgram.IsTotalRollBound 2 :=
  truncate_eq_map_some_iff 2 twoLevelTree twoLevelProgram

example : truncate 5 twoLevelTree = FreeM.map some twoLevelProgram :=
  truncate_eq_map_some_of_le
    (truncate_toResumption_eq_map_some twoLevelProgram_bound) (by omega)

/-- A query with no directions is a finite one-node program; its continuation
obligation and its successful factorization are both vacuous. -/
def emptyDirectionP : PFunctor.{0, 0} := monomial Unit PEmpty

def emptyDirectionProgram : FreeM emptyDirectionP Nat :=
  FreeM.liftBind () PEmpty.elim

def emptyDirectionTree : Resumption emptyDirectionP Nat :=
  query () PEmpty.elim

example : truncate 1 emptyDirectionTree = FreeM.map some emptyDirectionProgram := by
  have htree : emptyDirectionTree = FreeM.toResumption emptyDirectionProgram := by
    unfold emptyDirectionTree emptyDirectionProgram
    apply Resumption.eq_of_dest_eq
    rw [Resumption.dest_query, FreeM.dest_toResumption_liftBind]
    apply congrArg Sum.inr
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext direction
      exact PEmpty.elim direction
  rw [htree]
  apply truncate_toResumption_eq_map_some
  unfold emptyDirectionProgram
  rw [FreeM.liftBind_eq, FreeM.isTotalRollBound_lift_bind_iff]
  exact ⟨by omega, fun direction => PEmpty.elim direction⟩

/-- An infinite visible-query loop has a finite cutoff at every fuel. -/
def queryLoop : Resumption branchP Nat :=
  Resumption.corec
    (fun _ : Unit => Sum.inr ⟨false, fun _ : Bool => ()⟩) ()

@[simp] theorem dest_queryLoop : dest queryLoop =
    Sum.inr ⟨false, fun _ : Bool => queryLoop⟩ := by
  unfold queryLoop
  rw [Resumption.dest_corec]
  apply congrArg Sum.inr
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext direction
    rfl

def loopCut : ℕ → FreeM branchP (Option Nat)
  | 0 => FreeM.pure none
  | k + 1 => FreeM.liftBind false fun _ : Bool => loopCut k

theorem truncate_two_queryLoop : truncate 2 queryLoop = loopCut 2 := by
  rw [truncate_succ, dest_queryLoop]
  change FreeM.liftBind false (fun _ : Bool => truncate 1 queryLoop) =
    FreeM.liftBind false (fun _ : Bool => loopCut 1)
  congr 1

def followFalse {α : Type} : FreeM branchP α → α
  | .pure result => result
  | .liftBind _ next => followFalse (next false)

@[simp] theorem followFalse_map {α γ : Type} (f : α → γ)
    (program : FreeM branchP α) :
    followFalse (FreeM.map f program) = f (followFalse program) := by
  induction program with
  | pure result => rfl
  | lift_bind position next ih => exact ih false

example (program : FreeM branchP Nat) :
    truncate 2 queryLoop ≠ FreeM.map some program := by
  intro h
  rw [truncate_two_queryLoop] at h
  have hobserved := congrArg followFalse h
  change none = followFalse (FreeM.map some program) at hobserved
  rw [followFalse_map] at hobserved
  cases hobserved

end PFunctor.Resumption
