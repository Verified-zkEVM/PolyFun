/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Path.Bounded

/-! # Bounded path-length examples -/

@[expose] public section

open PFunctor

namespace PFunctor.FreeM.PathBoundedExamples

/- Lean compares the concrete polynomial and path indices below at implicit
transparency. -/
attribute [local implicit_reducible] PFunctor.monomial FreeM.bind

/-- A small interface whose first Boolean answer selects a one- or two-step
branch. -/
abbrev BranchP : PFunctor := Bool y^ Bool

def branchTail : Bool → FreeM BranchP Nat
  | false => FreeM.pure 3
  | true => FreeM.liftBind true fun _ => FreeM.pure 7

def branchProgram : FreeM BranchP Nat :=
  FreeM.liftBind false branchTail

def shortPath : Path branchProgram :=
  ⟨false, ⟨⟩⟩

def longPath : Path branchProgram :=
  ⟨true, false, ⟨⟩⟩

def relabelledLongPath : Path (FreeM.map Nat.succ branchProgram) :=
  ⟨true, false, ⟨⟩⟩

example : Path.length branchProgram shortPath = 1 := rfl

example : Path.length branchProgram longPath = 2 := rfl

/-- Pulling a path through a leaf relabelling preserves its exact query
length. -/
example : Path.length branchProgram
    (Path.pullMap Nat.succ branchProgram relabelledLongPath) = 2 := by
  rw [Path.length_pullMap]
  rfl

/-- The nondependent projection reports the exact branch-dependent path
length while retaining the original query structure. -/
example : withPathLength branchProgram =
    FreeM.liftBind (P := BranchP) false fun first : Bool =>
      match first with
      | false => (FreeM.pure 1 : FreeM BranchP Nat)
      | true => FreeM.liftBind (P := BranchP) true fun _ => FreeM.pure 2 := by
  rw [branchProgram, FreeM.liftBind_eq, withPathLength_liftBind]
  apply congrArg (FreeM.liftBind (P := BranchP) false)
  funext first
  cases first with
  | false => rfl
  | true =>
      rw [show branchTail true =
        (FreeM.lift (P := BranchP) true).bind fun _ : Bool => FreeM.pure 7 from rfl,
        withPathLength_liftBind]
      rfl

theorem branchProgram_bound : branchProgram.IsTotalRollBound 2 := by
  rw [branchProgram, FreeM.liftBind_eq, isTotalRollBound_lift_bind_iff]
  refine ⟨by omega, fun answer => ?_⟩
  cases answer with
  | false => simp [branchTail]
  | true =>
      rw [show branchTail true =
        (FreeM.liftBind true fun _ : Bool => FreeM.pure 7) from rfl,
        FreeM.liftBind_eq, isTotalRollBound_lift_bind_iff]
      exact ⟨by omega, fun _ => by simp⟩

example : Path.length branchProgram longPath ≤ 2 :=
  Path.length_le_of_isTotalRollBound branchProgram branchProgram_bound longPath

end PFunctor.FreeM.PathBoundedExamples
