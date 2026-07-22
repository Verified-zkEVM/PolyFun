/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Dynamical.DynComputation
public import PolyFun.PFunctor.Resumption.Truncate
public import PolyFun.PFunctor.Handler

/-!
# Bounded execution of returning dynamical computations

This module gives `DynComputation` its executable bounded semantics. A terminal
view returns without consuming fuel, while each visible query consumes exactly
one unit. The resulting bounded-depth `FreeM` program agrees with canonical resumption
truncation, so the operational definitions inherit an exact semantic
factorization theorem.

`ResolvesIn k state` is the branchwise proposition that every execution from
`state` returns within `k` visible queries. Its converse factorization theorem
uses explicit classical choice: the proposition supplies one well-founded residual
program for every dependent direction, and these witnesses must be assembled
into a single `FreeM` continuation. Recursive executable and resource laws add
no choice. Semantic equalities through the established M-type/resumption
bridges inherit their existing `Classical.choice` footprint.
-/

@[expose] public section

universe u v uA uB uα uβ uγ

namespace PFunctor

namespace DynSystem.DynComputation

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

/-! ## Executable bounded unrolling -/

/-- Unroll a returning computation for at most `k` visible queries. Terminal
readout is free; zero fuel cuts an unresolved query off with `none`. -/
def unroll (M : DynComputation.{u} p α β) : ℕ → M.State → FreeM p (Option β)
  | 0, state => match M.view state with
    | Sum.inl value => FreeM.pure (some value)
    | Sum.inr _ => FreeM.pure none
  | k + 1, state => match M.view state with
    | Sum.inl value => FreeM.pure (some value)
    | Sum.inr ⟨position, next⟩ =>
        FreeM.liftBind position fun direction => M.unroll k (next direction)

theorem unroll_zero (M : DynComputation.{u} p α β) (state : M.State) :
    M.unroll 0 state = match M.view state with
      | Sum.inl value => FreeM.pure (some value)
      | Sum.inr _ => FreeM.pure none := rfl

theorem unroll_succ (M : DynComputation.{u} p α β) (k : ℕ) (state : M.State) :
    M.unroll (k + 1) state = match M.view state with
      | Sum.inl value => FreeM.pure (some value)
      | Sum.inr ⟨position, next⟩ =>
          FreeM.liftBind position fun direction => M.unroll k (next direction) := rfl

@[simp] theorem unroll_return (M : DynComputation.{u} p α β)
    (k : ℕ) (state : M.State) (value : β) (hview : M.view state = Sum.inl value) :
    M.unroll k state = FreeM.pure (some value) := by
  cases k with
  | zero => rw [unroll_zero, hview]
  | succ k => rw [unroll_succ, hview]

theorem unroll_query_zero (M : DynComputation.{u} p α β)
    (state : M.State) (position : p.A) (next : p.B position → M.State)
    (hview : M.view state = Sum.inr ⟨position, next⟩) :
    M.unroll 0 state = FreeM.pure none := by
  rw [unroll_zero, hview]

theorem unroll_query_succ (M : DynComputation.{u} p α β)
    (k : ℕ) (state : M.State) (position : p.A)
    (next : p.B position → M.State)
    (hview : M.view state = Sum.inr ⟨position, next⟩) :
    M.unroll (k + 1) state =
      FreeM.liftBind position fun direction => M.unroll k (next direction) := by
  rw [unroll_succ, hview]

/-- Executable unrolling is exactly canonical truncation of the computation's
coinductive behavior from the same hidden state. -/
theorem unroll_eq_truncate (M : DynComputation.{u} p α β)
    (k : ℕ) (state : M.State) :
    M.unroll k state =
      Resumption.truncate k (M.toDynSystem.behavior state) := by
  induction k generalizing state with
  | zero =>
      rw [unroll_zero, Resumption.truncate_zero, dest_behavior_view]
      cases hview : M.view state with
      | inl value => rfl
      | inr query => rfl
  | succ k ih =>
      rw [unroll_succ, Resumption.truncate_succ, dest_behavior_view]
      cases hview : M.view state with
      | inl value => rfl
      | inr query =>
          rcases query with ⟨position, next⟩
          simp only [Sum.map_inr, PFunctor.map_eq]
          apply congrArg (FreeM.liftBind position)
          funext direction
          exact ih (next direction)

/-- Run a bounded computation from its input-selected initial state. -/
def run (M : DynComputation.{u} p α β) (k : ℕ) (input : α) :
    FreeM p (Option β) :=
  M.unroll k (M.init input)

theorem run_eq_truncate (M : DynComputation.{u} p α β)
    (k : ℕ) (input : α) :
    M.run k input = Resumption.truncate k (M.denote input) :=
  M.unroll_eq_truncate k (M.init input)

@[simp] theorem run_ofFn (f : α → β) (k : ℕ) (input : α) :
    (ofFn (p := p) f).run k input = FreeM.pure (some (f input)) := by
  apply unroll_return
  exact view_init_ofFn f input

/-- Every executable unrolling has total roll bound equal to its fuel. -/
theorem isTotalRollBound_unroll (M : DynComputation.{u} p α β)
    (k : ℕ) (state : M.State) :
    (M.unroll k state).IsTotalRollBound k := by
  rw [unroll_eq_truncate]
  exact Resumption.isTotalRollBound_truncate k (M.toDynSystem.behavior state)

/-! ## Resolution within a uniform query budget -/

/-- Every answer branch from `state` returns within `k` visible queries. -/
def ResolvesIn (M : DynComputation.{u} p α β) : ℕ → M.State → Prop
  | 0, state => match M.view state with
    | Sum.inl _ => True
    | Sum.inr _ => False
  | k + 1, state => match M.view state with
    | Sum.inl _ => True
    | Sum.inr ⟨_, next⟩ => ∀ direction, M.ResolvesIn k (next direction)

theorem resolvesIn_zero (M : DynComputation.{u} p α β) (state : M.State) :
    M.ResolvesIn 0 state ↔ ∃ value, M.view state = Sum.inl value := by
  cases hview : M.view state <;> simp [ResolvesIn, hview]

@[simp] theorem resolvesIn_return (M : DynComputation.{u} p α β)
    (k : ℕ) (state : M.State) (value : β) (hview : M.view state = Sum.inl value) :
    M.ResolvesIn k state := by
  cases k <;> simp [ResolvesIn, hview]

theorem not_resolvesIn_query_zero (M : DynComputation.{u} p α β)
    (state : M.State) (position : p.A) (next : p.B position → M.State)
    (hview : M.view state = Sum.inr ⟨position, next⟩) :
    ¬ M.ResolvesIn 0 state := by
  simp [ResolvesIn, hview]

theorem resolvesIn_query_succ_iff (M : DynComputation.{u} p α β)
    (k : ℕ) (state : M.State) (position : p.A)
    (next : p.B position → M.State)
    (hview : M.view state = Sum.inr ⟨position, next⟩) :
    M.ResolvesIn (k + 1) state ↔
      ∀ direction, M.ResolvesIn k (next direction) := by
  simp [ResolvesIn, hview]

/-- Resolution is monotone in the available query budget. -/
theorem ResolvesIn.mono {M : DynComputation.{u} p α β}
    {j k : ℕ} {state : M.State} (h : M.ResolvesIn j state) (hjk : j ≤ k) :
    M.ResolvesIn k state := by
  induction j generalizing k state with
  | zero =>
      obtain ⟨value, hview⟩ := (M.resolvesIn_zero state).mp h
      exact M.resolvesIn_return k state value hview
  | succ j ih =>
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      cases hview : M.view state with
      | inl value => exact M.resolvesIn_return _ state value hview
      | inr query =>
          rcases query with ⟨position, next⟩
          rw [M.resolvesIn_query_succ_iff j state position next hview] at h
          rw [M.resolvesIn_query_succ_iff k state position next hview]
          exact fun direction => ih (h direction) (by omega)

/-- A `some`-mapped unrolling has no unresolved leaf. This direction is fully
constructive. -/
theorem resolvesIn_of_unroll_eq_map_some {M : DynComputation.{u} p α β} :
    ∀ {k : ℕ} {state : M.State} {program : FreeM p β},
      M.unroll k state = FreeM.map some program → M.ResolvesIn k state
  | 0, state, program, h => by
      cases hview : M.view state with
      | inl value => exact M.resolvesIn_return 0 state value hview
      | inr query =>
          rw [unroll_query_zero M state query.1 query.2 hview] at h
          cases program with
          | pure value => cases h
          | liftBind position next => cases h
  | k + 1, state, program, h => by
      cases hview : M.view state with
      | inl value => exact M.resolvesIn_return (k + 1) state value hview
      | inr query =>
          rcases query with ⟨position, next⟩
          rw [unroll_query_succ M k state position next hview] at h
          cases program with
          | pure value => simp at h
          | liftBind source children =>
              obtain ⟨hposition, hchildren⟩ :=
                (FreeM.liftBind_inj position source
                  (fun direction => M.unroll k (next direction))
                  (fun direction => FreeM.map some (children direction))).mp h
              subst source
              rw [M.resolvesIn_query_succ_iff k state position next hview]
              exact fun direction =>
                resolvesIn_of_unroll_eq_map_some (congrFun hchildren direction)

/-- A resolution proof supplies a bounded-depth value tree whose leaves are all
successful. Classical choice is isolated here to assemble the dependent
family of recursively obtained child trees. -/
theorem unroll_eq_map_some_of_resolvesIn {M : DynComputation.{u} p α β} :
    ∀ {k : ℕ} {state : M.State}, M.ResolvesIn k state →
      ∃ program : FreeM p β, M.unroll k state = FreeM.map some program
  | 0, state, h => by
      obtain ⟨value, hview⟩ := (M.resolvesIn_zero state).mp h
      exact ⟨FreeM.pure value, by rw [unroll_return M 0 state value hview]; rfl⟩
  | k + 1, state, h => by
      cases hview : M.view state with
      | inl value =>
          exact ⟨FreeM.pure value,
            by rw [unroll_return M (k + 1) state value hview]; rfl⟩
      | inr query =>
          rcases query with ⟨position, next⟩
          have hnext : ∀ direction, M.ResolvesIn k (next direction) :=
            (M.resolvesIn_query_succ_iff k state position next hview).mp h
          classical
          choose program hprogram using fun direction =>
            unroll_eq_map_some_of_resolvesIn (hnext direction)
          exact ⟨FreeM.liftBind position program, by
            rw [unroll_query_succ M k state position next hview]
            exact congrArg (FreeM.liftBind position) (funext hprogram)⟩

/-- Resolution within `k` is exactly absence of `none` leaves in the
`k`-query unrolling. -/
theorem resolvesIn_iff_exists_unroll_eq_map_some
    {M : DynComputation.{u} p α β} {k : ℕ} {state : M.State} :
    M.ResolvesIn k state ↔
      ∃ program : FreeM p β, M.unroll k state = FreeM.map some program :=
  ⟨unroll_eq_map_some_of_resolvesIn, fun ⟨_, h⟩ =>
    resolvesIn_of_unroll_eq_map_some h⟩

/-- State-level fixed-program characterization of bounded execution. -/
theorem unroll_eq_map_some_iff (M : DynComputation.{u} p α β)
    (k : ℕ) (state : M.State) (program : FreeM p β) :
    M.unroll k state = FreeM.map some program ↔
      M.toDynSystem.behavior state = FreeM.toResumption program ∧
        program.IsTotalRollBound k := by
  rw [M.unroll_eq_truncate]
  exact Resumption.truncate_eq_map_some_iff k
    (M.toDynSystem.behavior state) program

/-- Internal leaf check used to keep the fixed-program resolution API
constructive without exporting a generic leaf predicate. -/
private def NoCutoff (program : FreeM p (Option β)) : Prop :=
  match program with
  | .pure result => (result.isSome : Prop)
  | .liftBind _ next => ∀ direction, NoCutoff (next direction)

private theorem noCutoff_pure (result : Option β) :
    NoCutoff (FreeM.pure (P := p) result) ↔ (result.isSome : Prop) :=
  Iff.rfl

private theorem noCutoff_liftBind (position : p.A)
    (next : p.B position → FreeM p (Option β)) :
    NoCutoff (FreeM.liftBind position next) ↔
      ∀ direction, NoCutoff (next direction) :=
  Iff.rfl

private theorem noCutoff_unroll_iff (M : DynComputation.{u} p α β)
    (k : ℕ) (state : M.State) :
    NoCutoff (M.unroll k state) ↔ M.ResolvesIn k state := by
  induction k generalizing state with
  | zero =>
      cases hview : M.view state with
      | inl value =>
          rw [M.unroll_return 0 state value hview, noCutoff_pure]
          simp [ResolvesIn, hview]
      | inr query =>
          rcases query with ⟨position, next⟩
          rw [M.unroll_query_zero state position next hview, noCutoff_pure]
          simp [ResolvesIn, hview]
  | succ k ih =>
      cases hview : M.view state with
      | inl value =>
          rw [M.unroll_return (k + 1) state value hview, noCutoff_pure]
          simp [ResolvesIn, hview]
      | inr query =>
          rcases query with ⟨position, next⟩
          rw [M.unroll_query_succ k state position next hview,
            noCutoff_liftBind,
            M.resolvesIn_query_succ_iff k state position next hview]
          exact forall_congr' fun direction => ih (next direction)

private theorem noCutoff_truncate_toResumption_iff
    (program : FreeM p β) (k : ℕ) :
    NoCutoff (Resumption.truncate k (FreeM.toResumption program)) ↔
      program.IsTotalRollBound k := by
  induction program using FreeM.induction generalizing k with
  | pure value =>
      rw [FreeM.toResumption_pure, Resumption.truncate_pure, noCutoff_pure]
      simp
  | lift_bind position next ih =>
      rw [← FreeM.liftBind_eq]
      cases k with
      | zero =>
          rw [Resumption.truncate_zero, FreeM.dest_toResumption_liftBind,
            FreeM.liftBind_eq, FreeM.isTotalRollBound_lift_bind_iff]
          rw [noCutoff_pure]
          simp
      | succ k =>
          rw [Resumption.truncate_succ, FreeM.dest_toResumption_liftBind,
            FreeM.liftBind_eq, FreeM.isTotalRollBound_lift_bind_iff]
          simp only [noCutoff_liftBind, Nat.zero_lt_succ,
            Nat.add_sub_cancel, true_and]
          exact forall_congr' fun direction => ih direction k

/-- Under supplied well-founded-program semantics, branchwise resolution is
equivalent to the program's total roll bound. The leaf argument selects no
witnesses, though the semantic resumption bridge retains its inherited M-type
axiom footprint. -/
theorem resolvesIn_iff_isTotalRollBound_of_behavior_eq
    (M : DynComputation.{u} p α β) (k : ℕ) (state : M.State)
    (program : FreeM p β)
    (hsem : M.toDynSystem.behavior state = FreeM.toResumption program) :
    M.ResolvesIn k state ↔ program.IsTotalRollBound k := by
  rw [← M.noCutoff_unroll_iff k state, M.unroll_eq_truncate, hsem]
  exact noCutoff_truncate_toResumption_iff program k

/-- Once execution has resolved, additional fuel leaves the exact unrolling
unchanged. This is constructive and does not choose a global value tree. -/
theorem unroll_eq_of_resolvesIn {M : DynComputation.{u} p α β}
    {j k : ℕ} {state : M.State} (h : M.ResolvesIn j state) (hjk : j ≤ k) :
    M.unroll k state = M.unroll j state := by
  induction j generalizing k state with
  | zero =>
      obtain ⟨value, hview⟩ := (M.resolvesIn_zero state).mp h
      rw [M.unroll_return k state value hview,
        M.unroll_return 0 state value hview]
  | succ j ih =>
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      cases hview : M.view state with
      | inl value =>
          rw [M.unroll_return (k + 1) state value hview,
            M.unroll_return (j + 1) state value hview]
      | inr query =>
          rcases query with ⟨position, next⟩
          rw [M.unroll_query_succ k state position next hview,
            M.unroll_query_succ j state position next hview]
          apply congrArg (FreeM.liftBind position)
          funext direction
          apply ih ((M.resolvesIn_query_succ_iff j state position next hview).mp h direction)
          omega

/-! ## Bounded sequential composition -/

/-- After handoff, bounded execution of the composite is exactly bounded
execution of the second computation. -/
theorem unroll_seqComp_inr {γ : Type uγ}
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (k : ℕ) (state₂ : M₂.State) :
    (M₁.seqComp M₂).unroll k (Sum.inr state₂) = M₂.unroll k state₂ := by
  induction k generalizing state₂ with
  | zero =>
      cases hview : M₂.view state₂ with
      | inl result =>
          have hcomposite : (M₁.seqComp M₂).view (Sum.inr state₂) =
              Sum.inl result := by
            rw [seqComp_view_inr]
            simp only [seqComp_State]
            rw [hview]
            rfl
          rw [(M₁.seqComp M₂).unroll_return 0 _ result hcomposite,
            M₂.unroll_return 0 state₂ result hview]
      | inr query =>
          rcases query with ⟨position, next⟩
          have hcomposite : (M₁.seqComp M₂).view (Sum.inr state₂) =
              Sum.inr ⟨position, fun direction => Sum.inr (next direction)⟩ := by
            rw [seqComp_view_inr]
            simp only [seqComp_State]
            rw [hview]
            rfl
          rw [(M₁.seqComp M₂).unroll_query_zero _ position _ hcomposite,
            M₂.unroll_query_zero state₂ position next hview]
  | succ k ih =>
      cases hview : M₂.view state₂ with
      | inl result =>
          have hcomposite : (M₁.seqComp M₂).view (Sum.inr state₂) =
              Sum.inl result := by
            rw [seqComp_view_inr]
            simp only [seqComp_State]
            rw [hview]
            rfl
          rw [(M₁.seqComp M₂).unroll_return (k + 1) _ result hcomposite,
            M₂.unroll_return (k + 1) state₂ result hview]
      | inr query =>
          rcases query with ⟨position, next⟩
          have hcomposite : (M₁.seqComp M₂).view (Sum.inr state₂) =
              Sum.inr ⟨position, fun direction => Sum.inr (next direction)⟩ := by
            rw [seqComp_view_inr]
            simp only [seqComp_State]
            rw [hview]
            rfl
          rw [(M₁.seqComp M₂).unroll_query_succ k _ position _ hcomposite,
            M₂.unroll_query_succ k state₂ position next hview]
          apply congrArg (FreeM.liftBind position)
          funext direction
          exact ih (next direction)

/-- If the first phase returns at its current state, the composite immediately
executes the second phase with the same fuel; no query or silent step is added. -/
theorem unroll_seqComp_inl_of_return {γ : Type uγ}
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (k : ℕ) (state₁ : M₁.State) (value : β)
    (hview : M₁.view state₁ = Sum.inl value) :
    (M₁.seqComp M₂).unroll k (Sum.inl state₁) =
      M₂.unroll k (M₂.init value) := by
  cases hview₂ : M₂.view (M₂.init value) with
  | inl result =>
      have hcomposite : (M₁.seqComp M₂).view (Sum.inl state₁) =
          Sum.inl result := by
        rw [seqComp_view_inl, hview]
        simp only [seqComp_State]
        rw [hview₂]
        rfl
      rw [(M₁.seqComp M₂).unroll_return k _ result hcomposite,
        M₂.unroll_return k _ result hview₂]
  | inr query =>
      rcases query with ⟨position, next⟩
      have hcomposite : (M₁.seqComp M₂).view (Sum.inl state₁) =
          Sum.inr ⟨position, fun direction => Sum.inr (next direction)⟩ := by
        rw [seqComp_view_inl, hview]
        simp only [seqComp_State]
        rw [hview₂]
        rfl
      cases k with
      | zero =>
          rw [(M₁.seqComp M₂).unroll_query_zero _ position _ hcomposite,
            M₂.unroll_query_zero _ position next hview₂]
      | succ k =>
          rw [(M₁.seqComp M₂).unroll_query_succ k _ position _ hcomposite,
            M₂.unroll_query_succ k _ position next hview₂]
          apply congrArg (FreeM.liftBind position)
          funext direction
          exact unroll_seqComp_inr M₁ M₂ k (next direction)

/-- A visible first-phase query consumes one composite fuel unit and keeps the
continuation in the first phase. -/
theorem unroll_seqComp_inl_of_query {γ : Type uγ}
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (k : ℕ) (state₁ : M₁.State) (position : p.A)
    (next : p.B position → M₁.State)
    (hview : M₁.view state₁ = Sum.inr ⟨position, next⟩) :
    (M₁.seqComp M₂).unroll (k + 1) (Sum.inl state₁) =
      FreeM.liftBind position fun direction =>
        (M₁.seqComp M₂).unroll k (Sum.inl (next direction)) := by
  have hcomposite : (M₁.seqComp M₂).view (Sum.inl state₁) =
      Sum.inr ⟨position, fun direction => Sum.inl (next direction)⟩ := by
    rw [seqComp_view_inl, hview]
    rfl
  exact (M₁.seqComp M₂).unroll_query_succ k _ position _ hcomposite

/-- Resolution in a handed-off state is exactly resolution in the second
computation. -/
theorem resolvesIn_seqComp_inr_iff {γ : Type uγ}
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (k : ℕ) (state₂ : M₂.State) :
    (M₁.seqComp M₂).ResolvesIn k (Sum.inr state₂) ↔
      M₂.ResolvesIn k state₂ := by
  rw [← (M₁.seqComp M₂).noCutoff_unroll_iff,
    ← M₂.noCutoff_unroll_iff, unroll_seqComp_inr]

/-- An immediate first-phase return preserves the second phase's exact
resolution predicate at the same fuel. -/
theorem resolvesIn_seqComp_inl_of_return_iff {γ : Type uγ}
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (k : ℕ) (state₁ : M₁.State) (value : β)
    (hview : M₁.view state₁ = Sum.inl value) :
    (M₁.seqComp M₂).ResolvesIn k (Sum.inl state₁) ↔
      M₂.ResolvesIn k (M₂.init value) := by
  rw [← (M₁.seqComp M₂).noCutoff_unroll_iff,
    ← M₂.noCutoff_unroll_iff,
    unroll_seqComp_inl_of_return M₁ M₂ k state₁ value hview]

/-- Second-phase resolution remains valid after the composite has handed off. -/
theorem ResolvesIn.seqComp_inr {γ : Type uγ}
    {M₁ : DynComputation.{u} p α β} {M₂ : DynComputation.{v} p β γ}
    {k : ℕ} {state₂ : M₂.State} (h : M₂.ResolvesIn k state₂) :
    (M₁.seqComp M₂).ResolvesIn k (Sum.inr state₂) :=
  (resolvesIn_seqComp_inr_iff M₁ M₂ k state₂).mpr h

/-- Resolution budgets compose additively from a first-phase state. The proof
handles an immediate first-phase return as a same-observation handoff. -/
theorem ResolvesIn.seqComp_inl {γ : Type uγ}
    {M₁ : DynComputation.{u} p α β} {M₂ : DynComputation.{v} p β γ}
    {k₁ k₂ : ℕ} {state₁ : M₁.State} (h₁ : M₁.ResolvesIn k₁ state₁)
    (h₂ : ∀ value, M₂.ResolvesIn k₂ (M₂.init value)) :
    (M₁.seqComp M₂).ResolvesIn (k₁ + k₂) (Sum.inl state₁) := by
  induction k₁ generalizing state₁ with
  | zero =>
      obtain ⟨value, hview⟩ := (M₁.resolvesIn_zero state₁).mp h₁
      simpa using
        (resolvesIn_seqComp_inl_of_return_iff M₁ M₂ k₂ state₁ value hview).mpr
          (h₂ value)
  | succ k₁ ih =>
      cases hview : M₁.view state₁ with
      | inl value =>
          apply (resolvesIn_seqComp_inl_of_return_iff M₁ M₂
            ((k₁ + 1) + k₂) state₁ value hview).mpr
          exact (h₂ value).mono (by omega)
      | inr query =>
          rcases query with ⟨position, next⟩
          have hnext :=
            (M₁.resolvesIn_query_succ_iff k₁ state₁ position next hview).mp h₁
          have hcomposite : (M₁.seqComp M₂).view (Sum.inl state₁) =
              Sum.inr ⟨position, fun direction => Sum.inl (next direction)⟩ := by
            rw [seqComp_view_inl, hview]
            rfl
          rw [show (k₁ + 1) + k₂ = (k₁ + k₂) + 1 by omega,
            (M₁.seqComp M₂).resolvesIn_query_succ_iff
              (k₁ + k₂) _ position _ hcomposite]
          exact fun direction => ih (hnext direction)

/-- Initial-state resolution budgets compose additively. -/
theorem ResolvesIn.seqComp_init {γ : Type uγ}
    {M₁ : DynComputation.{u} p α β} {M₂ : DynComputation.{v} p β γ}
    {k₁ k₂ : ℕ} {input : α} (h₁ : M₁.ResolvesIn k₁ (M₁.init input))
    (h₂ : ∀ value, M₂.ResolvesIn k₂ (M₂.init value)) :
    (M₁.seqComp M₂).ResolvesIn (k₁ + k₂)
      ((M₁.seqComp M₂).init input) := by
  change (M₁.seqComp M₂).ResolvesIn (k₁ + k₂) (Sum.inl (M₁.init input))
  exact h₁.seqComp_inl h₂

/-- Exact additive syntactic execution law under phase-resolution
certificates. The `none` branch is retained in the syntax but is unreachable
under `h₁`. -/
theorem unroll_seqComp_inl_of_resolvesIn {γ : Type uγ}
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (k₂ : ℕ) {k₁ : ℕ} {state₁ : M₁.State}
    (h₁ : M₁.ResolvesIn k₁ state₁)
    (h₂ : ∀ value, M₂.ResolvesIn k₂ (M₂.init value)) :
    (M₁.seqComp M₂).unroll (k₁ + k₂) (Sum.inl state₁) =
      FreeM.bind (M₁.unroll k₁ state₁) fun result => match result with
        | none => FreeM.pure none
        | some value => M₂.unroll k₂ (M₂.init value) := by
  induction k₁ generalizing state₁ with
  | zero =>
      obtain ⟨value, hview⟩ := (M₁.resolvesIn_zero state₁).mp h₁
      simp only [Nat.zero_add]
      rw [unroll_seqComp_inl_of_return M₁ M₂ k₂ state₁ value hview,
        M₁.unroll_return 0 state₁ value hview]
      rfl
  | succ k₁ ih =>
      cases hview : M₁.view state₁ with
      | inl value =>
          rw [unroll_seqComp_inl_of_return M₁ M₂ ((k₁ + 1) + k₂)
              state₁ value hview,
            M₁.unroll_return (k₁ + 1) state₁ value hview]
          change M₂.unroll ((k₁ + 1) + k₂) (M₂.init value) =
            M₂.unroll k₂ (M₂.init value)
          exact M₂.unroll_eq_of_resolvesIn (h₂ value) (by omega)
      | inr query =>
          rcases query with ⟨position, next⟩
          have hnext :=
            (M₁.resolvesIn_query_succ_iff k₁ state₁ position next hview).mp h₁
          rw [show (k₁ + 1) + k₂ = (k₁ + k₂) + 1 by omega,
            unroll_seqComp_inl_of_query M₁ M₂ (k₁ + k₂) state₁ position next hview,
            M₁.unroll_query_succ k₁ state₁ position next hview]
          change FreeM.liftBind position _ = FreeM.liftBind position _
          apply congrArg (FreeM.liftBind position)
          funext direction
          exact ih (hnext direction)

/-- Input-level specialization of additive bounded sequential execution. -/
theorem run_seqComp {γ : Type uγ}
    (M₁ : DynComputation.{u} p α β) (M₂ : DynComputation.{v} p β γ)
    (k₁ k₂ : ℕ) (input : α) (h₁ : M₁.ResolvesIn k₁ (M₁.init input))
    (h₂ : ∀ value, M₂.ResolvesIn k₂ (M₂.init value)) :
    (M₁.seqComp M₂).run (k₁ + k₂) input =
      FreeM.bind (M₁.run k₁ input) fun result => match result with
        | none => FreeM.pure none
        | some value => M₂.run k₂ value :=
  unroll_seqComp_inl_of_resolvesIn M₁ M₂ k₂ h₁ h₂

/-! ## Bounded implementation -/

/-- A computation implements `program` within the uniform query budget `k`. -/
def ImplementsWithin (M : DynComputation.{u} p α β)
    (program : α → FreeM p β) (k : ℕ) : Prop :=
  ∀ input, M.run k input = FreeM.map some (program input)

/-- Exact semantic-and-resource characterization of bounded implementation. -/
theorem implementsWithin_iff_implements_and_bound
    (M : DynComputation.{u} p α β) (program : α → FreeM p β) (k : ℕ) :
    M.ImplementsWithin program k ↔
      M.Implements program ∧ ∀ input, (program input).IsTotalRollBound k := by
  constructor
  · intro h
    constructor
    · intro input
      exact ((Resumption.truncate_eq_map_some_iff k
        (M.denote input) (program input)).mp (by
          rw [← M.run_eq_truncate k input]
          exact h input)).1
    · intro input
      exact ((Resumption.truncate_eq_map_some_iff k
        (M.denote input) (program input)).mp (by
          rw [← M.run_eq_truncate k input]
          exact h input)).2
  · rintro ⟨himplements, hbound⟩ input
    rw [M.run_eq_truncate, himplements input]
    exact Resumption.truncate_toResumption_eq_map_some (hbound input)

/-- Bounded implementation is equivalently qualitative implementation plus
branchwise resolution of every initial state. No branch witnesses are selected;
the qualitative semantic equality retains the inherited resumption footprint. -/
theorem implementsWithin_iff_implements_and_resolvesIn
    (M : DynComputation.{u} p α β) (program : α → FreeM p β) (k : ℕ) :
    M.ImplementsWithin program k ↔
      M.Implements program ∧ ∀ input, M.ResolvesIn k (M.init input) := by
  rw [implementsWithin_iff_implements_and_bound]
  apply and_congr_right
  intro himplements
  exact forall_congr' fun input =>
    (M.resolvesIn_iff_isTotalRollBound_of_behavior_eq k (M.init input)
      (program input) (himplements input)).symm

/-- Every bounded implementation supplies its operational resolution
certificate. -/
theorem ImplementsWithin.resolvesIn {M : DynComputation.{u} p α β}
    {program : α → FreeM p β} {k : ℕ} (h : M.ImplementsWithin program k)
    (input : α) : M.ResolvesIn k (M.init input) :=
  ((implementsWithin_iff_implements_and_resolvesIn M program k).mp h).2 input

/-- A bounded implementation remains valid at any larger uniform budget. -/
theorem ImplementsWithin.mono {M : DynComputation.{u} p α β}
    {program : α → FreeM p β} {j k : ℕ} (h : M.ImplementsWithin program j)
    (hjk : j ≤ k) : M.ImplementsWithin program k := by
  rw [implementsWithin_iff_implements_and_bound] at h ⊢
  exact ⟨h.1, fun input => (h.2 input).mono hjk⟩

/-- A synchronized simulation plus a uniform source-program bound proves
bounded implementation. -/
theorem implementsWithin_of_isSimulation (M : DynComputation.{u} p α β)
    (program : α → FreeM p β) (R : M.State → FreeM p β → Prop)
    (simulation : IsSimulation M.toDynSystem (ofFreeM program).toDynSystem R)
    (init_rel : ∀ input, R (M.init input) (program input)) (k : ℕ)
    (hbound : ∀ input, (program input).IsTotalRollBound k) :
    M.ImplementsWithin program k := by
  rw [implementsWithin_iff_implements_and_bound]
  exact ⟨implements_of_isSimulation M program R simulation init_rel, hbound⟩

/-- Bounded implementations compose sequentially with additive budgets. -/
theorem ImplementsWithin.seqComp {γ : Type uγ}
    {M₁ : DynComputation.{u} p α β} {M₂ : DynComputation.{v} p β γ}
    {program₁ : α → FreeM p β} {program₂ : β → FreeM p γ}
    {k₁ k₂ : ℕ} (h₁ : M₁.ImplementsWithin program₁ k₁)
    (h₂ : M₂.ImplementsWithin program₂ k₂) :
    (M₁.seqComp M₂).ImplementsWithin
      (fun input => FreeM.bind (program₁ input) program₂) (k₁ + k₂) := by
  rw [implementsWithin_iff_implements_and_bound] at h₁ h₂ ⊢
  exact ⟨h₁.1.seqComp h₂.1,
    fun input => FreeM.isTotalRollBound_bind (ob := program₂)
      (h₁.2 input) (fun value => h₂.2 value)⟩

/-! ## Monad-parametric bounded runs -/

/-!
`FreeM.liftM` interprets directions and return values in one homogeneous monad
universe. Accordingly this section aligns the interface direction, result, and
handler-value universes; the computation's state and input universes remain
independent. The preceding syntactic and logical API has no such alignment.
-/

section RunWith

variable {q : PFunctor.{uA, uβ}} {m : Type uβ → Type v} [Monad m]

/-- Interpret a bounded syntactic execution through a monadic handler. -/
def runWith (M : DynComputation.{u} q α β) (handler : Handler m q)
    (k : ℕ) (state : M.State) : m (Option β) :=
  FreeM.liftM handler (M.unroll k state)

/-- Interpret a bounded execution from the input-selected initial state. -/
def runWithInput (M : DynComputation.{u} q α β) (handler : Handler m q)
    (k : ℕ) (input : α) : m (Option β) :=
  M.runWith handler k (M.init input)

@[simp] theorem runWith_lift (M : DynComputation.{u} q α β)
    (k : ℕ) (state : M.State) :
    M.runWith (m := FreeM q) FreeM.lift k state = M.unroll k state :=
  FreeM.liftM_lift_eq_self (M.unroll k state)

@[simp] theorem runWithInput_lift (M : DynComputation.{u} q α β)
    (k : ℕ) (input : α) :
    M.runWithInput (m := FreeM q) FreeM.lift k input = M.run k input :=
  M.runWith_lift k (M.init input)

theorem runWith_return (M : DynComputation.{u} q α β)
    (handler : Handler m q) (k : ℕ) (state : M.State) (value : β)
    (hview : M.view state = Sum.inl value) :
    M.runWith handler k state = pure (some value) := by
  unfold runWith
  rw [unroll_return M k state value hview]
  rfl

theorem runWith_query_zero (M : DynComputation.{u} q α β)
    (handler : Handler m q) (state : M.State) (position : q.A)
    (next : q.B position → M.State)
    (hview : M.view state = Sum.inr ⟨position, next⟩) :
    M.runWith handler 0 state = pure none := by
  unfold runWith
  rw [unroll_query_zero M state position next hview]
  rfl

theorem runWith_query_succ (M : DynComputation.{u} q α β)
    (handler : Handler m q) (k : ℕ) (state : M.State)
    (position : q.A) (next : q.B position → M.State)
    (hview : M.view state = Sum.inr ⟨position, next⟩) :
    M.runWith handler (k + 1) state =
      handler position >>= fun direction => M.runWith handler k (next direction) := by
  unfold runWith
  rw [unroll_query_succ M k state position next hview]
  rfl

/-- Once every branch has returned, interpreting with additional fuel gives
the same monadic computation. No monad laws are needed: the syntax is equal
before interpretation. -/
theorem runWith_eq_of_resolvesIn (M : DynComputation.{u} q α β)
    (handler : Handler m q) {j k : ℕ} {state : M.State}
    (h : M.ResolvesIn j state) (hjk : j ≤ k) :
    M.runWith handler k state = M.runWith handler j state := by
  unfold runWith
  rw [M.unroll_eq_of_resolvesIn h hjk]

/-- Reading a bounded implementation through any lawful handler is exactly
the handler interpretation of its well-founded source program, with successful
results wrapped in `some`. -/
theorem ImplementsWithin.runWithInput_eq [LawfulMonad m]
    {M : DynComputation.{u} q α β} {program : α → FreeM q β} {k : ℕ}
    (h : M.ImplementsWithin program k) (handler : Handler m q) (input : α) :
    M.runWithInput handler k input =
      some <$> FreeM.liftM handler (program input) := by
  unfold runWithInput runWith
  have hrun := h input
  change M.unroll k (M.init input) = FreeM.map some (program input) at hrun
  rw [hrun]
  change FreeM.liftM handler (some <$> program input) = _
  rw [FreeM.liftM_map]

/-- The free handler exposes bounded implementation without information loss. -/
theorem implementsWithin_iff_runWithInput_lift
    (M : DynComputation.{u} q α β) (program : α → FreeM q β) (k : ℕ) :
    M.ImplementsWithin program k ↔
      ∀ input, M.runWithInput (m := FreeM q) FreeM.lift k input =
        FreeM.map some (program input) := by
  simp only [ImplementsWithin, runWithInput_lift]

/-- Monad-parametric execution agrees exactly with the second computation
after handoff. -/
theorem runWith_seqComp_inr {δ : Type uβ}
    (M₁ : DynComputation.{u} q α β) (M₂ : DynComputation.{v} q β δ)
    (handler : Handler m q) (k : ℕ) (state₂ : M₂.State) :
    (M₁.seqComp M₂).runWith handler k (Sum.inr state₂) =
      M₂.runWith handler k state₂ := by
  unfold runWith
  rw [unroll_seqComp_inr]

/-- Handler interpretation preserves the exact additive sequential-execution
law under phase-resolution certificates. -/
theorem runWithInput_seqComp [LawfulMonad m] {δ : Type uβ}
    (M₁ : DynComputation.{u} q α β) (M₂ : DynComputation.{v} q β δ)
    (handler : Handler m q) (k₁ k₂ : ℕ) (input : α)
    (h₁ : M₁.ResolvesIn k₁ (M₁.init input))
    (h₂ : ∀ value, M₂.ResolvesIn k₂ (M₂.init value)) :
    (M₁.seqComp M₂).runWithInput handler (k₁ + k₂) input =
      M₁.runWithInput handler k₁ input >>= fun result => match result with
        | none => pure none
        | some value => M₂.runWithInput handler k₂ value := by
  change FreeM.liftM handler ((M₁.seqComp M₂).run (k₁ + k₂) input) =
    FreeM.liftM handler (M₁.run k₁ input) >>= fun result => match result with
      | none => pure none
      | some value => FreeM.liftM handler (M₂.run k₂ value)
  rw [run_seqComp M₁ M₂ k₁ k₂ input h₁ h₂]
  change FreeM.liftM handler
      (M₁.run k₁ input >>= fun result => match result with
        | none => FreeM.pure none
        | some value => M₂.run k₂ value) = _
  rw [FreeM.liftM_bind]
  apply bind_congr
  intro result
  cases result <;> rfl

/-- State-transformer form of the query branch. It executes exactly the query
exposed by `view`; terminal states deliberately have no corresponding `p` step. -/
theorem runWith_query_succ_stateT
    {σ : Type uβ} (M : DynComputation.{u} q α β)
    (handler : Handler (StateT σ m) q) (k : ℕ) (state : M.State)
    (position : q.A) (next : q.B position → M.State)
    (hview : M.view state = Sum.inr ⟨position, next⟩) (handlerState : σ) :
    (M.runWith handler (k + 1) state).run handlerState =
      handler position handlerState >>= fun result =>
        (M.runWith handler k (next result.1)).run result.2 := by
  rw [M.runWith_query_succ handler k state position next hview]
  rfl

end RunWith

end DynSystem.DynComputation

end PFunctor
