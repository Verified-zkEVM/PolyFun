/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Bound
public import PolyFun.PFunctor.Free.Support

/-!
# Executing dependent handler substitution in explicit phases

One uniform dependent handler implements every position of an outer polynomial interface.
The dispatcher suspends the caller while that handler runs, then resumes the caller with its
typed answer. Entry and return are explicit administrative transitions; inner queries remain
visible. Finite execution retains unfinished phases and counts both kinds of transitions.

This is an operational semantics for substitution of finite polynomial programs. Its counters
measure dispatcher transitions and visible queries. Backend code for host-language operations,
encoded state sizes, and their machine costs are additional quantitative-realization obligations.
-/

public section

universe u

namespace PFunctor.FreeM.HandlerMachine

open MonadAttach

-- Constructor equations and monadic sequencing share the same polynomial bind operation.
attribute [local implicit_reducible] FreeM.bind

variable {P Q : PFunctor.{u, u}} {α : Type u}

/-- A caller or one active handler with the caller's suspended dependent continuation. -/
inductive Phase (P Q : PFunctor.{u, u}) (α : Type u) where
  | caller (program : FreeM P α)
  | handler (position : P.A) (program : FreeM Q (P.B position))
      (next : P.B position → FreeM P α)

/-- A finite execution's actual residual phase and its two transition counters. -/
structure Prefix (P Q : PFunctor.{u, u}) (α : Type u) where
  /-- Caller or handler code remaining after execution. -/
  phase : Phase P Q α
  /-- Executed handler-entry and handler-return transitions. -/
  administrative : ℕ
  /-- Executed queries against the inner polynomial interface. -/
  queries : ℕ

/-- Charge one administrative transition without changing the visible-query count. -/
@[expose] def Prefix.admin (out : Prefix P Q α) : Prefix P Q α :=
  { out with administrative := out.administrative + 1 }

/-- Charge one actual inner query without changing the administrative count. -/
@[expose] def Prefix.query (out : Prefix P Q α) : Prefix P Q α :=
  { out with queries := out.queries + 1 }

/-- Interpret a residual phase by ordinary dependent handler substitution. -/
@[expose] def denote (impl : (a : P.A) → FreeM Q (P.B a)) : Phase P Q α → FreeM Q α
  | .caller program => program.liftM impl
  | .handler _ program next => program >>= fun answer => (next answer).liftM impl

/-- Execute at most the supplied number of transitions, counting both dispatch and queries. -/
@[expose] def runPrefix (impl : (a : P.A) → FreeM Q (P.B a)) :
    ℕ → Phase P Q α → FreeM Q (Prefix P Q α)
  | 0, phase => pure ⟨phase, 0, 0⟩
  | _ + 1, .caller (.pure value) => pure ⟨.caller (.pure value), 0, 0⟩
  | fuel + 1, .caller (.liftBind a next) =>
      Prefix.admin <$> runPrefix impl fuel (.handler a (impl a) next)
  | fuel + 1, .handler _ (.pure answer) next =>
      Prefix.admin <$> runPrefix impl fuel (.caller (next answer))
  | fuel + 1, .handler a (.liftBind b rest) next =>
      FreeM.liftBind b fun answer =>
        Prefix.query <$> runPrefix impl fuel (.handler a (rest answer) next)

/-- Only a returned caller provides a final result; a handler return still needs dispatch. -/
@[expose] def result : Phase P Q α → Option α
  | .caller (.pure value) => some value
  | _ => none

/-- Pausing and then interpreting the retained phase preserves the complete program semantics,
including adaptive query order and the handler's dependent answer type. -/
theorem runPrefix_resume (impl : (a : P.A) → FreeM Q (P.B a))
    (fuel : ℕ) (phase : Phase P Q α) :
    (runPrefix impl fuel phase >>= fun out => denote impl out.phase) = denote impl phase := by
  induction fuel generalizing phase with
  | zero => simp [runPrefix]
  | succ fuel ih =>
      cases phase with
      | caller program =>
          cases program with
          | pure value => simp [runPrefix, denote]
          | liftBind a next =>
              simpa [runPrefix, Prefix.admin, bind_map_left, denote] using
                ih (.handler a (impl a) next)
      | handler a program next =>
          cases program with
          | pure answer =>
              simpa [runPrefix, Prefix.admin, bind_map_left, denote] using
                ih (.caller (next answer))
          | liftBind b rest =>
              simp only [runPrefix, denote]
              apply congrArg (FreeM.liftBind b)
              funext answer
              change (Prefix.query <$> runPrefix impl fuel (.handler a (rest answer) next) >>=
                fun out => denote impl out.phase) = denote impl (.handler a (rest answer) next)
              rw [bind_map_left]
              exact ih (.handler a (rest answer) next)

/-- Every prefix charges at most its allocated transitions. Administrative work is included. -/
theorem runPrefix_transitions (impl : (a : P.A) → FreeM Q (P.B a))
    (fuel : ℕ) (phase : Phase P Q α) :
    AllOutputs (fun out => out.administrative + out.queries ≤ fuel)
      (runPrefix impl fuel phase) := by
  induction fuel generalizing phase with
  | zero => simp [runPrefix, allOutputs_pure]
  | succ fuel ih =>
      cases phase with
      | caller program =>
          cases program with
          | pure value => simp [runPrefix, allOutputs_pure]
          | liftBind a next =>
              rw [runPrefix, allOutputs_map]
              intro out hout
              have h := ih (.handler a (impl a) next) out hout
              change out.administrative + 1 + out.queries ≤ fuel + 1
              omega
      | handler a program next =>
          cases program with
          | pure answer =>
              rw [runPrefix, allOutputs_map]
              intro out hout
              have h := ih (.caller (next answer)) out hout
              change out.administrative + 1 + out.queries ≤ fuel + 1
              omega
          | liftBind b rest =>
              rw [runPrefix, allOutputs_liftBind]
              intro answer
              rw [allOutputs_map]
              intro out hout
              have h := ih (.handler a (rest answer) next) out hout
              change out.administrative + (out.queries + 1) ≤ fuel + 1
              omega

/-- A compositional upper bound on remaining transitions. A suspended caller has at most `n`
further calls after its current handler returns, and that handler has at most `k` inner queries. -/
@[expose] def Budget (handlerLimit : ℕ) : Phase P Q α → ℕ → Prop
  | .caller program, fuel =>
      ∃ n, program.IsTotalRollBound n ∧ n * (handlerLimit + 2) ≤ fuel
  | .handler _ program next, fuel =>
      ∃ n k, program.IsTotalRollBound k ∧ (∀ answer, (next answer).IsTotalRollBound n) ∧
        n * (handlerLimit + 2) + k + 1 ≤ fuel

/-- The dispatcher completes whenever its fuel covers the compositional remaining budget. -/
theorem runPrefix_complete_of_budget (impl : (a : P.A) → FreeM Q (P.B a))
    (handlerLimit : ℕ) (himpl : ∀ a, (impl a).IsTotalRollBound handlerLimit)
    (fuel : ℕ) (phase : Phase P Q α) (hbudget : Budget handlerLimit phase fuel) :
    AllOutputs (fun out => ∃ value, out.phase = Phase.caller (FreeM.pure value))
      (runPrefix impl fuel phase) := by
  induction fuel generalizing phase with
  | zero =>
      cases phase with
      | caller program =>
          obtain ⟨n, hprogram, hsize⟩ := hbudget
          cases program with
          | pure value => simp [runPrefix, allOutputs_pure]
          | liftBind a next =>
              have hpos := Nat.mul_pos hprogram.1 (show 0 < handlerLimit + 2 by omega)
              omega
      | handler a program next =>
          obtain ⟨n, k, _, _, hsize⟩ := hbudget
          omega
  | succ fuel ih =>
      cases phase with
      | caller program =>
          obtain ⟨n, hprogram, hsize⟩ := hbudget
          cases program with
          | pure value => simp [runPrefix, allOutputs_pure]
          | liftBind a next =>
              rw [isTotalRollBound_liftBind_iff] at hprogram
              obtain ⟨hpos, hnext⟩ := hprogram
              cases n with
              | zero => omega
              | succ n =>
                  rw [runPrefix, allOutputs_map]
                  apply ih (.handler a (impl a) next)
                  refine ⟨n, handlerLimit, himpl a, ?_, ?_⟩
                  · simpa using hnext
                  · simp only [Nat.succ_mul] at hsize
                    omega
      | handler a program next =>
          obtain ⟨n, k, hprogram, hnext, hsize⟩ := hbudget
          cases program with
          | pure answer =>
              rw [runPrefix, allOutputs_map]
              exact ih (.caller (next answer)) ⟨n, hnext answer, by omega⟩
          | liftBind b rest =>
              rw [isTotalRollBound_liftBind_iff] at hprogram
              obtain ⟨hpos, hrest⟩ := hprogram
              cases k with
              | zero => omega
              | succ k =>
                  rw [runPrefix, allOutputs_liftBind]
                  intro answer
                  rw [allOutputs_map]
                  exact ih (.handler a (rest answer) next)
                    ⟨n, k, by simpa using hrest answer, hnext, by omega⟩

/-- If the caller makes at most `calls` outer queries and every handler makes at most `inner`
inner queries, `calls * (inner + 2)` transitions suffice, including entry and return dispatch. -/
theorem runPrefix_complete (impl : (a : P.A) → FreeM Q (P.B a))
    (program : FreeM P α) (calls inner : ℕ)
    (hprogram : program.IsTotalRollBound calls) (himpl : ∀ a, (impl a).IsTotalRollBound inner) :
    AllOutputs (fun out => ∃ value, out.phase = Phase.caller (FreeM.pure value))
      (runPrefix impl (calls * (inner + 2)) (.caller program)) :=
  runPrefix_complete_of_budget impl inner himpl _ _ ⟨calls, hprogram, le_rfl⟩

/-- Erasing the phase and counters of a completed execution gives ordinary handler substitution.
This equality preserves the complete ordered inner interaction, not just the returned value. -/
theorem map_result_runPrefix (impl : (a : P.A) → FreeM Q (P.B a))
    (program : FreeM P α) (calls inner : ℕ)
    (hprogram : program.IsTotalRollBound calls) (himpl : ∀ a, (impl a).IsTotalRollBound inner) :
    (fun out => result out.phase) <$>
        runPrefix impl (calls * (inner + 2)) (.caller program) =
      some <$> program.liftM impl := by
  let execution := runPrefix impl (calls * (inner + 2)) (.caller program)
  have hcomplete := runPrefix_complete impl program calls inner hprogram himpl
  calc
    (fun out => result out.phase) <$> execution =
        execution >>= (fun out => some <$> denote impl out.phase) := by
      rw [← LawfulMonad.bind_pure_comp]
      rw [← WeaklyLawfulMonadAttach.attach_bind_val (x := execution),
        ← WeaklyLawfulMonadAttach.attach_bind_val (x := execution)]
      apply bind_congr
      intro out
      obtain ⟨value, hvalue⟩ := hcomplete out.val out.property
      rw [hvalue]
      rfl
    _ = some <$> program.liftM impl := by
      rw [← _root_.map_bind, runPrefix_resume]
      rfl

end PFunctor.FreeM.HandlerMachine
