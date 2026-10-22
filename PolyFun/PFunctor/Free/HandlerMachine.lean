/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Bound
public import PolyFun.PFunctor.Free.Support
public import PolyFun.PFunctor.Handler.Machine.Defs
public import PolyFun.PFunctor.Handler.Instrumentation.Free
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Executing dependent handler substitution in explicit phases

One uniform dependent handler implements every position of an outer polynomial interface.
The dispatcher suspends the caller while that handler runs, then resumes the caller with its
typed answer. Entry and return are explicit administrative transitions; inner queries remain
visible. Finite execution retains unfinished phases and counts both kinds of transitions.

This is an operational semantics for substitution of finite polynomial programs. Its counters
measure dispatcher transitions and visible queries. Backend code for host-language operations,
encoded state sizes, and their machine costs are additional quantitative-realization obligations.
The runner folds a chunk of `MachineHandler.dispatch` through writer instrumentation. Its
constructor equations expose the finite phase API without another recursive interpreter.
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

/-- A stateless finite service retains its current free program as private machine state. -/
@[expose, reducible] def service (impl : (a : P.A) → FreeM Q (P.B a)) :
    MachineHandler P Q PUnit := fun a =>
  DynSystem.DynComputation.ofStep (fun program : FreeM Q (P.B a) => match program with
    | .pure answer => .inl (answer, PUnit.unit)
    | .liftBind q next => .inr ⟨q, next⟩) (fun _ => impl a)

/-- The residual-program caller used by the shared dispatcher. -/
@[expose, reducible] def caller : DynSystem.DynComputation P (FreeM P α) α :=
  .ofFreeM id

/-- Embed a finite residual phase in the common dispatcher state. -/
@[expose] def encodePhase (impl : (a : P.A) → FreeM Q (P.B a)) :
    Phase P Q α → MachineHandler.Phase (service impl) (caller (P := P) (α := α))
  | .caller program => .caller program PUnit.unit
  | .handler a program next => .handler a program
      (.ofView (DynSystem.DynComputation.view_ofFreeM_liftBind id a next))

/-- Observe the common dispatcher state through the finite-program phase API. -/
@[expose] def decodePhase (impl : (a : P.A) → FreeM Q (P.B a)) :
    MachineHandler.Phase (service impl) (caller (P := P) (α := α)) → Phase P Q α
  | .caller program _ => .caller program
  | .handler a program pending => .handler a program pending.resume

@[simp] theorem decodePhase_encodePhase (impl : (a : P.A) → FreeM Q (P.B a))
    (phase : Phase P Q α) : decodePhase impl (encodePhase impl phase) = phase := by
  cases phase with
  | caller program => rfl
  | handler a program next =>
    unfold encodePhase decodePhase
    congr 1

/-- Separate administrative and primitive-query counts, in the handler's universe. -/
abbrev Counts := ULift.{u} (Multiplicative (ℕ × ℕ))

/-- Interpret primitive queries directly and administrative transitions as a unary return. -/
@[expose] def primitiveHandler : Handler (FreeM Q) (Q + y.{u, u})
  | .inl q => FreeM.lift q
  | .inr _ => pure PUnit.unit

/-- Charge each explicit dispatcher operation in its own counter. -/
@[expose] def charge : (Q + y.{u, u}).A → Counts.{u}
  | .inl _ => ⟨Multiplicative.ofAdd (0, 1)⟩
  | .inr _ => ⟨Multiplicative.ofAdd (1, 0)⟩

/-- Observe a saved dispatcher chunk and its accumulated transition counts. -/
@[expose] def decodePrefix (impl : (a : P.A) → FreeM Q (P.B a))
    (out : DynSystem.DynComputation.Chunk
      (MachineHandler.Phase (service impl) (caller (P := P) (α := α))) (α × PUnit) × Counts) :
    Prefix P Q α :=
  ⟨match out.1 with
    | .done value => .caller (.pure value.1)
    | .paused phase => decodePhase impl phase,
    out.2.down.toAdd.1, out.2.down.toAdd.2⟩

/-- Execute the common dispatcher and record its operations through writer instrumentation. -/
@[expose] def runPrefix (impl : (a : P.A) → FreeM Q (P.B a))
    (fuel : ℕ) (phase : Phase P Q α) : FreeM Q (Prefix P Q α) :=
  decodePrefix impl <$> ((((service impl).dispatch caller).unrollChunk
    fuel (encodePhase impl phase)).liftM (primitiveHandler.withTraceBefore charge)).run

/-- Finite prefixes are observations of the same runner used for arbitrary machine services. -/
theorem runPrefix_eq_runChunk (impl : (a : P.A) → FreeM Q (P.B a))
    (fuel : ℕ) (phase : Phase P Q α) :
    runPrefix impl fuel phase =
      decodePrefix impl <$> (((service impl).dispatch caller).runChunk
        (primitiveHandler.withTraceBefore charge) fuel (encodePhase impl phase)).run := by
  rw [DynSystem.DynComputation.runChunk_eq_liftM]
  rfl

open DynSystem.DynComputation in
/-- The common dispatcher's view in finite residual-program coordinates. -/
theorem view_encodePhase (impl : (a : P.A) → FreeM Q (P.B a)) (phase : Phase P Q α) :
    ((service impl).dispatch caller).view (encodePhase impl phase) = match phase with
      | .caller (.pure value) => .inl (value, PUnit.unit)
      | .caller (.liftBind a next) => .inr ⟨.inr PUnit.unit,
          fun _ => encodePhase impl (.handler a (impl a) next)⟩
      | .handler _ (.pure answer) next => .inr ⟨.inr PUnit.unit,
          fun _ => encodePhase impl (.caller (next answer))⟩
      | .handler a (.liftBind q rest) next => .inr ⟨.inl q,
          fun answer => encodePhase impl (.handler a (rest answer) next)⟩ := by
  rw [MachineHandler.view_dispatch]
  cases phase with
  | caller program =>
    cases program with
    | pure value =>
      exact MachineHandler.dispatchStep_caller_pure (service impl) caller
        (view_ofFreeM_pure id value) PUnit.unit
    | liftBind a next =>
      exact MachineHandler.dispatchStep_caller_query (service impl) caller
        (view_ofFreeM_liftBind id a next) PUnit.unit
  | handler a program next =>
    cases program <;>
      simp only [MachineHandler.dispatchStep, encodePhase,
        service, view_ofStep]
    congr 3

open DynSystem.DynComputation in
@[simp] theorem runPrefix_zero (impl : (a : P.A) → FreeM Q (P.B a))
    (phase : Phase P Q α) : runPrefix impl 0 phase = pure ⟨phase, 0, 0⟩ := by
  rw [runPrefix, unrollChunk_zero, view_encodePhase]
  cases phase with
  | caller program => cases program <;> rfl
  | handler a program next =>
    cases program <;>
      change (pure ⟨decodePhase impl (encodePhase impl _), 0, 0⟩ : FreeM Q (Prefix P Q α)) = _
    all_goals rw [decodePhase_encodePhase]

open DynSystem.DynComputation in
@[freeM_unfold] theorem runPrefix_caller_pure (impl : (a : P.A) → FreeM Q (P.B a))
    (fuel : ℕ) (value : α) :
    runPrefix impl fuel (.caller (.pure value)) = pure ⟨.caller (.pure value), 0, 0⟩ := by
  cases fuel with
  | zero => exact runPrefix_zero _ _
  | succ fuel => rw [runPrefix, unrollChunk_succ, view_encodePhase]; rfl

private theorem decodePrefix_admin (impl : (a : P.A) → FreeM Q (P.B a))
    (out : DynSystem.DynComputation.Chunk
      (MachineHandler.Phase (service impl) (caller (P := P) (α := α))) (α × PUnit) × Counts) :
    decodePrefix impl (out.1, charge (Q := Q) (.inr PUnit.unit) * out.2) =
      (decodePrefix impl out).admin := by
  rcases out with ⟨chunk, counts⟩
  cases chunk <;> simp [decodePrefix, Prefix.admin, charge, Nat.add_comm]

private theorem decodePrefix_query (impl : (a : P.A) → FreeM Q (P.B a)) (q : Q.A)
    (out : DynSystem.DynComputation.Chunk
      (MachineHandler.Phase (service impl) (caller (P := P) (α := α))) (α × PUnit) × Counts) :
    decodePrefix impl (out.1, charge (Q := Q) (.inl q) * out.2) =
      (decodePrefix impl out).query := by
  rcases out with ⟨chunk, counts⟩
  cases chunk <;> simp [decodePrefix, Prefix.query, charge, Nat.add_comm]

open DynSystem.DynComputation in
/-- Entering a finite service consumes one administrative transition. -/
@[freeM_unfold] theorem runPrefix_caller_query (impl : (a : P.A) → FreeM Q (P.B a))
    (fuel : ℕ) (a : P.A) (next : P.B a → FreeM P α) :
    runPrefix impl (fuel + 1) (.caller (.liftBind a next)) =
      Prefix.admin <$> runPrefix impl fuel (.handler a (impl a) next) := by
  rw [runPrefix, unrollChunk_succ, view_encodePhase]
  dsimp only
  rw [Handler.run_liftM_withTraceBefore_liftBind]
  simp only [primitiveHandler, LawfulMonad.pure_bind, runPrefix, Functor.map_map]
  congr 1
  funext out
  exact decodePrefix_admin impl out

open DynSystem.DynComputation in
/-- Returning an answer to the caller consumes one administrative transition. -/
@[freeM_unfold] theorem runPrefix_handler_pure (impl : (a : P.A) → FreeM Q (P.B a))
    (fuel : ℕ) (a : P.A) (answer : P.B a) (next : P.B a → FreeM P α) :
    runPrefix impl (fuel + 1) (.handler a (.pure answer) next) =
      Prefix.admin <$> runPrefix impl fuel (.caller (next answer)) := by
  rw [runPrefix, unrollChunk_succ, view_encodePhase]
  dsimp only
  rw [Handler.run_liftM_withTraceBefore_liftBind]
  simp only [primitiveHandler, LawfulMonad.pure_bind, runPrefix, Functor.map_map]
  congr 1
  funext out
  exact decodePrefix_admin impl out

open DynSystem.DynComputation in
/-- An actual inner operation consumes one query transition. -/
@[freeM_unfold] theorem runPrefix_handler_query (impl : (a : P.A) → FreeM Q (P.B a))
    (fuel : ℕ) (a : P.A) (q : Q.A) (rest : Q.B q → FreeM Q (P.B a))
    (next : P.B a → FreeM P α) :
    runPrefix impl (fuel + 1) (.handler a (.liftBind q rest) next) =
      FreeM.liftBind q fun answer =>
        Prefix.query <$> runPrefix impl fuel (.handler a (rest answer) next) := by
  rw [runPrefix, unrollChunk_succ, view_encodePhase]
  dsimp only
  rw [Handler.run_liftM_withTraceBefore_liftBind]
  simp only [primitiveHandler, _root_.map_bind]
  change FreeM.liftBind q _ = FreeM.liftBind q _
  congr 1
  funext answer
  simp only [FreeM.bind_eq_bind, LawfulMonad.pure_bind, runPrefix, Functor.map_map]
  congr 1
  funext out
  exact decodePrefix_query impl q out

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
  | zero => simp only [runPrefix_zero, LawfulMonad.pure_bind]
  | succ fuel ih =>
      cases phase with
      | caller program =>
          cases program with
          | pure value => rw [runPrefix_caller_pure]; simp [denote]
          | liftBind a next =>
              rw [runPrefix_caller_query]
              simpa [Prefix.admin, bind_map_left, denote] using
                ih (.handler a (impl a) next)
      | handler a program next =>
          cases program with
          | pure answer =>
              rw [runPrefix_handler_pure]
              simpa [Prefix.admin, bind_map_left, denote] using
                ih (.caller (next answer))
          | liftBind b rest =>
              rw [runPrefix_handler_query]
              simp only [denote]
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
  | zero => simp [runPrefix_zero, allOutputs_pure]
  | succ fuel ih =>
      cases phase with
      | caller program =>
          cases program with
          | pure value => rw [runPrefix_caller_pure]; simp [allOutputs_pure]
          | liftBind a next =>
              rw [runPrefix_caller_query, allOutputs_map]
              intro out hout
              have h := ih (.handler a (impl a) next) out hout
              change out.administrative + 1 + out.queries ≤ fuel + 1
              omega
      | handler a program next =>
          cases program with
          | pure answer =>
              rw [runPrefix_handler_pure, allOutputs_map]
              intro out hout
              have h := ih (.caller (next answer)) out hout
              change out.administrative + 1 + out.queries ≤ fuel + 1
              omega
          | liftBind b rest =>
              rw [runPrefix_handler_query, allOutputs_liftBind]
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
          | pure value => rw [runPrefix_caller_pure]; simp [allOutputs_pure]
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
          | pure value => rw [runPrefix_caller_pure]; simp [allOutputs_pure]
          | liftBind a next =>
              rw [isTotalRollBound_liftBind_iff] at hprogram
              obtain ⟨hpos, hnext⟩ := hprogram
              cases n with
              | zero => omega
              | succ n =>
                  rw [runPrefix_caller_query, allOutputs_map]
                  apply ih (.handler a (impl a) next)
                  refine ⟨n, handlerLimit, himpl a, ?_, ?_⟩
                  · simpa using hnext
                  · simp only [Nat.succ_mul] at hsize
                    omega
      | handler a program next =>
          obtain ⟨n, k, hprogram, hnext, hsize⟩ := hbudget
          cases program with
          | pure answer =>
              rw [runPrefix_handler_pure, allOutputs_map]
              exact ih (.caller (next answer)) ⟨n, hnext answer, by omega⟩
          | liftBind b rest =>
              rw [isTotalRollBound_liftBind_iff] at hprogram
              obtain ⟨hpos, hrest⟩ := hprogram
              cases k with
              | zero => omega
              | succ k =>
                  rw [runPrefix_handler_query, allOutputs_liftBind]
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
