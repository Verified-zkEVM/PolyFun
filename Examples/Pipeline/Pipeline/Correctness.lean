/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Pipeline.Network
public import PolyFun.Control.Monad.Support.Instances

/-! # Correctness of the token protocol

The mathematical filesystem is an arbitrary total map into success or read error. IO handlers
are tested separately: this theorem does not assert that real files remain unchanged between reads.
The invariant is the actual routed residual, not a replacement operational interpreter.
-/

@[expose] public section

namespace Pipeline

open PFunctor DynSystem Interaction Interaction.Execution ReactiveNetwork

/-- A concrete deterministic environment, including arbitrary per-path read failures. -/
abbrev FileMap := String → Except String ByteArray

/-- A between-files configuration of the same network, retaining accumulated output. -/
def ready (files : FileMap) (paths remaining : List String) (entries : List Entry)
    (elapsed : Nat) : State ((assembly (m := Id) files paths).diagram.network
      (collectorId (m := Id) files paths)) Unit where
  localState
    | .inl (.inl _) => LoaderState.waiting
    | .inl (.inr _) => (none : Option Entry)
    | .inr _ => collect remaining entries
  inbox _ := []
  service := ()
  pending := []
  output := []
  focus := collectorId (m := Id) files paths
  elapsed := elapsed

/-- The library's initial configuration is exactly the empty accumulated report. -/
theorem initial_eq_ready (files : FileMap) (paths : List String) :
    (assembly (m := Id) files paths).diagram.initial (collectorId (m := Id) files paths) =
      ready files paths paths [] 0 := by
  apply State.ext
  · funext node
    rcases node with (node | node) | node <;> cases node <;> rfl
  all_goals rfl

/-- Nine routed activations deliver the analysed reply and retain the entry. -/
theorem runToken_nine (files : FileMap) (paths : List String) (path : String)
    (remaining : List String) (entries : List Entry) (elapsed : Nat) :
    (assembly (m := Id) files paths).diagram.runToken (collectorId (m := Id) files paths) 9
        (ready files paths (path :: remaining) entries elapsed) =
      ready files paths remaining (analyse (path, files path) :: entries) (elapsed + 9) := by
  cbv
  apply State.ext
  · funext node
    rcases node with (node | node) | node <;> cases node <;> cbv
  · funext node
    rcases node with (node | node) | node <;> cases node <;> cbv
  all_goals rfl

/-- The routed residual contains exactly the reports for all remaining inputs. -/
theorem runToken_complete (files : FileMap) (paths remaining : List String)
    (entries : List Entry) (elapsed : Nat) :
    (assembly (m := Id) files paths).diagram.runToken (collectorId files paths)
        (9 * remaining.length) (ready files paths remaining entries elapsed) =
      ready files paths []
        ((remaining.map fun path ↦ analyse (path, files path)).reverse ++ entries)
        (elapsed + 9 * remaining.length) := by
  induction remaining generalizing entries elapsed with
  | nil => rfl
  | cons path remaining ih =>
    rw [List.length_cons, show 9 * (remaining.length + 1) = 9 + 9 * remaining.length by omega,
      HandledDiagram.runToken_add, runToken_nine]
    change (assembly (m := Id) files paths).diagram.runToken (collectorId files paths)
      (9 * remaining.length) (ready files paths remaining
        (analyse (path, files path) :: entries) (elapsed + 9)) = _
    rw [ih]
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, Nat.add_assoc]

/-- An exhausted input list returns the accumulated report, with no extra activation. -/
theorem outcome_ready_nil (files : FileMap) (paths : List String)
    (entries : List Entry) (elapsed : Nat) :
    outcome (collectorId (m := Id) files paths) (ready files paths [] entries elapsed) =
      some (.returned entries.reverse) := rfl

/-- The default activation budget completes every finite deterministic file report,
including repeated paths and arbitrary read errors. -/
theorem run_complete (files : FileMap) (paths : List String) :
    outcome (collectorId (m := Id) files paths)
        (run (m := Id) files paths (activationBudget paths)) =
      some (.returned (paths.map fun path ↦ analyse (path, files path))) := by
  unfold run activationBudget
  rw [initial_eq_ready, runToken_complete, outcome_ready_nil]
  simp

/-- The pure specialisation of the independent sequential interpreter. -/
theorem reference_eq_map (files : FileMap) (paths : List String) :
    reference (m := Id) files paths = paths.map (fun path ↦ analyse (path, files path)) := by
  induction paths with
  | nil => rfl
  | cons path paths ih =>
    simp only [reference, List.mapM_cons, List.map_cons]
    exact congrArg (List.cons (analyse (path, files path))) ih

/-- The composed network agrees with the sequential specification at the default budget. -/
theorem run_eq_reference (files : FileMap) (paths : List String) :
    outcome (collectorId (m := Id) files paths)
        (run (m := Id) files paths (activationBudget paths)) =
      some (.returned (reference (m := Id) files paths)) := by
  rw [run_complete, reference_eq_map]

/-- Reachability retains an actual token prefix, including prefixes ending mid-file. -/
def Reachable (files : FileMap) (paths : List String)
    (state : State ((assembly (m := Id) files paths).diagram.network
      (collectorId files paths)) Unit) :
    Prop := ∃ fuel, run (m := Id) files paths fuel = state

/-- The elapsed counter records the length of the actual prefix. -/
theorem elapsed_run (files : FileMap) (paths : List String) (fuel : Nat) :
    (run (m := Id) files paths fuel).elapsed = fuel := by
  simpa only [HandledDiagram.initial, ReactiveNetwork.initial, Nat.zero_add] using
    elapsed_runToken (m := Id)
    ((assembly (m := Id) files paths).diagram.handlers (collectorId files paths)) fuel
    ((assembly (m := Id) files paths).diagram.initial (collectorId files paths))
    (run (m := Id) files paths fuel) rfl

/-- Extra activations preserve an already completed report. -/
theorem run_complete_of_le (files : FileMap) (paths : List String) (fuel : Nat)
    (bound : activationBudget paths ≤ fuel) :
    outcome (collectorId (m := Id) files paths) (run (m := Id) files paths fuel) =
      some (.returned (reference (m := Id) files paths)) := by
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le bound
  rw [run_add]
  exact outcome_runToken_of_some (m := Id) _ rest _ _ _ _ (run_eq_reference files paths) rfl

/-- A global activation certificate for the actual deterministic routed network.
The rank decreases even when a prefix ends between reading and forwarding a file. -/
def budgetCertificate (files : FileMap) (paths : List String) :
    TokenBudgetCertificate ((assembly (m := Id) files paths).diagram.handlers
      (collectorId files paths)) (Reachable files paths) where
  rank state := activationBudget paths - state.elapsed
  zero state reachable zero := by
    obtain ⟨fuel, rfl⟩ := reachable
    rw [elapsed_run] at zero
    exact ⟨_, run_complete_of_le files paths fuel (by omega)⟩
  preserves state next reachable step := by
    obtain ⟨fuel, rfl⟩ := reachable
    refine ⟨fuel + 1, ?_⟩
    rw [run_add]
    change activate (m := Id) _ .token _ _ = next
    exact step
  decreases state next reachable unfinished step := by
    have elapsed := elapsed_activate (m := Id) _ .token state.focus state next step
    obtain ⟨fuel, rfl⟩ := reachable
    rw [elapsed_run] at elapsed ⊢
    have unfinishedBound : fuel < activationBudget paths := by
      by_contra! bound
      have complete := run_complete_of_le files paths fuel bound
      change outcome (collectorId (m := Id) files paths) _ = none at unfinished
      rw [unfinished] at complete
      contradiction
    omega
  progress state _ := ⟨_, rfl⟩

end Pipeline
