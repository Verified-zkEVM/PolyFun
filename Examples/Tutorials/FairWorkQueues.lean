/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Concurrent.Fairness
import Mathlib.Order.Monotone.Basic

/-! # Two finite work queues under an explicit scheduler

Polling a queue completes one pending job, or does nothing when it is empty. Both polls are
always enabled: weak fairness therefore requires both stable queue tickets to recur. With no
new arrivals, fairness drains every finite backlog. A legal scheduler can still starve a queue;
the runtime does not supply the fairness hypothesis automatically.
-/

@[expose] public section

namespace PolyFunExamples.FairWorkQueues

open Interaction Interaction.Concurrent PFunctor

/-- Number of pending jobs in each of two queues. -/
abbrev Queues := Bool → Nat

/-- One completed job from the selected queue; polling an empty queue is harmless. -/
def service (queues : Queues) (selected : Bool) : Queues :=
  Function.update queues selected (queues selected - 1)

/-- One visible scheduler choice per step, using the existing concurrent process substrate. -/
def process : Process Queues Unit :=
  ProcessOver.ofStep Queues fun queues ↦
    { tree := .node Bool (fun _ ↦ .done)
      semantics := ⟨{ controllers := fun _ ↦ [()], views := fun _ ↦ .pick }, fun _ ↦ PUnit.unit⟩
      next := fun path ↦ service queues path.1 }

/-- Queue identities remain the same scheduling obligations at every residual state. -/
@[implicit_reducible] def ticketed : Process.Ticketed Unit where
  State := Queues
  toDynSystem := process
  Ticket := Bool
  ticket _ path := path.1

/-- A standard input-driven machine supplies runs from an explicit choice stream. -/
def worker : MooreMachine Queues Unit Bool := (fun _ ↦ ()) ⇆ service

/-- Lift the standard Moore-machine run into the concurrent protocol's one-choice paths. -/
def scheduled (initial : Queues) (choose : Nat → Bool) : Process.Run process where
  state := worker.stateStream initial choose
  dir n := ⟨choose n, PUnit.unit⟩
  next_state n := worker.stateStream_succ initial choose n

/-- Either queue may always be polled, including after it empties. -/
theorem enabled (run : Process.Run process) (slot : Bool) (n : Nat) :
    Process.Ticketed.enabledAt ticketed run slot n :=
  (ProcessOver.Ticketed.enabledAt_iff _ _ _ _).mpr ⟨⟨slot, PUnit.unit⟩, rfl⟩

/-- The protocol step retains the actual selected queue as its stable ticket. -/
theorem state_succ (run : Process.Run process) (n : Nat) :
    run.state (n + 1) = service (run.state n) (run.dir n).1 := run.next_state n

/-- With no arrivals, every queue's pending count is nonincreasing. -/
theorem pending_antitone (run : Process.Run process) (slot : Bool) :
    Antitone (fun n ↦ run.state n slot) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [state_succ]
  simp only [service, Function.update_apply]
  split
  · next h => simp [h]
  · exact le_rfl

/-- Fair service drains an arbitrary finite backlog after any starting time. -/
theorem eventually_empty (run : Process.Run process)
    (fair : Process.Ticketed.WeakFair ticketed run) (slot : Bool) (start : Nat) :
    ∃ n, start ≤ n ∧ run.state n slot = 0 := by
  have onSlot := (ProcessOver.Ticketed.weakFair_iff _ _).mp fair slot
  have persistent := ProcessOver.Run.eventuallyAlways_iff.mpr
    ⟨0, fun n _ ↦ enabled run slot n⟩
  have recurring := (ProcessOver.Ticketed.weakFairOn_iff _ _ _).mp onSlot persistent
  rw [ProcessOver.Run.infinitelyOften_iff] at recurring
  suffices ∀ count time, run.state time slot ≤ count →
      ∃ n, time ≤ n ∧ run.state n slot = 0 from this _ start le_rfl
  intro count
  induction count with
  | zero => intro time h; exact ⟨time, le_rfl, Nat.eq_zero_of_le_zero h⟩
  | succ count ih =>
    intro time h
    obtain ⟨next, hnext, fired⟩ := recurring time
    have hmono := pending_antitone run slot hnext
    change run.state next slot ≤ run.state time slot at hmono
    have selected : (run.dir next).1 = slot :=
      (ProcessOver.Ticketed.firedAt_iff _ _ _ _).mp fired
    have hstep : run.state (next + 1) slot = run.state next slot - 1 := by
      rw [state_succ, selected]
      simp [service]
    obtain ⟨finish, hfinish, hempty⟩ := ih (next + 1) (by omega)
    exact ⟨finish, by omega, hempty⟩

/-- An alternating choice stream needs no probabilistic interpretation. -/
def alternating (n : Nat) : Bool := n % 2 == 1

/-- Alternation satisfies strong fairness for each queue, and hence weak fairness. -/
theorem alternating_fair (initial : Queues) :
    Process.Ticketed.StrongFair ticketed (scheduled initial alternating) := by
  apply (ProcessOver.Ticketed.strongFair_iff ticketed _).mpr
  intro slot
  apply (ProcessOver.Ticketed.strongFairOn_iff ticketed _ slot).mpr
  intro _
  rw [ProcessOver.Run.infinitelyOften_iff]
  intro n
  cases slot with
  | false =>
    refine ⟨2 * n, by omega, ?_⟩
    apply (ProcessOver.Ticketed.firedAt_iff ticketed _ _ _).mpr
    change alternating (2 * n) = false
    simp [alternating]
  | true =>
    refine ⟨2 * n + 1, by omega, ?_⟩
    apply (ProcessOver.Ticketed.firedAt_iff ticketed _ _ _).mpr
    change alternating (2 * n + 1) = true
    simp [alternating]

/-- A valid run can permanently ignore the second queue. -/
def starving : Process.Run process where
  state _ slot := if slot then 1 else 0
  dir _ := ⟨false, PUnit.unit⟩
  next_state _ := by funext slot; cases slot <;> rfl

/-- Starvation is observable and contradicts fairness, not the transition semantics. -/
theorem starving_not_fair : ¬ Process.Ticketed.WeakFair ticketed starving := by
  intro fair
  obtain ⟨n, _, h⟩ := eventually_empty starving fair true 0
  change 1 = 0 at h
  contradiction

/-- Four alternating polls drain backlogs of two and one. -/
example : (scheduled (fun slot ↦ if slot then 1 else 2) alternating).state 4 =
    (fun _ ↦ 0) := by funext slot; cases slot <;> rfl

end PolyFunExamples.FairWorkQueues
