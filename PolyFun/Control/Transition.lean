/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.Sum.Basic

/-!
# Deterministic transitions with exact residual states

One transition either returns a result or supplies the next state. Each call to
the transition function consumes one unit of fuel, including the call reporting
termination. Exhausted fuel retains the exact state and is not an error or a
claim of divergence. Result types, including any language-specific errors, are
parameters of this interface.
-/

public section

namespace Control

/-- A total deterministic transition with a terminating result branch. -/
abbrev Transition (S R : Type*) := S → R ⊕ S

namespace Transition

variable {S R : Type*} (next : Transition S R)

/-- Execute a finite number of transitions, retaining any residual state. -/
@[expose] def run : Nat → S → R ⊕ S
  | 0, state => .inr state
  | n + 1, state => match next state with
      | .inl result => .inl result
      | .inr state' => run n state'

/-- Resume a residual; a returned result is already final. -/
@[expose] def continueRun (fuel : Nat) : R ⊕ S → R ⊕ S
  | .inl result => .inl result
  | .inr state => run next fuel state

/-- Splitting the fuel budget preserves results and exact residual states. -/
theorem run_add (n m : Nat) (state : S) :
    run next (n + m) state = continueRun next m (run next n state) := by
  induction n generalizing state with
  | zero => simp [run, continueRun]
  | succ n ih =>
      simp only [Nat.succ_add, run]
      cases next state with
      | inl result => rfl
      | inr state' => exact ih state'

/-- A finite derivation of terminating execution. -/
inductive Executes : S → R → Prop where
  | done {state result} (h : next state = .inl result) : Executes state result
  | next {state state' result} (h : next state = .inr state')
      (tail : Executes state' result) : Executes state result

/-- Some finite transition budget returns the specified result. -/
@[expose] def Terminates (state : S) (result : R) : Prop :=
  ∃ fuel, run next fuel state = .inl result

/-- Inductive execution and finite successful chunks describe the same behavior. -/
theorem executes_iff_terminates (state : S) (result : R) :
    Executes next state result ↔ Terminates next state result := by
  constructor
  · intro h
    induction h with
    | done hs => exact ⟨1, by simp [run, hs]⟩
    | next hs _ ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, by simp [run, hs, hn]⟩
  · rintro ⟨n, hn⟩
    induction n generalizing state with
    | zero => cases hn
    | succ n ih =>
        cases hs : next state with
        | inl out =>
            have : out = result := by simpa [run, hs] using hn
            exact .done (this ▸ hs)
        | inr state' => exact .next hs (ih state' (by simpa [run, hs] using hn))

/-- Deterministic execution has a unique terminating result. -/
theorem Executes.unique {state : S} {left right : R}
    (hl : Executes next state left) (hr : Executes next state right) : left = right := by
  induction hl with
  | done h =>
      cases hr with
      | done h' => exact Sum.inl.inj (h.symm.trans h')
      | next h' _ => cases h.symm.trans h'
  | next h _ ih =>
      cases hr with
      | done h' => cases h.symm.trans h'
      | next h' tail =>
          have heq := Sum.inr.inj (h.symm.trans h')
          subst heq
          exact ih tail

/-- Equal next transitions have the same terminating executions. -/
theorem Executes.of_step_eq {state state' : S} {result : R}
    (h : next state = next state') (hr : Executes next state' result) :
    Executes next state result := by
  cases hr with
  | done h' => exact .done (h.trans h')
  | next h' tail => exact .next (h.trans h') tail

/-- A preserved state interpretation computes the meaning of every returned result. -/
theorem Executes.meaning {D : Type*} (stateMeaning : S → D) (resultMeaning : R → D)
    (preserve : ∀ state, stateMeaning state =
      Sum.elim resultMeaning stateMeaning (next state))
    {state : S} {result : R} (h : Executes next state result) :
    stateMeaning state = resultMeaning result := by
  induction h with
  | @done state result hs => simpa [hs] using preserve state
  | @next state state' result hs _ ih =>
      have he : stateMeaning state = stateMeaning state' := by
        simpa [hs] using preserve state
      exact he.trans ih

end Transition
end Control
