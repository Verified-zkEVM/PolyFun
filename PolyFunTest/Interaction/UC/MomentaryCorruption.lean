/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Logic.Equiv.Defs
public import PolyFun.Interaction.UC.MomentaryCorruption
public import PolyFun.Interaction.UC.Leakage

/-!
# Identity and observation examples for momentary-corruption bookkeeping

The updates commute with bijective identity renaming and admit empty and pair
identity types. The boundary examples distinguish update equations from
assumptions about histories or observations. All imports use the public API.
-/

@[expose] public section

open Interaction UC MomentaryCorruption

namespace Interaction.UC.MomentaryCorruptionExamples

/-- Transport the bookkeeping fields along an identity equivalence. -/
def reindex {M N : Type} (e : M ≃ N) (cs : State M) : State N where
  corrupted := cs.corrupted ∘ e.symm
  compromised := cs.compromised ∘ e.symm
  epoch := cs.epoch ∘ e.symm

/-- Identity transport preserves initialization. -/
theorem reindex_init {M N : Type} (e : M ≃ N) :
    reindex e State.init = State.init := rfl

/-- Compromise commutes with bijective identity renaming. -/
theorem reindex_compromise {M N : Type} [DecidableEq M] [DecidableEq N]
    (e : M ≃ N) (x : M) (cs : State M) :
    State.applyCompromise (e x) (reindex e cs) = reindex e (State.applyCompromise x cs) := by
  ext y z
  · simp [reindex, State.applyCompromise, Function.update_apply,
      ← Equiv.eq_symm_apply]
  · simp [reindex, State.applyCompromise, ← Equiv.eq_symm_apply]
  · rfl

/-- Refresh commutes with bijective identity renaming. -/
theorem reindex_refresh {M N : Type} [DecidableEq M] [DecidableEq N]
    (e : M ≃ N) (x : M) (cs : State M) :
    State.applyRefresh (e x) (reindex e cs) = reindex e (State.applyRefresh x cs) := by
  ext y z
  · simp [reindex, State.applyRefresh, Function.update_apply,
      ← Equiv.eq_symm_apply]
  · rfl
  · simp [reindex, State.applyRefresh, Function.update_apply,
      ← Equiv.eq_symm_apply]

example (cs : State Empty) : cs = State.init := by
  ext x
  all_goals exact x.elim

example (a : Alphabet Empty) : False := a.target.elim

/-- A constant observation is a valid snapshot projection. -/
abbrev constantLeak : SnapshotLeakable (Party := Unit) Bool Unit where
  leak _ _ := ()

example : constantLeak.leak true () = constantLeak.leak false () := rfl

-- An epoch already marked compromised remains so after refresh, even if it is in the future.
example :
    let cs : State Unit := { compromised := fun _ _ => true }
    let refreshed := State.applyRefresh () cs
    refreshed.compromised () (refreshed.epoch ()) = true := rfl

-- Pair keys distinguish sessions even when the party coordinate is the same.
example :
    (State.applyCompromise (0, false) (State.init : State (Nat × Bool))).corrupted
      (1, false) = false := by simp [State.applyCompromise]

-- Compromise followed by refresh records epoch zero while leaving epoch one unmarked.
example :
    let cs := State.applyRefresh false (State.applyCompromise false (State.init : State Bool))
    cs.corrupted false = false ∧ cs.epoch false = 1 ∧
      cs.compromised false 0 = true ∧ cs.compromised false 1 = false := by
  simp [State.applyCompromise, State.applyRefresh, State.init]

universe v w

example {M : Type} [DecidableEq M] {m : Type → Type w} [Pure m]
    {Δ : PortBoundary} (p : OpenProcess.{0, v, 0, w} m M Δ) :
    p.withMomentaryCorruption.process = p := rfl

-- A model's process abbreviation fixes the reaction types but permits a passive reaction.
example {M : Type} [DecidableEq M] {m : Type → Type w} [Pure m]
    {Δ : PortBoundary} (p : OpenProcess.{0, v, 0, w} m M Δ) :
    (model M m).Process M Δ :=
  { process := p, envAction := EnvAction.passive (Alphabet M) (State M) }

end Interaction.UC.MomentaryCorruptionExamples
