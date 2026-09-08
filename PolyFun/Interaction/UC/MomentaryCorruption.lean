/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.UC.CorruptionModel
public import PolyFun.Interaction.UC.EnvAction
public import PolyFun.Interaction.UC.EnvOpenProcess

/-!
# Momentary-corruption bookkeeping

`MomentaryCorruption` tracks compromise flags and refresh counters for identities
in an arbitrary type `M`. The deterministic updates have the following effects:

* `compromise m` sets `corrupted m` and marks the current epoch of `m` in
  `compromised`.
* `refresh m` clears `corrupted m` and increments `epoch m`. It preserves the
  entire `compromised` function, including any flags for future epochs supplied
  in the input state.

`react` returns these updates through `pure`, and `model M m` bundles them as a
`CorruptionModel m`. `OpenProcess.withMomentaryCorruption` pairs an open process
with this reaction on a separate bookkeeping state. Connecting events to
protocol-state observations, secret updates, or execution scheduling requires
consumer-supplied semantics. The definitions and equations here establish no
post-compromise security or leakage guarantee.

## Identity and universes

The alphabet, state, and process types accept any `M : Type`; the updates and
canonical reaction require `[DecidableEq M]`. Pair identities can be supplied as
`M := Sid × Pid`. No session structure is used by the updates.

The identity and bookkeeping types live in `Type 0`, matching the input
universe of `m : Type → Type w'` in `CorruptionModel`. The process-state universe
`v` and the monad-output universe `w'` remain independent.

## References

CJSV22, *Universally Composable End-to-End Secure Messaging*, motivates the
compromise/refresh vocabulary; see `REFERENCES.md`. Its protocol-specific
recovery arguments require secret-state semantics and key evolution beyond the
bookkeeping implemented here.
-/

public section

universe v w'

namespace Interaction
namespace UC
namespace MomentaryCorruption

/-! ## Alphabet and epoch -/

/--
Events selecting the compromise or refresh update for an identity.
Their interpretation on bookkeeping state is given by `react`.
-/
inductive Alphabet (M : Type) where
  /-- Mark the current epoch of `m` as compromised. -/
  | compromise (m : M) : Alphabet M
  /-- Advance the epoch counter of `m` and clear its current corruption flag. -/
  | refresh    (m : M) : Alphabet M
deriving DecidableEq

namespace Alphabet

variable {M : Type}

/-- The machine targeted by an event. -/
@[expose]
def target : Alphabet M → M
  | .compromise m => m
  | .refresh m    => m

@[simp] theorem target_compromise (m : M) :
    (compromise m).target = m := rfl

@[simp] theorem target_refresh (m : M) :
    (refresh m).target = m := rfl

end Alphabet

/--
The natural-number counter advanced by each refresh of an identity.
-/
abbrev Epoch : Type := ℕ

/-! ## Bookkeeping state -/

/--
Flags and counters carried between events.

* `corrupted m` is set by `compromise m` and cleared by `refresh m`.
* `compromised m e` records a flag for identity `m` at epoch `e`. Compromise
  marks the current epoch, and both updates preserve previously set flags.
* `epoch m` is incremented by `refresh m`.

The structure admits arbitrary field values. Relating the flags to an event
history requires a reachability invariant from `State.init`; relating them to
an observer's knowledge requires a separate semantic interpretation.
-/
@[ext]
structure State (M : Type) where
  /-- Current corruption flag, set by `compromise` and cleared by `refresh`. -/
  corrupted : M → Bool := fun _ => false
  /-- Per-(identity, epoch) compromise flag, preserved by both updates once true. -/
  compromised : M → Epoch → Bool := fun _ _ => false
  /-- Per-machine refresh counter, advanced by `refresh`. -/
  epoch : M → Epoch := fun _ => 0

namespace State

variable {M : Type}

/--
The initial bookkeeping state: all flags false and every epoch counter zero.
-/
@[expose]
def init : State M := {}

instance : Inhabited (State M) := ⟨init⟩

@[simp] theorem corrupted_init (m : M) :
    (init : State M).corrupted m = false := rfl

@[simp] theorem compromised_init (m : M) (e : Epoch) :
    (init : State M).compromised m e = false := rfl

@[simp] theorem epoch_init (m : M) :
    (init : State M).epoch m = 0 := rfl

variable [DecidableEq M]

/--
Apply `compromise m` to the bookkeeping state: set `corrupted m`
and mark the current epoch of `m` as compromised. The epoch counter
is not advanced.

This is a deterministic update, so the value lives in the
underlying `State`; the canonical `EnvAction` reaction wraps it
via `pure`.
-/
@[expose]
def applyCompromise (m : M) (cs : State M) : State M where
  corrupted := Function.update cs.corrupted m true
  compromised := fun m' e' =>
    cs.compromised m' e' || (decide (m = m') && decide (e' = cs.epoch m))
  epoch := cs.epoch

/--
Clear `corrupted m` and advance the epoch counter of `m` by one.
The entire `compromised` function is preserved, regardless of the recorded
epochs. Subsequent compromise events mark the new current epoch.
-/
@[expose]
def applyRefresh (m : M) (cs : State M) : State M where
  corrupted := Function.update cs.corrupted m false
  compromised := cs.compromised
  epoch := Function.update cs.epoch m (cs.epoch m + 1)

@[simp] theorem corrupted_applyCompromise_self (m : M) (cs : State M) :
    (applyCompromise m cs).corrupted m = true := by
  simp [applyCompromise]

theorem corrupted_applyCompromise_of_ne
    {m m' : M} (h : m' ≠ m) (cs : State M) :
    (applyCompromise m cs).corrupted m' = cs.corrupted m' := by
  simp [applyCompromise, Function.update_of_ne h]

@[simp] theorem corrupted_applyRefresh_self (m : M) (cs : State M) :
    (applyRefresh m cs).corrupted m = false := by
  simp [applyRefresh]

theorem corrupted_applyRefresh_of_ne
    {m m' : M} (h : m' ≠ m) (cs : State M) :
    (applyRefresh m cs).corrupted m' = cs.corrupted m' := by
  simp [applyRefresh, Function.update_of_ne h]

@[simp] theorem epoch_applyCompromise (m : M) (cs : State M) :
    (applyCompromise m cs).epoch = cs.epoch := rfl

@[simp] theorem epoch_applyRefresh_self (m : M) (cs : State M) :
    (applyRefresh m cs).epoch m = cs.epoch m + 1 := by
  simp [applyRefresh]

theorem epoch_applyRefresh_of_ne {m m' : M} (h : m' ≠ m) (cs : State M) :
    (applyRefresh m cs).epoch m' = cs.epoch m' := by
  simp [applyRefresh, Function.update_of_ne h]

theorem compromised_applyCompromise_self_currentEpoch (m : M) (cs : State M) :
    (applyCompromise m cs).compromised m (cs.epoch m) = true := by
  simp [applyCompromise]

/--
Compromise preserves every flag that was already set, for any identity and epoch.
-/
theorem compromised_applyCompromise_of_compromised {cs : State M} {m : M}
    {m' : M} {e : Epoch} (h : cs.compromised m' e = true) :
    (applyCompromise m cs).compromised m' e = true := by
  simp [applyCompromise, h]

/-- Refresh preserves all compromise flags. -/
@[simp] theorem compromised_applyRefresh (m : M) (cs : State M) :
    (applyRefresh m cs).compromised = cs.compromised := rfl

end State

/-! ## Reaction and bundled model -/

variable {M : Type} [DecidableEq M]
variable {m : Type → Type w'} [Pure m]

/--
Return the deterministic bookkeeping update selected by an event through `pure`.
Any `[Pure m]` suffices; `m := Id` gives the underlying state update.
-/
@[expose]
def react (s : Alphabet M) (cs : State M) : m (State M) :=
  match s with
  | .compromise m₀ => pure (State.applyCompromise m₀ cs)
  | .refresh m₀    => pure (State.applyRefresh m₀ cs)

/-- The canonical momentary-corruption `EnvAction`. -/
@[expose]
def envAction : EnvAction m (Alphabet M) (State M) where
  react := react

@[simp] theorem react_compromise (m₀ : M) (cs : State M) :
    (react (m := m) (.compromise m₀) cs) =
      (pure (State.applyCompromise m₀ cs) : m (State M)) := rfl

@[simp] theorem react_refresh (m₀ : M) (cs : State M) :
    (react (m := m) (.refresh m₀) cs) =
      (pure (State.applyRefresh m₀ cs) : m (State M)) := rfl

@[simp] theorem envAction_react :
    (envAction (m := m) (M := M)).react = react := rfl

/--
The momentary-corruption model bundled as a `CorruptionModel`.

Use this when you want to talk about the model abstractly through
the `CorruptionModel` API — for instance, when stating a lemma
that is generic over corruption models but instantiated to the
momentary case at a use site.
-/
@[expose]
def model (M : Type) [DecidableEq M] (m : Type → Type w') [Pure m] :
    CorruptionModel m where
  Event := Alphabet M
  State := State M
  envAction := envAction

@[simp] theorem model_Event : (model M m).Event = Alphabet M := rfl

@[simp] theorem model_State : (model M m).State = State M := rfl

@[simp] theorem model_envAction : (model M m).envAction = envAction := rfl

/-! ## Canonical corruption-aware open process -/

/--
Open processes over `M` paired with a reaction on `Alphabet M` and `State M`.
Each value supplies its reaction; `OpenProcess.withMomentaryCorruption`
supplies the canonical `envAction`.

The type requires only `[Pure m]`. Constructing the canonical reaction
additionally requires `[DecidableEq M]`.
-/
abbrev Process (M : Type) (m : Type → Type w') [Pure m] (Δ : PortBoundary) :=
  EnvOpenProcess.{0, 0, v, 0, w'} m (M) Δ
    (Alphabet M) (State M)

end MomentaryCorruption

/--
Pair an open process with `MomentaryCorruption.envAction` on a separate
`MomentaryCorruption.State M`. The underlying process is preserved
definitionally; events update only the bookkeeping state passed to `react`.
-/
@[expose]
def OpenProcess.withMomentaryCorruption
    {M : Type} {m : Type → Type w'} [Pure m] {Δ : PortBoundary}
    [DecidableEq M]
    (P : OpenProcess.{0, v, 0, w'} m M Δ) :
    MomentaryCorruption.Process.{v, w'} M m Δ where
  process := P
  envAction := MomentaryCorruption.envAction

namespace OpenProcess

variable {M : Type} {m : Type → Type w'} [Pure m] {Δ : PortBoundary}
  [DecidableEq M]

@[simp] theorem process_withMomentaryCorruption (P : OpenProcess.{0, v, 0, w'} m M Δ) :
    P.withMomentaryCorruption.process = P := rfl

@[simp] theorem envAction_withMomentaryCorruption (P : OpenProcess.{0, v, 0, w'} m M Δ) :
    P.withMomentaryCorruption.envAction = MomentaryCorruption.envAction := rfl

@[simp]
theorem react_withMomentaryCorruption_compromise
    (P : OpenProcess.{0, v, 0, w'} m M Δ)
    (mid : M) (cs : MomentaryCorruption.State M) :
    P.withMomentaryCorruption.react (.compromise mid) cs =
      (pure (MomentaryCorruption.State.applyCompromise mid cs) :
        m (MomentaryCorruption.State M)) := rfl

@[simp]
theorem react_withMomentaryCorruption_refresh
    (P : OpenProcess.{0, v, 0, w'} m M Δ)
    (mid : M) (cs : MomentaryCorruption.State M) :
    P.withMomentaryCorruption.react (.refresh mid) cs =
      (pure (MomentaryCorruption.State.applyRefresh mid cs) :
        m (MomentaryCorruption.State M)) := rfl

end OpenProcess

end UC
end Interaction
