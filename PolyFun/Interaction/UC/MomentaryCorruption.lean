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
# Momentary corruption: the CJSV22 corruption model

This file ships the **momentary corruption model**: the canonical
adaptive corruption model with refresh-based healing introduced in
Canetti, Jain, Swanberg, Varia, *Universally Composable End-to-End
Secure Messaging* (CRYPTO 2022, §3.2). All names live under the
`MomentaryCorruption.*` namespace so it is unambiguous which
*model* (in the sense of `CorruptionModel`) is in scope.

The model captures:

* **Adaptive compromise.** The environment may issue
  `compromise(m)` for any machine `m` at any time, marking `m`'s
  current epoch as compromised in the adversary's view.
* **Refresh-based healing.** A subsequent `refresh(m)` advances
  `m`'s epoch counter and clears the current `corrupted` snapshot
  flag; future epochs are not (yet) compromised. This is the
  structural ingredient that lets the framework derive
  post-compromise security as a healing theorem rather than as an
  axiom.

The bundled value `MomentaryCorruption.model M` is a
`CorruptionModel` whose `Event` is `Alphabet M` and whose
`State` is `State M` (the two-flag plus epoch tracking). Machines are
identified by an arbitrary type `M` with decidable equality; CJSV22's
`(sid, pid)` pairs are one instantiation, and nothing here depends on
session structure.

## Contents

* **`Alphabet M`** — inductive event alphabet
  `compromise(m) | refresh(m)`, indexed by the machine identity type `M`.
* **`Epoch`** — the per-machine refresh counter (a `ℕ` abbrev).
* **`State M`** — two-flag corruption tracking
  (`corrupted`, `compromised`) plus the per-machine `epoch`
  counter.
* **`State.applyCompromise` / `State.applyRefresh`** — the
  canonical deterministic updates triggered by alphabet events.
* **`react`** — the monad-parametric `Alphabet → State → m State`
  reaction driving the model's `EnvAction`.
* **`envAction`** — the canonical `EnvAction Alphabet State` for
  the model.
* **`model M`** — the bundled `CorruptionModel` value.
* **`Process M m Δ`** — the corruption-aware open-process
  abbreviation: `EnvOpenProcess` of an open process over `M` with this
  model's env channel.
* **`OpenProcess.withMomentaryCorruption`** — the standard
  wrapping that turns an open process over `M` into a `Process`.

## Universe constraint

`M` lives in `Type` (i.e. `Type 0`) because
`State M` is fed to the reaction monad `m : Type → Type w'`,
whose argument must live in `Type 0`. Concrete protocol identity
types (`ℕ`, `String`, pairs of them, etc.) all satisfy this bound. The two
`OpenProcess` universes `(v, w')` are exposed.

## Additive design

The model is **standalone**: nothing here is threaded into
`OpenNodeProfile`. Existing `OpenProcess` constructions are
untouched. The corruption-aware composition operators (par / wire /
plug lifted from `OpenTheory`) and the four `*.corrupt` forwarding
lemmas (CJSV22 §4.2) live in a downstream layer that consumes
`Process` and the model's bundled `envAction`; this file ships only
the data and the per-event reactions.

## Decidability

All comparisons are over the machine identity type `M` and over
`Epoch = ℕ`. The deterministic state updates require
`[DecidableEq M]`; the alphabet, state, and process types themselves
do not.
-/

public section

universe v w'

namespace Interaction
namespace UC
namespace MomentaryCorruption

/-! ## Alphabet and epoch -/

/--
The momentary-corruption event alphabet.

* `compromise m` snapshots the current state of machine `m` into
  the adversary's view: a leakage observer (declared separately,
  e.g. via `SnapshotLeakable`) fires, and the current epoch of `m`
  is marked compromised in the bookkeeping state.
* `refresh m` advances the epoch counter for `m` and clears the
  current snapshot flag. After a refresh, future epochs of `m` are
  not (yet) compromised; the protocol's forward-secrecy mechanism
  gets a chance to heal.

The pair `(compromise, refresh)` is what makes corruption
*momentary* (rather than persistent): at any point the environment
may compromise a machine, and a subsequent refresh recovers
post-compromise security for future epochs.
-/
inductive Alphabet (M : Type) where
  /-- Snapshot the current state of `m` into the adversary's view. -/
  | compromise (m : M) : Alphabet M
  /-- Advance the epoch counter of `m`, enabling forward healing. -/
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
`Epoch` indexes the per-machine refresh cycles.

A flat `ℕ` is the simplest concrete choice: refresh counts as
`epoch m += 1`. Richer protocols (e.g. Signal's asymmetric ratchet
with separate sending and receiving counters) can wrap this in
their own `Epoch`-isomorphic type; the model only requires
`DecidableEq` and a way to advance.
-/
abbrev Epoch : Type := ℕ

/-! ## Bookkeeping state -/

/--
`State M` packages the two-flag corruption tracking that the
model carries between events.

* `corrupted m = true` iff the current state of `m` has been
  snapshotted by the adversary at least once and not refreshed
  since. Mutated by `compromise m` (sets `true`) and `refresh m`
  (sets `false`).
* `compromised m e = true` iff the secrets for epoch `e` of `m`
  are in the adversary's view. Strictly accumulating: a compromise
  event sets `compromised m (current_epoch m)`; epochs once
  compromised stay compromised forever.
* `epoch m` is `m`'s current refresh counter. Mutated by
  `refresh m` (increments by one).

The two flags `corrupted` and `compromised` are deliberately
independent:

* `corrupted m` may be `false` while `compromised m e` holds for
  some past `e`: the adversary saw that epoch's secret, but the
  machine has since refreshed and now has a fresh secret.
* `corrupted m` may be `true` while `compromised m e'` is `false`
  for some future `e'`: a forward-secret key schedule may
  forward-decrypt only a bounded window from a current compromise.

Two flags, two distinct purposes. The naming deliberately avoids
the ambiguous "exposed", which would collide with `OpenTheory`'s
boundary-exposure terminology.
-/
@[ext]
structure State (M : Type) where
  /-- Per-machine snapshot flag, mutated by `compromise` and `refresh`. -/
  corrupted : M → Bool := fun _ => false
  /-- Per-(machine, epoch) leak flag, monotonically accumulating. -/
  compromised : M → Epoch → Bool := fun _ _ => false
  /-- Per-machine refresh counter, advanced by `refresh`. -/
  epoch : M → Epoch := fun _ => 0

namespace State

variable {M : Type}

/--
The fully-honest initial state: nothing corrupted, nothing
compromised, every machine at epoch zero.
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
Apply `refresh m` to the bookkeeping state: clear `corrupted m`
and advance the epoch counter of `m` by one. Past `compromised`
flags are preserved (they are historical and accumulate).

After a refresh, future events on `m` write into the new epoch;
this is the structural ingredient that lets the model derive PCS
(post-compromise security) as a healing theorem rather than as an
axiom.
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
`compromise` is monotone: once an epoch is in the adversary's view,
it stays in the adversary's view. This is the structural fact that
makes PCS (post-compromise security) about *future* epochs rather
than about un-leaking past ones.
-/
theorem compromised_applyCompromise_of_compromised {cs : State M} {m : M}
    {m' : M} {e : Epoch} (h : cs.compromised m' e = true) :
    (applyCompromise m cs).compromised m' e = true := by
  simp [applyCompromise, h]

/-- `refresh` preserves all past compromise flags. -/
@[simp] theorem compromised_applyRefresh (m : M) (cs : State M) :
    (applyRefresh m cs).compromised = cs.compromised := rfl

end State

/-! ## Reaction and bundled model -/

variable {M : Type} [DecidableEq M]
variable {m : Type → Type w'} [Pure m]

/--
The canonical `EnvAction` reaction for the momentary-corruption
alphabet: `compromise` snapshots, `refresh` advances the epoch.

This is the baseline used by every protocol that opts in to
momentary corruption. Protocols that need richer per-event
behaviour (e.g. simulator-controlled randomization on `compromise`,
or a non-trivial leakage function) build their own `EnvAction`
rather than overriding individual branches here.

The reaction is monad-parametric: any `[Pure m]` works, and
deterministic protocols typically use `m := Id` while crypto-flavored
consumers instantiate `m := ProbComp`.
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
`Process M m Δ` is the canonical open process for the
momentary-corruption model: an open process over the machine identity
type `M` paired with this model's env channel.

The type-level definition does not depend on `[DecidableEq M]`; the
typeclass requirement only appears when one constructs the env action's
reaction (e.g. via `OpenProcess.withMomentaryCorruption`).
-/
abbrev Process (M : Type) (m : Type → Type w') [Pure m] (Δ : PortBoundary) :=
  EnvOpenProcess.{0, 0, v, 0, w'} m (M) Δ
    (Alphabet M) (State M)

end MomentaryCorruption

/--
Wrap an open process over the machine identity type `M` with the
canonical momentary-corruption env channel, yielding a
`MomentaryCorruption.Process`.

This is the **standard inhabitant**: `compromise(m)` snapshots
`m`'s current epoch into the adversary's view (sets `corrupted m`
and `compromised m (epoch m)`), and `refresh(m)` advances `m`'s
epoch counter and clears `corrupted m`.

Protocols that need richer per-event behaviour (e.g.
simulator-controlled randomization on `compromise`, or a
non-trivial leakage function that depends on the protocol state)
build their `EnvOpenProcess` directly with a bespoke `EnvAction`
rather than going through this wrapping.
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
