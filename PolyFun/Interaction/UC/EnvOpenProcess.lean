/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.UC.OpenProcess
public import PolyFun.Interaction.UC.EnvAction

/-!
# Open processes paired with an environment-event channel

`EnvOpenProcess m Party Δ Event State` bundles an `OpenProcess m Party Δ` with
an `EnvAction m Event State`. Its `react` projection acts on the supplied
`State`, independently of the process's internal state. A consumer provides any
scheduling or state connection between environment reactions and process steps.

The wrapper supports an empty alphabet (`ofOpenProcess`), a reaction that
preserves state (`passive`), alphabet adaptation (`comapEvent`), reaction
replacement (`withEnvAction`), and boundary adaptation (`mapBoundary`).
Composition of reactions requires a consumer-selected combination strategy.

`MomentaryCorruption.Process M m Δ` specializes the wrapper with
`Event := MomentaryCorruption.Alphabet M` and
`State := MomentaryCorruption.State M`. Its canonical wrapper is
`OpenProcess.withMomentaryCorruption`, defined in
`PolyFun/Interaction/UC/MomentaryCorruption.lean`.
-/

public section

universe u uE v w w'

namespace Interaction
namespace UC

/--
An open process and an independent environment-event reaction.

`process` supplies the port boundary and process behavior; `envAction` describes
how events update a separate state of type `State`. The wrapper carries no
relation between that state and the internal state of `process`.

The environment state lives in `Type w`, matching the input universe of
`m : Type w → Type w'`. The party, event, and process-state universes remain
independent.
-/
@[ext]
structure EnvOpenProcess (m : Type w → Type w') [Pure m] (Party : Type u) (Δ : PortBoundary)
    (Event : Type uE) (State : Type w) where
  /-- The underlying open process exposing the boundary `Δ`. -/
  process : OpenProcess.{u, v, w, w'} m Party Δ
  /-- The environment-event channel acting on `State` under `Event`. -/
  envAction : EnvAction m Event State

namespace EnvOpenProcess

variable {m : Type w → Type w'} [Pure m] {Party : Type u} {Δ : PortBoundary}
  {Event : Type uE} {State : Type w}

/-! ## Projections -/

/--
Forget the environment channel and view as a plain `OpenProcess`.

This is the canonical projection: it drops the env action and retains
only the open-process boundary surface.
-/
@[expose, reducible]
def toOpenProcess (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State) :
    OpenProcess.{u, v, w, w'} m Party Δ := E.process

/--
React to an environment event on the env-side state, delegating to the
underlying `EnvAction.react`.

Provided as a top-level projection so that downstream consumers can
write `E.react e s` without unfolding the wrapper.
-/
@[expose]
def react (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State)
    (e : Event) (s : State) : m State :=
  E.envAction.react e s

@[simp]
theorem react_eq_envAction_react (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State)
    (e : Event) (s : State) :
    E.react e s = E.envAction.react e s := rfl

/-! ## Canonical wrappings -/

/--
Wrap an `OpenProcess` with the trivial empty alphabet: no environment
events ever fire.

This is the canonical no-op wrapping: every existing `OpenProcess`
embeds into `EnvOpenProcess _ _ Empty State` for any `State`.
-/
@[expose]
def ofOpenProcess (P : OpenProcess.{u, v, w, w'} m Party Δ) (S : Type w) :
    EnvOpenProcess.{u, 0, v, w, w'} m Party Δ Empty S where
  process := P
  envAction := EnvAction.empty S

@[simp]
theorem process_ofOpenProcess (P : OpenProcess.{u, v, w, w'} m Party Δ) (S : Type w) :
    (ofOpenProcess P S).process = P := rfl

@[simp]
theorem envAction_ofOpenProcess (P : OpenProcess.{u, v, w, w'} m Party Δ) (S : Type w) :
    (ofOpenProcess P S).envAction = EnvAction.empty S := rfl

/--
Wrap an `OpenProcess` with the passive alphabet: every event leaves the
state unchanged.

Useful when a process needs to participate in a non-trivial alphabet
(so its env-channel slot must be inhabited at the chosen `Event` /
`State` types) but its own state is unaffected by every event.
-/
@[expose]
def passive (P : OpenProcess.{u, v, w, w'} m Party Δ) (Event : Type uE) (S : Type w) :
    EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event S where
  process := P
  envAction := EnvAction.passive Event S

@[simp]
theorem process_passive (P : OpenProcess.{u, v, w, w'} m Party Δ) (Event : Type uE) (S : Type w) :
    (passive P Event S).process = P := rfl

@[simp]
theorem envAction_passive (P : OpenProcess.{u, v, w, w'} m Party Δ) (Event : Type uE) (S : Type w) :
    (passive P Event S).envAction = EnvAction.passive Event S := rfl

@[simp]
theorem react_passive (P : OpenProcess.{u, v, w, w'} m Party Δ) (Event : Type uE) (S : Type w)
    (e : Event) (s : S) :
    (passive P Event S).react e s = pure s := rfl

/-! ## Alphabet and env-action adaptation -/

/--
Adapt the env alphabet along an event embedding `g : Event → Event'`.

The new wrapper accepts events of type `Event`; each such event `e` is
routed through `g` to obtain `g e : Event'` and passed to the original
env action. This is the contravariant action on the alphabet that lets
coarser alphabets be embedded into finer ones (e.g. lift a
`MomentaryCorruption.Alphabet` into a richer alphabet that also
tracks broadcast events).

The underlying open process is unchanged.
-/
@[expose]
def comapEvent {Event' : Type uE} (g : Event → Event')
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event' State) :
    EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State where
  process := E.process
  envAction := E.envAction.comap g

@[simp]
theorem process_comapEvent {Event' : Type uE} (g : Event → Event')
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event' State) :
    (comapEvent g E).process = E.process := rfl

@[simp]
theorem envAction_comapEvent {Event' : Type uE} (g : Event → Event')
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event' State) :
    (comapEvent g E).envAction = E.envAction.comap g := rfl

@[simp]
theorem comapEvent_id (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State) :
    comapEvent (id : Event → Event) E = E := by
  cases E; simp [comapEvent]

@[simp]
theorem comapEvent_comapEvent {Event' Event'' : Type uE} (h : Event → Event') (g : Event' → Event'')
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event'' State) :
    comapEvent h (comapEvent g E) = comapEvent (g ∘ h) E := by
  cases E; simp [comapEvent]

/--
Replace the env action wholesale, retargeting the wrapper to a new
`(Event', State')` pair. The underlying open process is unchanged.

Used when the same open process needs to be paired with a different env
channel (e.g. lifting from the canonical `MomentaryCorruption.react`
reaction to a richer simulator-controlled reaction with its own state).
-/
@[expose]
def withEnvAction {Event' : Type uE} {State' : Type w}
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State)
    (ea : EnvAction m Event' State') :
    EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event' State' where
  process := E.process
  envAction := ea

@[simp]
theorem process_withEnvAction {Event' : Type uE} {State' : Type w}
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State)
    (ea : EnvAction m Event' State') :
    (E.withEnvAction ea).process = E.process := rfl

@[simp]
theorem envAction_withEnvAction {Event' : Type uE} {State' : Type w}
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State)
    (ea : EnvAction m Event' State') :
    (E.withEnvAction ea).envAction = ea := rfl

/-! ## Boundary adaptation -/

/--
Adapt the underlying open process along a `PortBoundary.Hom`, leaving
the env channel intact.

The boundary action of the underlying process is translated forward
(emitted packets translated, activation flags preserved) along `φ`.
The env action is independent of the port boundary, so it is carried
through unchanged. This is the env-channel-aware analogue of
`OpenProcess.mapBoundary`.
-/
@[expose]
def mapBoundary {Δ₁ Δ₂ : PortBoundary} (φ : PortBoundary.Hom Δ₁ Δ₂)
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ₁ Event State) :
    EnvOpenProcess.{u, uE, v, w, w'} m Party Δ₂ Event State where
  process := E.process.mapBoundary φ
  envAction := E.envAction

@[simp]
theorem process_mapBoundary {Δ₁ Δ₂ : PortBoundary} (φ : PortBoundary.Hom Δ₁ Δ₂)
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ₁ Event State) :
    (E.mapBoundary φ).process = E.process.mapBoundary φ := rfl

@[simp]
theorem envAction_mapBoundary {Δ₁ Δ₂ : PortBoundary} (φ : PortBoundary.Hom Δ₁ Δ₂)
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ₁ Event State) :
    (E.mapBoundary φ).envAction = E.envAction := rfl

end EnvOpenProcess

end UC
end Interaction
