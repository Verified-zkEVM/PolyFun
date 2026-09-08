/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.UC.EnvOpenProcess

/-!
# Corruption models as bundled environment alphabets

`CorruptionModel m` bundles an event alphabet, a bookkeeping state, and an
`EnvAction m Event State` describing the per-event reaction. Models are explicit
values, so a construction can select a model or take one as an argument.
`MomentaryCorruption.model M m` is a concrete example in
`PolyFun/Interaction/UC/MomentaryCorruption.lean`.

`CorruptionModel.Process` specializes `EnvOpenProcess` to a model's event and
state types. A value of that type still supplies its own reaction; the
abbreviation does not require it to equal the model's `envAction`.

Consumers supply restrictions on event histories, connect reactions to process
execution, and interpret observations. `SnapshotLeakable` in
`PolyFun/Interaction/UC/Leakage.lean` provides a separate projection interface.
The bundle contains no leakage or security law. Consumers that need decidable
event equality can require `[DecidableEq M.Event]` at their use site.
-/

public section

universe u v w'

namespace Interaction
namespace UC

/--
An event alphabet, bookkeeping state, and per-event reaction.
A concrete model may key its events and state by an identity type, as
`MomentaryCorruption.model` does; the bundle itself leaves these types arbitrary.
-/
structure CorruptionModel (m : Type → Type w') [Pure m] where
  /-- The event alphabet recognised by the model. -/
  Event : Type
  /-- The bookkeeping state carried between events. -/
  State : Type
  /-- The per-event reaction updating `State` on each `Event`. -/
  envAction : EnvAction m Event State

namespace CorruptionModel

/--
Open processes paired with a reaction on the event and state types of `M`.
The reaction is a field of each `EnvOpenProcess` value; this abbreviation fixes
its types but does not constrain it to equal `M.envAction`.

`Party : Type u` and the process-state universe `v` remain arbitrary. The move
space and environment state live in `Type 0`, matching the input universe of
`m`. For `MomentaryCorruption.model M m`, the usual party type is `M` and the
event type is `MomentaryCorruption.Alphabet M`.
-/
abbrev Process {m : Type → Type w'} [Pure m] (M : CorruptionModel m) (Party : Type u)
    (Δ : PortBoundary) :=
  EnvOpenProcess.{u, 0, v, 0, w'} m Party Δ M.Event M.State

end CorruptionModel

end UC
end Interaction
