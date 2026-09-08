/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

/-!
# Per-party snapshot projections

`SnapshotLeakable` supplies a function from a state and party to an observation.
It is independent of `CorruptionModel` and `EnvAction`: a consumer chooses when
to invoke the projection and how to make its result observable in an execution.

The class contains only the projection function. Constant projections are
valid inhabitants. Its presence or absence establishes no security property,
and it imposes no simulator-consistency or equivocability condition. Those
properties require explicit statements and proofs in the consuming semantics.

No default instance is provided; each consumer selects its projection. CJSV22,
*Universally Composable End-to-End Secure Messaging*, is a motivating use of
state observations at compromise time; see `REFERENCES.md`.
-/

public section

universe u

namespace Interaction
namespace UC

/--
A per-party projection `State → Party → Leakage`.

The party type is arbitrary; session/party pairs are one possible choice.
`Leakage` is an `outParam`, so instance synthesis can infer the output type
from an instance selected for `State` and `Party`. This is an inference
convention, not a proof of uniqueness of the projection or its output type.

Consumers determine when the projection is evaluated and state any required
laws about the resulting observations.
-/
class SnapshotLeakable
    {Party : Type u} (State : Type) (Leakage : outParam Type) where
  /-- Project an observation from the supplied state for a party. -/
  leak : State → Party → Leakage

end UC
end Interaction
