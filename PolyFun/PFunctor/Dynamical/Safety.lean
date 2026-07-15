/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Basic
import Batteries.Tactic.Lint

/-!
# Labels, tickets, and verification predicates for dynamical systems

Comparison-oriented metadata attached to the transitions of a `p`-dynamical
system, kept out of `DynSystem` itself so the core dynamics stay minimal:

* `DynSystem.EventMap` / `DynSystem.Labeled` — a stable external label for each
  transition (state and direction), the observable step descriptions one wants
  to preserve under refinement or compare across runs.
* `DynSystem.Tickets` / `DynSystem.Ticketed` — a stable obligation identifier
  for each transition, the handles that fairness and liveness layers quantify
  over instead of the state-dependent direction types themselves.
* `DynSystem.SafetySpec` — a dynamical system together with an initial-state
  predicate, ambient assumptions, and a safety predicate.
Concrete steps and their relations live with the operational core in
`PFunctor.Dynamical.Basic` as `DynSystem.Step` and `DynSystem.StepRel`.

Instantiating `p` recovers the corresponding bundles for the concrete system
notions built on `DynSystem`, such as concurrent machines and processes.
-/

@[expose] public section

universe u uA uB w

namespace PFunctor

namespace DynSystem

variable {p : PFunctor.{uA, uB}}

/-- A stable external label for each transition of a dynamical system: at each
state, an assignment of an `Event` to every direction at the exposed position. -/
abbrev EventMap {S : Type u} (s : DynSystem S p) (Event : Type w) :=
  (st : S) → p.B (s.expose st) → Event

/-- A stable obligation identifier for each transition of a dynamical system.

Unlike the direction itself, a ticket is meant to persist across different
representations of the same scheduling obligation, so fairness and liveness
layers quantify over tickets rather than over the direction type of one
particular state. -/
abbrev Tickets {S : Type u} (s : DynSystem S p) (Ticket : Type w) :=
  (st : S) → p.B (s.expose st) → Ticket

/-- A dynamical system equipped with a stable external event label for each
transition. This is the smallest bundle supporting statements about observable
event traces. -/
-- The system's state/interface universes and the event-label universe (`w`) are independent.
@[nolint checkUnivs]
structure Labeled (p : PFunctor.{uA, uB}) extends Machine.{u} p where
  /-- The type of observable external event labels. -/
  Event : Type w
  /-- The assignment of an event label to each transition. -/
  event : toMachine.toDynSystem.EventMap Event

/-- A dynamical system equipped with a stable ticket for each transition. This
is the entry point for fairness and liveness statements. -/
-- The system's state/interface universes and the ticket universe (`w`) are independent.
@[nolint checkUnivs]
structure Ticketed (p : PFunctor.{uA, uB}) extends Machine.{u} p where
  /-- The type of stable scheduling-obligation identifiers. -/
  Ticket : Type w
  /-- The assignment of a ticket to each transition. -/
  ticket : toMachine.toDynSystem.Tickets Ticket

/-- A safety-verification problem: dynamics together with initial states,
ambient assumptions, and the state predicate to be established.

These predicates are orthogonal to the dynamics themselves, so they are kept
out of `DynSystem` and bundled only for verification-oriented statements. -/
-- The system's state universe (`u`) and interface universes are independent.
@[nolint checkUnivs]
structure SafetySpec (p : PFunctor.{uA, uB}) extends Machine.{u} p where
  /-- The predicate characterizing the system's initial states. -/
  init : State → Prop
  /-- The ambient assumptions imposed on states. -/
  assumptions : State → Prop := fun _ => True
  /-- The safety predicate that states are required to satisfy. -/
  safe : State → Prop := fun _ => True
end DynSystem

end PFunctor
