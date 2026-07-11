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
* `DynSystem.System` — a dynamical system together with the standard
  verification predicates: initial states, ambient assumptions, safety, and
  invariants.
* `DynSystem.DirRel` — a relation between single transitions of two systems,
  the generic step-matching interface consumed by refinement and bisimulation.

Instantiating `p` recovers the corresponding bundles for the concrete system
notions built on `DynSystem`, such as concurrent machines and processes.
-/

@[expose] public section

universe u u₁ u₂ uA uB uA₂ uB₂ w

namespace PFunctor

namespace DynSystem

variable {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}

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
structure Labeled (p : PFunctor.{uA, uB}) where
  /-- The set of states of the underlying system. -/
  State : Type u
  /-- The underlying dynamical system being labeled. -/
  toDynSystem : DynSystem State p
  /-- The type of observable external event labels. -/
  Event : Type w
  /-- The assignment of an event label to each transition. -/
  event : toDynSystem.EventMap Event

/-- A dynamical system equipped with a stable ticket for each transition. This
is the entry point for fairness and liveness statements. -/
-- The system's state/interface universes and the ticket universe (`w`) are independent.
@[nolint checkUnivs]
structure Ticketed (p : PFunctor.{uA, uB}) where
  /-- The set of states of the underlying system. -/
  State : Type u
  /-- The underlying dynamical system being ticketed. -/
  toDynSystem : DynSystem State p
  /-- The type of stable scheduling-obligation identifiers. -/
  Ticket : Type w
  /-- The assignment of a ticket to each transition. -/
  ticket : toDynSystem.Tickets Ticket

/-- A dynamical system together with the standard verification predicates:
initial states, ambient assumptions, safety, and invariants.

These predicates are orthogonal to the dynamics themselves, so they are kept
out of `DynSystem` and bundled only for verification-oriented statements. -/
-- The system's state universe (`u`) and interface universes are independent.
@[nolint checkUnivs]
structure System (p : PFunctor.{uA, uB}) where
  /-- The set of states of the underlying system. -/
  State : Type u
  /-- The underlying dynamical system. -/
  toDynSystem : DynSystem State p
  /-- The predicate characterizing the system's initial states. -/
  init : State → Prop
  /-- The ambient assumptions imposed on states. -/
  assumptions : State → Prop := fun _ => True
  /-- The safety predicate that states are required to satisfy. -/
  safe : State → Prop := fun _ => True
  /-- The invariant predicate maintained across transitions. -/
  inv : State → Prop := fun _ => True

namespace System

/-- The position exposed by the underlying dynamical system at each state. -/
abbrev expose (sys : System.{u} p) : sys.State → p.A := sys.toDynSystem.expose

/-- The transition of the underlying dynamical system: given a direction at the
exposed position, the next state. -/
abbrev update (sys : System.{u} p) :
    (st : sys.State) → p.B (sys.expose st) → sys.State :=
  sys.toDynSystem.update

end System

/-- A relation between one transition of `s₁` and one transition of `s₂`, at
any pair of states: the generic step-matching interface consumed by refinement
and bisimulation. -/
abbrev DirRel {S₁ : Type u₁} {S₂ : Type u₂} (s₁ : DynSystem S₁ p) (s₂ : DynSystem S₂ q) :=
  {st₁ : S₁} → {st₂ : S₂} →
    p.B (s₁.expose st₁) → q.B (s₂.expose st₂) → Prop

namespace DirRel

variable {S₁ : Type u₁} {S₂ : Type u₂} {s₁ : DynSystem S₁ p} {s₂ : DynSystem S₂ q}

/-- The permissive step relation that accepts every pair of transitions. -/
def top : DirRel s₁ s₂ := fun _ _ => True

/-- Reverse a step-matching relation by flipping its two arguments. -/
def reverse (rel : DirRel s₁ s₂) : DirRel s₂ s₁ := fun d₂ d₁ => rel d₁ d₂

/-- Conjunction of step-matching relations. -/
def inter (first second : DirRel s₁ s₂) : DirRel s₁ s₂ :=
  fun d₁ d₂ => first d₁ d₂ ∧ second d₁ d₂

/-- The synchronized step relation between two systems over a shared interface:
the two states expose equal positions and the chosen directions agree up to
transport along that equality. This is the step-matching relation at which a
step-synchronized simulation (`DynSystem.IsSimulation`) is a forward
simulation. -/
def sync (t₁ : DynSystem S₁ p) (t₂ : DynSystem S₂ p) : DirRel t₁ t₂ :=
  fun {st₁} {st₂} d₁ d₂ => t₁.expose st₁ = t₂.expose st₂ ∧ HEq d₁ d₂

end DirRel

end DynSystem

end PFunctor
