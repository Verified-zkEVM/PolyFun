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
* `DynSystem.DirRel` — a relation between single transitions of two systems,
  the generic step-matching interface consumed by refinement.

Instantiating `p` recovers the corresponding bundles for the concrete system
notions built on `DynSystem`, such as concurrent machines and processes.
-/

@[expose] public section

universe u u₁ u₂ u₃ uA uB uA₂ uB₂ uA₃ uB₃ w

namespace PFunctor

namespace DynSystem

variable {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}

/-- A stable external label for each transition of a dynamical system: at each
state, an assignment of an `Event` to every direction at the exposed position. -/
abbrev EventMap (s : DynSystem.{u} p) (Event : Type w) :=
  (st : s.State) → p.B (s.expose st) → Event

/-- A stable obligation identifier for each transition of a dynamical system.

Unlike the direction itself, a ticket is meant to persist across different
representations of the same scheduling obligation, so fairness and liveness
layers quantify over tickets rather than over the direction type of one
particular state. -/
abbrev Tickets (s : DynSystem.{u} p) (Ticket : Type w) :=
  (st : s.State) → p.B (s.expose st) → Ticket

/-- A dynamical system equipped with a stable external event label for each
transition. This is the smallest bundle supporting statements about observable
event traces. -/
-- The system's state/interface universes and the event-label universe (`w`) are independent.
@[nolint checkUnivs]
structure Labeled (p : PFunctor.{uA, uB}) where
  /-- The underlying dynamical system being labeled. -/
  toDynSystem : DynSystem.{u} p
  /-- The type of observable external event labels. -/
  Event : Type w
  /-- The assignment of an event label to each transition. -/
  event : toDynSystem.EventMap Event

/-- A dynamical system equipped with a stable ticket for each transition. This
is the entry point for fairness and liveness statements. -/
-- The system's state/interface universes and the ticket universe (`w`) are independent.
@[nolint checkUnivs]
structure Ticketed (p : PFunctor.{uA, uB}) where
  /-- The underlying dynamical system being ticketed. -/
  toDynSystem : DynSystem.{u} p
  /-- The type of stable scheduling-obligation identifiers. -/
  Ticket : Type w
  /-- The assignment of a ticket to each transition. -/
  ticket : toDynSystem.Tickets Ticket

/-- A safety-verification problem: dynamics together with initial states,
ambient assumptions, and the state predicate to be established.

These predicates are orthogonal to the dynamics themselves, so they are kept
out of `DynSystem` and bundled only for verification-oriented statements. -/
-- The system's state universe (`u`) and interface universes are independent.
@[nolint checkUnivs]
structure SafetySpec (p : PFunctor.{uA, uB}) extends toDynSystem : DynSystem.{u} p where
  /-- The predicate characterizing the system's initial states. -/
  init : State → Prop
  /-- The ambient assumptions imposed on states. -/
  assumptions : State → Prop := fun _ => True
  /-- The safety predicate that states are required to satisfy. -/
  safe : State → Prop := fun _ => True

/-- A relation between one transition of `s₁` and one transition of `s₂`, at
any pair of states: the generic step-matching interface consumed by refinement. -/
abbrev DirRel (s₁ : DynSystem.{u₁} p) (s₂ : DynSystem.{u₂} q) :=
  {st₁ : s₁.State} → {st₂ : s₂.State} →
    p.B (s₁.expose st₁) → q.B (s₂.expose st₂) → Prop

namespace DirRel

variable {s₁ : DynSystem.{u₁} p} {s₂ : DynSystem.{u₂} q}

/-- Relational composition of direction matchers. The intermediate state and
direction are retained existentially because direction types depend on state. -/
def comp {r : PFunctor.{uA₃, uB₃}} {s₃ : DynSystem.{u₃} r}
    (first : DirRel s₁ s₂) (second : DirRel s₂ s₃) : DirRel s₁ s₃ :=
  fun {_} {_} d₁ d₃ =>
    ∃ st₂ : s₂.State, ∃ d₂ : q.B (s₂.expose st₂), first d₁ d₂ ∧ second d₂ d₃

/-- The permissive step relation that accepts every pair of transitions. -/
def top : DirRel s₁ s₂ := fun _ _ => True

@[simp] theorem top_apply {st₁ : s₁.State} {st₂ : s₂.State}
    (d₁ : p.B (s₁.expose st₁)) (d₂ : q.B (s₂.expose st₂)) :
    (top : DirRel s₁ s₂) d₁ d₂ := trivial

/-- Reverse a step-matching relation by flipping its two arguments. -/
def reverse (rel : DirRel s₁ s₂) : DirRel s₂ s₁ := fun d₂ d₁ => rel d₁ d₂

@[simp] theorem reverse_apply (rel : DirRel s₁ s₂) {st₁ : s₁.State} {st₂ : s₂.State}
    (d₂ : q.B (s₂.expose st₂)) (d₁ : p.B (s₁.expose st₁)) :
    reverse rel d₂ d₁ ↔ rel d₁ d₂ := Iff.rfl

/-- Conjunction of step-matching relations. -/
def inter (first second : DirRel s₁ s₂) : DirRel s₁ s₂ :=
  fun d₁ d₂ => first d₁ d₂ ∧ second d₁ d₂

@[simp] theorem inter_apply (first second : DirRel s₁ s₂)
    {st₁ : s₁.State} {st₂ : s₂.State}
    (d₁ : p.B (s₁.expose st₁)) (d₂ : q.B (s₂.expose st₂)) :
    inter first second d₁ d₂ ↔ first d₁ d₂ ∧ second d₁ d₂ := Iff.rfl

/-- The synchronized step relation between two systems over a shared interface:
the two states expose equal positions and the chosen directions agree up to
transport along that equality. This is the step-matching relation at which a
step-synchronized simulation (`DynSystem.IsSimulation`) is a forward
simulation. -/
def sync (t₁ : DynSystem.{u₁} p) (t₂ : DynSystem.{u₂} p) : DirRel t₁ t₂ :=
  fun {st₁} {st₂} d₁ d₂ => t₁.expose st₁ = t₂.expose st₂ ∧ HEq d₁ d₂

end DirRel

end DynSystem

end PFunctor
