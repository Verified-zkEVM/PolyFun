/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/
import PolyFun.Interaction.Concurrent.Process
import Batteries.Tactic.Lint

/-!
# State-indexed concurrent machines

This file provides the flat, transition-system presentation of the concurrent
interaction framework.

The semantic center of the library is `Concurrent.Process`: a residual process
state exposes one sequential interaction step, and completing that step yields
the next residual state. That continuation-based view is convenient when the
shape of the current interaction matters.

Many protocol designers, however, start from a more operational picture:

* there is an explicit global state `σ`,
* a family `Enabled σ` of events that may happen next, and
* a function describing the successor state after such an event.

`Machine` packages exactly that presentation: it is the dynamical system over
the universe polynomial `PFunctor.univ`, whose exposed position at each state
is the type of currently enabled events and whose update is the successor
state. The classical vocabulary is kept as `Machine.Enabled` / `Machine.step`
/ `Machine.mk'`, and the whole `PFunctor.DynSystem` toolkit (coalgebra
structure map, behavior, runs, labels, tickets, verification predicates)
applies to machines directly. The key bridge is `Machine.toProcess`, which
interprets each enabled event set as a one-node sequential step and thereby
embeds machine semantics into the general `Concurrent.Process` core.

This is the natural frontend for transition-system style models, including
state-heavy distributed and cryptographic protocol semantics.
-/

universe u v

namespace Interaction
namespace Concurrent

set_option linter.checkUnivs false in
/--
`Machine S` is the minimal state-indexed presentation of a concurrent system
with residual states `S`: a dynamical system over the universe polynomial. At
any residual state `σ`, the exposed position `Enabled σ` is the type of events
that may occur next, and `step σ e` is the successor state produced by choosing
the enabled event `e`.

This carrier intentionally contains only dynamics. Event labels, fairness
tickets, controller ownership, local views, and verification predicates are all
added by the generic `PFunctor.DynSystem` layers (`DynSystem.Labeled`,
`DynSystem.Ticketed`, `Machine.SafetySpec`, …) so that the core transition
semantics stays small and reusable.
-/
-- The state universe (`v`) and the enabled-event universe (`u`) are independent.
abbrev Machine (S : Type v) := PFunctor.DynSystem S PFunctor.univ.{u}

namespace Machine

/-- The events enabled at a given residual state: the machine's exposed
position, read as a type. -/
abbrev Enabled {S : Type v} (machine : Machine.{u, v} S) (σ : S) : Type u :=
  machine.expose σ

/-- The successor state produced by choosing an enabled event at a state: the
machine's transition function. -/
abbrev step {S : Type v} (machine : Machine.{u, v} S) (σ : S)
    (e : machine.Enabled σ) : S :=
  machine.update σ e

/-- Build a machine from its state set, enabled-event family, and successor
function, using the classical field names. -/
def mk' (State : Type v) (Enabled : State → Type u)
    (step : (σ : State) → Enabled σ → State) : Machine.{u, v} State :=
  Enabled ⇆ step

@[simp] theorem enabled_mk' (State : Type v) (Enabled : State → Type u)
    (step : (σ : State) → Enabled σ → State) :
    (mk' State Enabled step).Enabled = Enabled := rfl

@[simp] theorem step_mk' (State : Type v) (Enabled : State → Type u)
    (step : (σ : State) → Enabled σ → State) :
    (mk' State Enabled step).step = step := rfl

set_option linter.checkUnivs false in
/--
`Machine.SafetySpec` is a machine-level safety-verification problem: dynamics,
initial states, ambient assumptions, and the safety predicate.
-/
-- The machine's state universe (`v`) and event universe (`u`) are independent.
abbrev SafetySpec := PFunctor.DynSystem.SafetySpec.{v} PFunctor.univ.{u}

/--
Compile a flat state-indexed machine into the continuation-based
`Concurrent.Process` core.

At each machine state `σ`, the current enabled event type `Enabled σ` is turned
into a one-node sequential interaction step. The supplied `semantics` equips
that node with controller and local-view information, so the result is not just
an operational embedding of the state transition relation, but a full process
step inside the richer interaction semantics.

`Machine.toProcess` is therefore the canonical bridge from transition-system
models to the more general process-centered concurrent layer.
-/
def toProcess {Party : Type u} {S : Type v} (machine : Machine S)
    (semantics : (σ : S) → NodeProfile Party (machine.Enabled σ)) :
    Process S Party :=
  ProcessOver.ofStep S fun σ =>
    { spec := .node (machine.Enabled σ) (fun _ => .done)
      semantics := ⟨semantics σ, fun _ => PUnit.unit⟩
      next := fun
        | ⟨event, _⟩ => machine.step σ event }

/--
Lift `Machine.toProcess` from bare dynamics to `Process.SafetySpec` by reusing
the same initial-state, assumption, and safety predicates.
-/
def SafetySpec.toProcess {Party : Type u} (system : Machine.SafetySpec)
    (semantics : (σ : system.State) →
      NodeProfile Party (system.toDynSystem.expose σ)) :
    Process.SafetySpec Party :=
  { system with toMachine :=
      { system.toMachine with
        toDynSystem := Machine.toProcess system.toDynSystem semantics } }

end Machine
end Concurrent
end Interaction
