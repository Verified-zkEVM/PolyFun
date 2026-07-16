/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Concurrent.Execution
import PolyFun.PFunctor.Dynamical.Run

/-!
# Finite prefixes and infinite runs of dynamic concurrent processes

This file extends finite executions in the two directions needed for semantic
reasoning about ongoing concurrent behavior.

* `ProcessOver.Prefix` is the right notion of a finite initial segment of an
  execution. Unlike `ProcessOver.Trace`, it may stop at any residual process
  state, not only at a quiescent one.
* `ProcessOver.Run` is an infinite execution, represented by the residual
  process state at each time index together with the complete path chosen
  for the corresponding process step.

The closed-world `Process` API is recovered as a specialization of these
generic definitions.
-/

universe u v w w₂ w₃

namespace Interaction
namespace Concurrent
namespace ProcessOver

/--
`Prefix process p n` is a finite prefix of length `n` of an execution starting
from the residual process state `p`: the dynamical-system `Prefix` at the step
polynomial, where each `step` records one complete sequential path of the
current process step.

Unlike `ProcessOver.Trace`, a `Prefix` may stop at any residual state. This
makes it the correct finite prefix object for later infinite-run semantics.
-/
abbrev Prefix
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} (process : ProcessOver P Γ) :
    process.Proc → Nat → Sort _ :=
  PFunctor.DynSystem.Prefix process

namespace Prefix

/--
The sequence of current controlling parties exposed by a finite prefix after
projecting the generic context into `StepContext`.
-/
def currentControllers
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party)) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List (Option Party)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      ((process.step p).mapContext resolve).currentController? tr :: currentControllers resolve tail

/--
The sequence of full controller paths exposed by a finite prefix after
projecting the generic context into `StepContext`.
-/
def controllerPaths
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party)) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List (List Party)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      ((process.step p).mapContext resolve).controllerPath tr :: controllerPaths resolve tail

/-- The stable event labels attached to the executed steps of a finite prefix. -/
abbrev events
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List Event :=
  PFunctor.DynSystem.Prefix.events eventMap

/-- The stable tickets attached to the executed steps of a finite prefix. -/
abbrev tickets
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List Ticket :=
  PFunctor.DynSystem.Prefix.tickets ticketMap

/--
Forget the quiescence proof of a finite `Trace` and keep only its executed
prefix.
-/
def ofTrace
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ} :
    {p : process.Proc} → (trace : Trace process p) → Prefix process p trace.length
  | _, .done _ => .nil
  | _, .step tr tail => .step tr (ofTrace tail)

@[simp, grind =]
theorem currentControllers_nil
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    {p : process.Proc} :
    currentControllers resolve (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem controllerPaths_nil
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    {p : process.Proc} :
    controllerPaths resolve (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem events_nil
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    {p : process.Proc} :
    events eventMap (.nil : Prefix process p 0) = [] :=
  PFunctor.DynSystem.Prefix.events_nil eventMap

@[simp, grind =]
theorem tickets_nil
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    {p : process.Proc} :
    tickets ticketMap (.nil : Prefix process p 0) = [] :=
  PFunctor.DynSystem.Prefix.tickets_nil ticketMap

end Prefix

/--
`Run process` is an infinite execution of the dynamic process `process`: the
dynamical-system `Run` at the step polynomial.

It is represented by:

* `state n`, the residual process state after `n` complete process steps;
* `path n` (the generic `dir` field), the concrete path chosen for
  step `n`;
* `next_state`, which states that the residual state stream follows the
  process continuation exactly.

This is a continuation-based infinite semantics: the run does not introduce a
new operational state space of its own. It simply records how the residual
process state evolves when one complete process step is chosen at each time.
-/
abbrev Run
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} (process : ProcessOver P Γ) :=
  PFunctor.DynSystem.Run process

namespace Run

/-- The concrete path chosen for step `n`: the run's generic direction
choice, read at the step-polynomial interface. -/
abbrev path
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    (run : Run process) (n : Nat) : (process.step (run.state n)).tree.Path :=
  run.dir n

/-- The initial residual process state of a run. -/
abbrev initial
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    (run : Run process) : process.Proc :=
  PFunctor.DynSystem.Run.initial run

/--
The first complete process-step path of the run.
-/
abbrev head
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    (run : Run process) : (process.step run.initial).tree.Path :=
  PFunctor.DynSystem.Run.head run

/--
The tail of a run after its first process step.
-/
abbrev tail
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    (run : Run process) :
    Run process :=
  PFunctor.DynSystem.Run.tail run

/--
The initial state of `run.tail` is exactly the residual state obtained by
executing `run.head`.
-/
theorem tail_initial
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    (run : Run process) :
    run.tail.initial = (process.step run.initial).next run.head :=
  PFunctor.DynSystem.Run.tail_initial run

/--
`take run n` is the length-`n` finite execution prefix of the infinite run
`run`.
-/
abbrev take
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    (run : Run process) : (n : Nat) → Prefix process run.initial n :=
  PFunctor.DynSystem.Run.take run

/--
The current controlling party of step `n` of a run, if any, after projecting
the generic context into `StepContext`.
-/
def currentController?
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    (run : Run process) (n : Nat) : Option Party :=
  ((process.step (run.state n)).mapContext resolve).currentController? (run.path n)

/-- The current controlling parties exposed along the first `n` executed steps
of the run `run`. -/
def currentControllersUpTo
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    (run : Run process) : Nat → List (Option Party)
  | 0 => []
  | n + 1 => run.currentController? resolve 0 :: run.tail.currentControllersUpTo resolve n

/--
The full controller path recorded by step `n` of a run after projecting the
generic context into `StepContext`.
-/
def controllerPath
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    (run : Run process) (n : Nat) : List Party :=
  ((process.step (run.state n)).mapContext resolve).controllerPath (run.path n)

/-- The full controller paths exposed along the first `n` executed steps of the
run `run`. -/
def controllerPathsUpTo
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    (run : Run process) : Nat → List (List Party)
  | 0 => []
  | n + 1 => run.controllerPath resolve 0 :: run.tail.controllerPathsUpTo resolve n

/-- The stable event label attached to step `n` of a run. -/
abbrev event
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    (run : Run process) (n : Nat) : Event :=
  PFunctor.DynSystem.Run.event eventMap run n

/-- The stable event labels attached to the first `n` executed steps of the run
`run`. -/
abbrev eventsUpTo
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    (run : Run process) : Nat → List Event :=
  PFunctor.DynSystem.Run.eventsUpTo eventMap run

/-- The stable ticket attached to step `n` of a run. -/
abbrev ticket
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    (run : Run process) (n : Nat) : Ticket :=
  PFunctor.DynSystem.Run.ticket ticketMap run n

/-- The stable tickets attached to the first `n` executed steps of the run
`run`. -/
abbrev ticketsUpTo
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    (run : Run process) : Nat → List Ticket :=
  PFunctor.DynSystem.Run.ticketsUpTo ticketMap run

/--
`RelUpTo rel left right n` states that the first `n` executed steps of the
runs `left` and `right` match step-by-step according to `rel`.
-/
abbrev RelUpTo
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Δ : Interaction.TypeTree.Node.Context.{w, w₃}}
    {P₁ : Type v} {left : ProcessOver P₁ Γ}
    {P₂ : Type v} {right : ProcessOver P₂ Δ}
    (rel : ProcessOver.StepRel left right)
    (leftRun : Run left) (rightRun : Run right) : Nat → Prop :=
  PFunctor.DynSystem.Run.RelUpTo rel leftRun rightRun

/--
`Rel rel left right` states that every finite prefix of the runs `left` and
`right` matches according to `rel`.
-/
abbrev Rel
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Δ : Interaction.TypeTree.Node.Context.{w, w₃}}
    {P₁ : Type v} {left : ProcessOver P₁ Γ}
    {P₂ : Type v} {right : ProcessOver P₂ Δ}
    (rel : ProcessOver.StepRel left right)
    (leftRun : Run left) (rightRun : Run right) : Prop :=
  PFunctor.DynSystem.Run.Rel rel leftRun rightRun

/-- Pointwise step matching implies prefix matching of the first `n` steps. -/
theorem relUpTo_of_pointwise
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Δ : Interaction.TypeTree.Node.Context.{w, w₃}}
    {P₁ : Type v} {left : ProcessOver P₁ Γ}
    {P₂ : Type v} {right : ProcessOver P₂ Δ}
    (rel : ProcessOver.StepRel left right)
    (leftRun : Run left) (rightRun : Run right)
    (hrel : ∀ n, rel ⟨leftRun.state n, leftRun.path n⟩
      ⟨rightRun.state n, rightRun.path n⟩) :
    ∀ n, RelUpTo rel leftRun rightRun n :=
  PFunctor.DynSystem.Run.relUpTo_of_pointwise rel leftRun rightRun hrel

/-- Pointwise step matching implies full run matching. -/
theorem rel_of_pointwise
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Δ : Interaction.TypeTree.Node.Context.{w, w₃}}
    {P₁ : Type v} {left : ProcessOver P₁ Γ}
    {P₂ : Type v} {right : ProcessOver P₂ Δ}
    (rel : ProcessOver.StepRel left right)
    (leftRun : Run left) (rightRun : Run right)
    (hrel : ∀ n, rel ⟨leftRun.state n, leftRun.path n⟩
      ⟨rightRun.state n, rightRun.path n⟩) :
    Rel rel leftRun rightRun :=
  PFunctor.DynSystem.Run.rel_of_pointwise rel leftRun rightRun hrel

@[simp, grind =]
theorem take_zero
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    (run : Run process) :
    run.take 0 = .nil := rfl

@[simp, grind =]
theorem take_succ
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    (run : Run process) (n : Nat) :
    run.take (n + 1) =
      PFunctor.DynSystem.Prefix.step run.head
        (PFunctor.DynSystem.Run.tail_initial run ▸ run.tail.take n) := rfl

@[simp, grind =]
theorem currentControllersUpTo_zero
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    (run : Run process) :
    run.currentControllersUpTo resolve 0 = [] := rfl

@[simp, grind =]
theorem controllerPathsUpTo_zero
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    (run : Run process) :
    run.controllerPathsUpTo resolve 0 = [] := rfl

@[simp, grind =]
theorem eventsUpTo_zero
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    (run : Run process) :
    run.eventsUpTo eventMap 0 = [] := rfl

@[simp, grind =]
theorem ticketsUpTo_zero
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    (run : Run process) :
    run.ticketsUpTo ticketMap 0 = [] := rfl

@[simp, grind =]
theorem currentControllersUpTo_succ
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    (run : Run process) (n : Nat) :
    run.currentControllersUpTo resolve (n + 1) =
      run.currentController? resolve 0 :: run.tail.currentControllersUpTo resolve n := rfl

@[simp, grind =]
theorem controllerPathsUpTo_succ
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    (run : Run process) (n : Nat) :
    run.controllerPathsUpTo resolve (n + 1) =
      run.controllerPath resolve 0 :: run.tail.controllerPathsUpTo resolve n := rfl

@[simp, grind =]
theorem eventsUpTo_succ
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    (run : Run process) (n : Nat) :
    run.eventsUpTo eventMap (n + 1) =
      run.event eventMap 0 :: run.tail.eventsUpTo eventMap n := rfl

@[simp, grind =]
theorem ticketsUpTo_succ
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    (run : Run process) (n : Nat) :
    run.ticketsUpTo ticketMap (n + 1) =
      run.ticket ticketMap 0 :: run.tail.ticketsUpTo ticketMap n := rfl

end Run

end ProcessOver

namespace Process

/-- The closed-world specialization of `ProcessOver.Prefix`. -/
abbrev Prefix {Party : Type u} {P : Type v} (process : Process P Party) :=
  ProcessOver.Prefix process

namespace Prefix

/-- The sequence of current controlling parties exposed by a finite closed-world
prefix. -/
def currentControllers {Party : Type u} {P : Type v} {process : Process P Party} :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List (Option Party)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      (process.step p).currentController? tr :: currentControllers tail

/-- The sequence of full controller paths exposed by a finite closed-world
prefix. -/
def controllerPaths {Party : Type u} {P : Type v} {process : Process P Party} :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List (List Party)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      (process.step p).controllerPath tr :: controllerPaths tail

/-- The stable event labels attached to the executed steps of a finite
closed-world prefix. -/
abbrev events {Party : Type u} {P : Type v} {process : Process P Party} {Event : Type w₃}
    (eventMap : process.EventMap Event) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List Event :=
  ProcessOver.Prefix.events eventMap

/-- The stable tickets attached to the executed steps of a finite closed-world
prefix. -/
abbrev tickets {Party : Type u} {P : Type v} {process : Process P Party} {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List Ticket :=
  ProcessOver.Prefix.tickets ticketMap

/-- Forget the quiescence proof of a finite closed-world trace and keep only
its executed prefix. -/
abbrev ofTrace {Party : Type u} {P : Type v} {process : Process P Party} :
    {p : process.Proc} → (trace : Trace process p) → Prefix process p trace.length :=
  ProcessOver.Prefix.ofTrace

@[simp, grind =]
theorem currentControllers_nil {Party : Type u} {P : Type v} {process : Process P Party}
    {p : process.Proc} :
    currentControllers (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem controllerPaths_nil {Party : Type u} {P : Type v} {process : Process P Party}
    {p : process.Proc} :
    controllerPaths (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem events_nil {Party : Type u} {P : Type v} {process : Process P Party}
    {Event : Type w₃} (eventMap : process.EventMap Event)
    {p : process.Proc} :
    events eventMap (.nil : Prefix process p 0) = [] :=
  ProcessOver.Prefix.events_nil eventMap

@[simp, grind =]
theorem tickets_nil {Party : Type u} {P : Type v} {process : Process P Party}
    {Ticket : Type w₃} (ticketMap : process.Tickets Ticket)
    {p : process.Proc} :
    tickets ticketMap (.nil : Prefix process p 0) = [] :=
  ProcessOver.Prefix.tickets_nil ticketMap

end Prefix

/-- The closed-world specialization of `ProcessOver.Run`. -/
abbrev Run {Party : Type u} {P : Type v} (process : Process P Party) :=
  ProcessOver.Run process

namespace Run

/-- The initial residual process state of a closed-world run. -/
abbrev initial {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) : process.Proc :=
  ProcessOver.Run.initial run

/-- The first complete process-step path of a closed-world run. -/
abbrev head {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) : (process.step run.initial).tree.Path :=
  ProcessOver.Run.head run

/-- The tail of a closed-world run after its first process step. -/
abbrev tail {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) :
    Run process :=
  ProcessOver.Run.tail run

theorem tail_initial {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) :
    run.tail.initial = (process.step run.initial).next run.head :=
  ProcessOver.Run.tail_initial run

/-- The length-`n` finite prefix of a closed-world run. -/
abbrev take {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) : (n : Nat) → Prefix process run.initial n :=
  ProcessOver.Run.take run

/-- The current controlling party of step `n` of a closed-world run, if any. -/
def currentController? {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) (n : Nat) : Option Party :=
  (process.step (run.state n)).currentController? (run.path n)

/-- The current controlling parties exposed along the first `n` executed steps
of a closed-world run. -/
def currentControllersUpTo {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) : Nat → List (Option Party)
  | 0 => []
  | n + 1 => run.currentController? 0 :: run.tail.currentControllersUpTo n

/-- The full controller path recorded by step `n` of a closed-world run. -/
def controllerPath {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) (n : Nat) : List Party :=
  (process.step (run.state n)).controllerPath (run.path n)

/-- The full controller paths exposed along the first `n` executed steps of a
closed-world run. -/
def controllerPathsUpTo {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) : Nat → List (List Party)
  | 0 => []
  | n + 1 => run.controllerPath 0 :: run.tail.controllerPathsUpTo n

/-- The stable event label attached to step `n` of a closed-world run. -/
abbrev event {Party : Type u} {P : Type v} {process : Process P Party}
    {Event : Type w₃} (eventMap : process.EventMap Event)
    (run : Run process) (n : Nat) : Event :=
  ProcessOver.Run.event eventMap run n

/-- The stable event labels attached to the first `n` executed steps of a
closed-world run. -/
abbrev eventsUpTo {Party : Type u} {P : Type v} {process : Process P Party}
    {Event : Type w₃} (eventMap : process.EventMap Event)
    (run : Run process) : Nat → List Event :=
  ProcessOver.Run.eventsUpTo eventMap run

/-- The stable ticket attached to step `n` of a closed-world run. -/
abbrev ticket {Party : Type u} {P : Type v} {process : Process P Party}
    {Ticket : Type w₃} (ticketMap : process.Tickets Ticket)
    (run : Run process) (n : Nat) : Ticket :=
  ProcessOver.Run.ticket ticketMap run n

/-- The stable tickets attached to the first `n` executed steps of a
closed-world run. -/
abbrev ticketsUpTo {Party : Type u} {P : Type v} {process : Process P Party}
    {Ticket : Type w₃} (ticketMap : process.Tickets Ticket)
    (run : Run process) : Nat → List Ticket :=
  ProcessOver.Run.ticketsUpTo ticketMap run

@[simp, grind =]
theorem take_zero {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) :
    run.take 0 = .nil :=
  ProcessOver.Run.take_zero run

@[simp, grind =]
theorem take_succ {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) (n : Nat) :
    run.take (n + 1) =
      PFunctor.DynSystem.Prefix.step run.head
        (PFunctor.DynSystem.Run.tail_initial run ▸ run.tail.take n) :=
  ProcessOver.Run.take_succ run n

@[simp, grind =]
theorem currentControllersUpTo_zero {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) :
    run.currentControllersUpTo 0 = [] := rfl

@[simp, grind =]
theorem controllerPathsUpTo_zero {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) :
    run.controllerPathsUpTo 0 = [] := rfl

@[simp, grind =]
theorem eventsUpTo_zero {Party : Type u} {P : Type v} {process : Process P Party}
    {Event : Type w₃} (eventMap : process.EventMap Event)
    (run : Run process) :
    run.eventsUpTo eventMap 0 = [] :=
  ProcessOver.Run.eventsUpTo_zero eventMap run

@[simp, grind =]
theorem ticketsUpTo_zero {Party : Type u} {P : Type v} {process : Process P Party}
    {Ticket : Type w₃} (ticketMap : process.Tickets Ticket)
    (run : Run process) :
    run.ticketsUpTo ticketMap 0 = [] :=
  ProcessOver.Run.ticketsUpTo_zero ticketMap run

@[simp, grind =]
theorem currentControllersUpTo_succ {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) (n : Nat) :
    run.currentControllersUpTo (n + 1) =
      run.currentController? 0 :: run.tail.currentControllersUpTo n := rfl

@[simp, grind =]
theorem controllerPathsUpTo_succ {Party : Type u} {P : Type v} {process : Process P Party}
    (run : Run process) (n : Nat) :
    run.controllerPathsUpTo (n + 1) =
      run.controllerPath 0 :: run.tail.controllerPathsUpTo n := rfl

@[simp, grind =]
theorem eventsUpTo_succ {Party : Type u} {P : Type v} {process : Process P Party}
    {Event : Type w₃} (eventMap : process.EventMap Event)
    (run : Run process) (n : Nat) :
    run.eventsUpTo eventMap (n + 1) =
      run.event eventMap 0 :: run.tail.eventsUpTo eventMap n :=
  ProcessOver.Run.eventsUpTo_succ eventMap run n

@[simp, grind =]
theorem ticketsUpTo_succ {Party : Type u} {P : Type v} {process : Process P Party}
    {Ticket : Type w₃} (ticketMap : process.Tickets Ticket)
    (run : Run process) (n : Nat) :
    run.ticketsUpTo ticketMap (n + 1) =
      run.ticket ticketMap 0 :: run.tail.ticketsUpTo ticketMap n :=
  ProcessOver.Run.ticketsUpTo_succ ticketMap run n

end Run

end Process
end Concurrent
end Interaction
