/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Concurrent.Process

/-!
# Finite executions of dynamic concurrent processes

This file explains what it means to execute a `Concurrent.ProcessOver` for
finitely many steps.

The important point is that one process step is itself a finite sequential
interaction episode. So a finite concurrent execution is not just a list of
atomic labels: at each residual state we record one complete sequential
path of the current step, then continue from the residual process state
selected by that path.

This file therefore provides two parallel views of finite execution:

* `ProcessOver.Trace`, the exact global execution history for any realized
  node context; and
* `Step.Observed` / `ProcessOver.ObservedTrace`, the local observations that
  one fixed party extracts from that history once the node context is
  projected into `StepContext`.

The closed-world `Process` API is recovered as a specialization of these
generic definitions.
-/

universe u v w w₂ w₃

namespace Interaction
namespace Concurrent

namespace Step

/--
`Observed me semantics tr` is the exact typed sequence of local observations
available to the fixed party `me` during one sequential step.

More concretely, suppose the current process step executes along path
`tr`. At each visited node of that path, the step semantics determines
what `me` is allowed to observe there, and `Observed` records exactly that
piece of local information before continuing to the next node.

So `Observed` is the step-local projection of the global path: it forgets
everything that `me` is not entitled to see, while preserving the exact local
observation type at every node.
-/
inductive Observed {Party : Type u} [DecidableEq Party] (me : Party) :
    {spec : Interaction.TypeTree.{w}} →
      PFunctor.FreeM.Displayed.Decoration (P := TypeTree.basePFunctor)
        (α := PUnit.{w + 1}) (StepContext Party) spec →
      PFunctor.FreeM.Path spec →
      Sort _ where
  | /-- The unique observed path of a completed sequential step. -/
    done :
      Observed (Party := Party) me (spec := .done) PUnit.unit PUnit.unit
  | /-- Extend an observed path by the local observation available at
    the current node. -/
    step
      {Moves : Type w}
      {rest : Moves → Interaction.TypeTree.{w}}
      {node : NodeProfile Party Moves}
      {semantics : (x : Moves) →
        PFunctor.FreeM.Displayed.Decoration (P := TypeTree.basePFunctor)
          (α := PUnit.{w + 1}) (StepContext Party) (rest x)}
      {x : Moves}
      {tail : PFunctor.FreeM.Path (rest x)}
      (obs : (node.views me).ObsType)
      (restObs : Observed me (semantics x) tail) :
      Observed (spec := TypeTree.node Moves rest) me
        (show PFunctor.FreeM.Displayed.Decoration (P := TypeTree.basePFunctor)
            (α := PUnit.{w + 1}) (StepContext Party) (TypeTree.node Moves rest) from
          ⟨node, semantics⟩)
        (show PFunctor.FreeM.Path (TypeTree.node Moves rest) from
          ⟨x, tail⟩)

namespace Observed

/--
The number of visited nodes recorded by an observed sequential path.
-/
def length {Party : Type u} [DecidableEq Party] {me : Party} :
    {spec : Interaction.TypeTree.{w}} →
      {semantics : PFunctor.FreeM.Displayed.Decoration (P := TypeTree.basePFunctor)
        (α := PUnit.{w + 1}) (StepContext Party) spec} →
      {tr : PFunctor.FreeM.Path spec} →
      Observed me semantics tr →
      Nat
  | .done, _, _, Observed.done => 0
  | .node _ _, _, _, Observed.step _ restObs => restObs.length.succ

/--
`ofPath me semantics tr` is the canonical observed sequential path
induced by the concrete global path `tr`.

It is obtained by replaying `tr` and, at each visited node, extracting the
observation that the local view for `me` exposes there.
-/
def ofPath {Party : Type u} [DecidableEq Party] (me : Party) :
    {spec : Interaction.TypeTree.{w}} →
      (semantics : PFunctor.FreeM.Displayed.Decoration (P := TypeTree.basePFunctor)
        (α := PUnit.{w + 1}) (StepContext Party) spec) →
      (tr : PFunctor.FreeM.Path spec) →
      Observed me semantics tr
  | .done, _, _ =>
      show Observed (Party := Party) me (spec := .done) PUnit.unit PUnit.unit from
        .done
  | .node _ _, ⟨node, semantics⟩, ⟨x, tail⟩ =>
      .step ((node.views me).obsOf x) (ofPath me (semantics x) tail)

end Observed

/--
`Observed me step tr` is the sequence of local observations exposed to `me`
while the step `step` executes along the path `tr`.

This is the most convenient step-level type when working with concrete process
steps rather than raw decorations.
-/
abbrev ObservedPath {Party : Type u} [DecidableEq Party] (me : Party)
    {P : Type v} (step : Step Party P) (tr : PFunctor.FreeM.Path step.tree) :=
  Observed me step.semantics tr

/--
`observe me step tr` is the canonical observed sequential path induced by
running `step` along `tr`.
-/
abbrev observe {Party : Type u} [DecidableEq Party] (me : Party)
    {P : Type v} (step : Step Party P) (tr : PFunctor.FreeM.Path step.tree) :
    ObservedPath me step tr :=
  Observed.ofPath me step.semantics tr

end Step

namespace StepOver

/--
`ObservedPath me resolve step tr` is the local observation sequence seen
by `me` when the generic step `step` is interpreted through the context
projection `resolve : Γ → StepContext Party`.
-/
abbrev ObservedPath
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u} [DecidableEq Party]
    (me : Party)
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    {P : Type v}
    (step : StepOver Γ P)
    (tr : PFunctor.FreeM.Path step.tree) :=
  Step.ObservedPath me (step.mapContext resolve) tr

/--
`observe me resolve step tr` is the canonical observed sequential path of
`step` along `tr`, after projecting the generic step context into
`StepContext`.
-/
abbrev observe
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u} [DecidableEq Party]
    (me : Party)
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    {P : Type v}
    (step : StepOver Γ P)
    (tr : PFunctor.FreeM.Path step.tree) :
    ObservedPath me resolve step tr :=
  Step.observe me (step.mapContext resolve) tr

end StepOver

namespace ProcessOver

/--
`Trace process p` is a finite execution trace of the residual process state
`p`.

Each `step` constructor records one whole sequential path for the current
process step, then continues with the residual process selected by that
path. The `done` constructor is available only when the current step has
no complete paths at all, so a `Trace` represents a genuinely terminated
finite execution.

`ProcessOver.Trace` is therefore the generic finite-history object for the
dynamic concurrent core: one element per process step, where each element
remembers the entire internal interaction episode that realized that step.
-/
inductive Trace
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} (process : ProcessOver P Γ) :
    process.Proc → Sort _ where
  | /-- A finished execution of a residual process state whose current step has
    no complete paths. -/
    done {p : process.Proc} :
      ((process.step p).tree.Path → False) →
      Trace process p
  | /-- Execute one complete sequential step path and continue with the
    residual process state induced by that path. -/
    step {p : process.Proc}
      (tr : (process.step p).tree.Path) :
      Trace process ((process.step p).next tr) →
      Trace process p

namespace Trace

/-- The number of process steps recorded by a finite execution trace. -/
def length
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ} :
    {p : process.Proc} → Trace process p → Nat
  | _, .done _ => 0
  | _, .step _ tail => tail.length.succ

/--
`currentControllers resolve trace` records the current controlling party of
each executed process step after projecting the generic step context into
`StepContext`.
-/
def currentControllers
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party)) :
    {p : process.Proc} → Trace process p → List (Option Party)
  | _, .done _ => []
  | p, .step tr tail =>
      ((process.step p).mapContext resolve).currentController? tr ::
        currentControllers resolve tail

/--
`controllerPaths resolve trace` records the full controller path of each
executed process step after projecting the generic step context into
`StepContext`.
-/
def controllerPaths
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u}
    {P : Type v} {process : ProcessOver P Γ}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party)) :
    {p : process.Proc} → Trace process p → List (List Party)
  | _, .done _ => []
  | p, .step tr tail =>
      ((process.step p).mapContext resolve).controllerPath tr ::
        controllerPaths resolve tail

/--
`events eventMap trace` records the external event label attached to each
process step path by the stable event map `eventMap`.
-/
def events
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event) :
    {p : process.Proc} → Trace process p → List Event
  | _, .done _ => []
  | p, .step tr tail =>
      eventMap p tr :: events eventMap tail

/--
`tickets ticketMap trace` records the stable tickets attached to each process
step path by `ticketMap`.
-/
def tickets
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket) :
    {p : process.Proc} → Trace process p → List Ticket
  | _, .done _ => []
  | p, .step tr tail =>
      ticketMap p tr :: tickets ticketMap tail

@[simp, grind =]
theorem length_done
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {p : process.Proc}
    (h : (process.step p).tree.Path → False) :
    length (.done h : Trace process p) = 0 := rfl

@[simp, grind =]
theorem length_step
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {P : Type v} {process : ProcessOver P Γ}
    {p : process.Proc}
    (tr : (process.step p).tree.Path)
    (tail : Trace process ((process.step p).next tr)) :
    length (.step tr tail : Trace process p) = tail.length.succ := rfl

end Trace

/--
`ObservedTrace me resolve process trace` is the exact typed sequence of local
observations available to `me` along the concrete process execution `trace`,
after interpreting the generic node context through `resolve`.
-/
inductive ObservedTrace
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u} [DecidableEq Party]
    (me : Party)
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    {P : Type v} (process : ProcessOver P Γ) :
    {p : process.Proc} → Trace process p → Sort _ where
  | /-- The unique observed trace of a finished quiescent execution. -/
    done {p : process.Proc}
      {h : (process.step p).tree.Path → False} :
      ObservedTrace me resolve process (.done h : Trace process p)
  | /-- Extend an observed trace by the observed sequential path of the
    current step. -/
    step {p : process.Proc}
      {tr : (process.step p).tree.Path}
      {tail : Trace process ((process.step p).next tr)}
      (obs : StepOver.ObservedPath me resolve (process.step p) tr)
      (rest : ObservedTrace me resolve process tail) :
      ObservedTrace me resolve process (.step tr tail : Trace process p)

namespace ObservedTrace

/-- The number of process steps recorded by an observed trace. -/
def length
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u} [DecidableEq Party]
    {me : Party} {resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party)}
    {P : Type v} {process : ProcessOver P Γ} :
    {p : process.Proc} → {trace : Trace process p} →
      ObservedTrace me resolve process trace →
      Nat
  | _, _, ObservedTrace.done => 0
  | _, _, ObservedTrace.step _ rest => rest.length.succ

/--
`ofTrace me resolve process trace` is the canonical observed process trace
induced by the concrete execution trace `trace`.
-/
def ofTrace
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u} [DecidableEq Party]
    (me : Party)
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    {P : Type v} (process : ProcessOver P Γ) :
    {p : process.Proc} → (trace : Trace process p) →
      ObservedTrace me resolve process trace
  | _, .done _ => .done
  | p, .step tr tail =>
      .step
        (StepOver.observe me resolve (process.step p) tr)
        (ofTrace me resolve process tail)

@[simp, grind =]
theorem length_done
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u} [DecidableEq Party]
    {me : Party} {resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party)}
    {P : Type v} {process : ProcessOver P Γ} {p : process.Proc}
    {h : (process.step p).tree.Path → False} :
    length (ObservedTrace.done
      (me := me) (resolve := resolve) (process := process) (p := p) (h := h)) = 0 := by
  rfl

@[simp, grind =]
theorem length_step
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u} [DecidableEq Party]
    {me : Party} {resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party)}
    {P : Type v} {process : ProcessOver P Γ} {p : process.Proc}
    {tr : (process.step p).tree.Path}
    {tail : Trace process ((process.step p).next tr)}
    (obs : StepOver.ObservedPath me resolve (process.step p) tr)
    (rest : ObservedTrace me resolve process tail) :
    length (.step obs rest : ObservedTrace me resolve process
      (.step tr tail : Trace process p)) = rest.length.succ := by
  rfl

/--
The canonical observed process trace has the same number of process steps as
the underlying execution trace.
-/
theorem length_ofTrace
    {Γ : Interaction.TypeTree.Node.Context.{w, w₂}}
    {Party : Type u} [DecidableEq Party]
    {me : Party}
    (resolve : Interaction.TypeTree.Node.ContextHom Γ (StepContext Party))
    {P : Type v} (process : ProcessOver P Γ) :
    {p : process.Proc} → (trace : Trace process p) →
      (ofTrace me resolve process trace).length = trace.length
  | _, .done _ => rfl
  | _, .step _ tail => by
      simpa [ObservedTrace.ofTrace, ObservedTrace.length, Trace.length] using
        congrArg Nat.succ (length_ofTrace (me := me) resolve process tail)

end ObservedTrace

end ProcessOver

namespace Process

/-- The closed-world specialization of `ProcessOver.Trace`. -/
abbrev Trace {Party : Type u} {P : Type v} (process : Process P Party) :=
  ProcessOver.Trace process

namespace Trace

/-- The number of process steps recorded by a finite closed-world execution
trace. -/
abbrev length {Party : Type u} {P : Type v} {process : Process P Party} :
    {p : process.Proc} → Process.Trace process p → Nat :=
  ProcessOver.Trace.length

/-- The current controlling party of each executed step of a closed-world
trace. -/
def currentControllers {Party : Type u} {P : Type v} {process : Process P Party} :
    {p : process.Proc} → Process.Trace process p → List (Option Party)
  | _, .done _ => []
  | p, .step tr tail =>
      (process.step p).currentController? tr :: currentControllers tail

/-- The full controller path of each executed step of a closed-world trace. -/
def controllerPaths {Party : Type u} {P : Type v} {process : Process P Party} :
    {p : process.Proc} → Process.Trace process p → List (List Party)
  | _, .done _ => []
  | p, .step tr tail =>
      (process.step p).controllerPath tr :: controllerPaths tail

/-- The stable event labels attached to the executed steps of a closed-world
trace. -/
abbrev events {Party : Type u} {P : Type v} {process : Process P Party} {Event : Type w₃}
    (eventMap : process.EventMap Event) :
    {p : process.Proc} → Process.Trace process p → List Event :=
  ProcessOver.Trace.events eventMap

/-- The stable tickets attached to the executed steps of a closed-world trace. -/
abbrev tickets {Party : Type u} {P : Type v} {process : Process P Party} {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket) :
    {p : process.Proc} → Process.Trace process p → List Ticket :=
  ProcessOver.Trace.tickets ticketMap

@[simp, grind =]
theorem length_done {Party : Type u} {P : Type v} {process : Process P Party}
    {p : process.Proc} (h : (process.step p).tree.Path → False) :
    length (.done h : Process.Trace process p) = 0 :=
  ProcessOver.Trace.length_done h

@[simp, grind =]
theorem length_step {Party : Type u} {P : Type v} {process : Process P Party}
    {p : process.Proc}
    (tr : (process.step p).tree.Path)
    (tail : Process.Trace process ((process.step p).next tr)) :
    length (.step tr tail : Process.Trace process p) = tail.length.succ :=
  ProcessOver.Trace.length_step tr tail

end Trace

/-- The closed-world specialization of `ProcessOver.ObservedTrace`. -/
abbrev ObservedTrace {Party : Type u} [DecidableEq Party]
    (me : Party) {P : Type v} (process : Process P Party) :
    {p : process.Proc} → Process.Trace process p → Sort _ :=
  ProcessOver.ObservedTrace me
    (Interaction.TypeTree.Node.ContextHom.id (StepContext Party))
    process

namespace ObservedTrace

/-- The number of process steps recorded by an observed closed-world trace. -/
abbrev length {Party : Type u} [DecidableEq Party]
    {me : Party} {P : Type v} {process : Process P Party} :
    {p : process.Proc} → {trace : Process.Trace process p} →
      ObservedTrace me process trace →
      Nat :=
  ProcessOver.ObservedTrace.length

/--
`ofTrace me process trace` is the canonical observed closed-world process trace
induced by the concrete execution trace `trace`.
-/
abbrev ofTrace {Party : Type u} [DecidableEq Party]
    (me : Party) {P : Type v} (process : Process P Party) :
    {p : process.Proc} → (trace : Process.Trace process p) →
      ObservedTrace me process trace :=
  ProcessOver.ObservedTrace.ofTrace me
    (Interaction.TypeTree.Node.ContextHom.id (StepContext Party))
    process

@[grind =]
theorem length_done {Party : Type u} [DecidableEq Party]
    {me : Party} {P : Type v} {process : Process P Party} {p : process.Proc}
    {h : (process.step p).tree.Path → False} :
    length (ProcessOver.ObservedTrace.done
      (me := me)
      (resolve := Interaction.TypeTree.Node.ContextHom.id (StepContext Party))
      (process := process)
      (p := p)
      (h := h)) = 0 := by
  rfl

@[grind =]
theorem length_step {Party : Type u} [DecidableEq Party]
    {me : Party} {P : Type v} {process : Process P Party} {p : process.Proc}
    {tr : (process.step p).tree.Path}
    {tail : Process.Trace process ((process.step p).next tr)}
    (obs : StepOver.ObservedPath me
      (Interaction.TypeTree.Node.ContextHom.id (StepContext Party))
      (process.step p) tr)
    (rest : ObservedTrace me process tail) :
    length (.step obs rest : ObservedTrace me process
      (.step tr tail : Process.Trace process p)) = rest.length.succ := by
  rfl

/--
The canonical observed closed-world trace has the same number of process steps
as the underlying execution trace.
-/
theorem length_ofTrace {Party : Type u} [DecidableEq Party]
    {me : Party} {P : Type v} (process : Process P Party) :
    {p : process.Proc} → (trace : Process.Trace process p) →
      (ofTrace me process trace).length = trace.length :=
  ProcessOver.ObservedTrace.length_ofTrace
    (me := me)
    (resolve := Interaction.TypeTree.Node.ContextHom.id (StepContext Party))
    process

end ObservedTrace

end Process

end Concurrent
end Interaction
