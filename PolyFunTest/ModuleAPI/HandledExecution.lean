/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveNetwork.HandledAssembly
public import PolyFun.Interaction.Concurrent.Fairness

/-! # Ordinary-import handled execution and fairness consumers

The stateful consumer distinguishes dependent answers, threads state through effects, and
continues a residual without interpreting an operation twice. Generic laws retain arbitrary
diagrams and lawful monads rather than specializing to a file-reporting application.
-/

@[expose] public section

namespace PolyFunTest.HandledExecution

open PFunctor DynSystem Interaction Interaction.Execution ReactiveProcess ReactiveNetwork

/-- Distinct response fibers prevent accidentally exchanging the operations. -/
abbrev Effects : PFunctor := ⟨Bool, fun b ↦ if b then Nat else Unit⟩

/-- A write followed by a read, with no packet traffic. -/
def program : Process Effects PortBoundary.empty Unit Nat :=
  DynComputation.ofFreeM fun _ ↦ .liftBind (.effect false) fun _ ↦
    .liftBind (.effect true) fun n ↦ .pure (.returned n)

/-- State and failure are ambient capabilities explicitly selected by the handler. -/
def handler : Handler (StateT Nat Option) Effects
  | false, n => some ((), n + 1)
  | true, n => some (n, n)

/-- The existing assembly owns the handler; no separate dispatcher is needed. -/
def diagram := (HandledAssembly.atom program handler).diagram

example : ((do
    let first ← diagram.runToken () 1 (diagram.initial ())
    let last ← diagram.runToken () 1 first
    return outcome () last).run 7) = some (some (.returned 8), 8) := rfl

/-- Transformer order deliberately retains the first effect when the resumed read fails. -/
def failingHandler : Handler (ExceptT String (StateM Nat)) Effects
  | false => modify (· + 1)
  | true => throw "read failed"

example : ((do
    let d := (HandledAssembly.atom program failingHandler).diagram
    let first ← d.runToken () 1 (d.initial ())
    let last ← d.runToken () 1 first
    return outcome () last).run.run 7) = (Except.error "read failed", 8) := rfl

example {m : Type → Type} [Monad m] [LawfulMonad m] {N R : Type} [DecidableEq N]
    {boundary : PortBoundary} (d : HandledDiagram m N boundary R) (environment : N)
    (state : State (d.network environment) Unit) (first rest : List (Activation N)) :
    d.runFIFO environment (first ++ rest) state =
      (d.runFIFO environment first state >>= d.runFIFO environment rest) :=
  d.runFIFO_append environment first rest state

example {m : Type → Type} [Monad m] [LawfulMonad m] {N R : Type} [DecidableEq N]
    {boundary : PortBoundary} (d : HandledDiagram m N boundary R) (environment : N)
    (state : State (d.network environment) Unit) (first rest : Nat) :
    d.runToken environment (first + rest) state =
      (d.runToken environment first state >>= d.runToken environment rest) :=
  d.runToken_add environment first rest state

example {Γ : TypeTree.Node.Context} (t : Concurrent.ProcessOver.Ticketed Γ)
    (r : Concurrent.ProcessOver.Run t.toProcess)
    (h : Concurrent.ProcessOver.Ticketed.WeakFair t r) (ticket : t.Ticket) :
    Concurrent.ProcessOver.Run.EventuallyAlways
        (Concurrent.ProcessOver.Ticketed.enabledAt t r ticket) →
      Concurrent.ProcessOver.Run.InfinitelyOften
        (Concurrent.ProcessOver.Ticketed.firedAt t r ticket) :=
  (Concurrent.ProcessOver.Ticketed.weakFairOn_iff t r ticket).mp
    ((Concurrent.ProcessOver.Ticketed.weakFair_iff t r).mp h ticket)

end PolyFunTest.HandledExecution
