/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveNetwork.HandledAssembly

/-!
# Intrinsic handler regressions

Identical polynomial machines and routing diagrams can produce different observations under
different local effect interpreters. Carrying those interpreters in the assembled data makes
this distinction explicit, while raw compilation preserves it.
-/

public section

namespace Interaction.Execution.ReactiveNetwork.HandlerTests

open Interaction.Open PFunctor ReactiveProcess DynSystem OpenSyntax

@[expose] def bitEffect : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

@[expose] def readBit : Process bitEffect PortBoundary.empty Unit Bool :=
  DynComputation.ofFreeM fun _ =>
    .liftBind (.effect ()) fun bit => .pure (.returned bit)

@[expose] def agent (value : Bool) : HandledAssembly Id PortBoundary.empty Bool :=
  HandledAssembly.atom readBit fun _ => value

/-- The machines, states, and routes alone do not distinguish the two interpretations. -/
example : (agent false).diagram.toDiagram = (agent true).diagram.toDiagram := rfl

/-- One actual local operation returns the Boolean selected by that node's interpreter. -/
example (value : Bool) : (agent value).tokenObservation () 1 = some (.returned value) := by
  cases value <;> rfl

/-- Equality of unhandled routing diagrams does not justify equality of observed execution. -/
theorem changing_handler_changes_observation :
    (agent false).tokenObservation () 1 ≠ (agent true).tokenObservation () 1 := by
  intro h
  cases h

/-- Zero fuel retains the unfinished local operation under either interpreter. -/
example (value : Bool) : (agent value).tokenObservation () 0 = none := by
  cases value <;> rfl

@[expose] def raw (value : Bool) :
    Raw (fun Δ => HandledAssembly Id Δ Bool) PortBoundary.empty := .atom (agent value)

/-- Raw interpretation retains the operation handler as executable data. -/
example (value : Bool) :
    (HandledAssembly.compile (raw value) fun atom => atom).tokenObservation () 1 =
      some (.returned value) := by
  cases value <;> rfl

@[expose] def partialAgent : HandledAssembly Option PortBoundary.empty Bool :=
  HandledAssembly.atom readBit fun _ => none

/-- The outer option records failure of the interpreter, distinct from an unfinished prefix. -/
example : partialAgent.tokenObservation () 0 = some none := rfl

/-- Running the failing operation produces no residual state or terminal observation. -/
example : partialAgent.tokenObservation () 1 = none := rfl

/-- Failure and a successfully executed unfinished prefix are different runtime observations. -/
example : partialAgent.tokenObservation () 1 ≠ partialAgent.tokenObservation () 0 := by decide

end Interaction.Execution.ReactiveNetwork.HandlerTests
