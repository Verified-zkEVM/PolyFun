/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ReactiveNetwork

/-!
# Reactive delivery regressions

An environment sends a Boolean to an echo service and waits for the response. Both runners
observe the actual received value. FIFO needs explicit deliveries; token passing transfers
control with sends. The tests also separate residual computation, abort, and return.
-/

public section

namespace Interaction.UC.ReactiveNetwork.Tests

open PFunctor ReactiveProcess DynSystem

@[expose] def noEffect : PFunctor.{0, 0} := ⟨Empty, Empty.elim⟩

@[expose] def booleanPort : Interface := ⟨Unit, fun _ => Bool⟩

@[expose] def ports : PortBoundary := ⟨booleanPort, booleanPort⟩

def env (value : Bool) : FreeM (signature noEffect ports) (Outcome Bool) :=
  .liftBind (.send ⟨(), value⟩) fun _ =>
    .liftBind .receive fun packet => .pure (.returned packet.2)

def echo : FreeM (signature noEffect ports) (Outcome Bool) :=
  .liftBind .receive fun packet =>
    .liftBind (.send packet) fun _ => .pure (.returned packet.2)

@[expose] def echoNetwork (value : Bool) : Network Bool PortBoundary.empty Bool where
  effect := fun _ => noEffect
  ports := fun _ => ports
  component id := DynComputation.ofFreeM fun _ => if id then echo else env value
  route id packet := .inl ⟨!id, packet⟩
  ingress packet := packet.1.elim
  environment := false

def impl (value : Bool) :
    (id : Bool) → Handler (StateT Unit Id) ((echoNetwork value).effect id) :=
  fun _ operation => operation.elim

def fifoSchedule : List (Activation Bool) :=
  [.node false, .deliver, .node true, .node true, .deliver, .node false]

def tokenRun (value : Bool) : State (echoNetwork value) Unit :=
  runToken (impl value) 4 (initial (echoNetwork value) ())

def fifoRun (value : Bool) : State (echoNetwork value) Unit :=
  runFIFO (impl value) fifoSchedule (initial (echoNetwork value) ())

/-- Token passing observes the actual reply to the environment's chosen input. -/
theorem tokenRun_outcome (value : Bool) :
    outcome false (tokenRun value) = some (.returned value) := by
  cases value <;> rfl

/-- FIFO yields the same reply with two separately charged delivery activations. -/
example (value : Bool) : outcome false (fifoRun value) = some (.returned value) := by
  cases value <;> rfl

/-- The two policies consume different amounts of fuel even in this serial fragment. -/
example (value : Bool) : (tokenRun value).elapsed = 4 ∧ (fifoRun value).elapsed = 6 := by
  cases value <;> exact ⟨rfl, rfl⟩

/-- Scheduling the receiver cannot manufacture a delivery from the pending FIFO queue. -/
example (value : Bool) :
    outcome false (runFIFO (m := Id) (impl value) [.node false, .node true, .node false]
      (initial (echoNetwork value) ())) = none := by
  cases value <;> rfl

/-- An insufficient prefix retains an unfinished environment, rather than returning a value. -/
example (value : Bool) :
    outcome false (runToken (m := Id) (impl value) 3 (initial (echoNetwork value) ())) = none := by
  cases value <;> rfl

/-- A completed execution has no pending FIFO packets or delivered unread mail. -/
example (value : Bool) : (fifoRun value).pending = [] ∧
    (fifoRun value).inbox false = [] ∧ (fifoRun value).inbox true = [] := by
  cases value <;> exact ⟨rfl, rfl, rfl⟩

/-- Successful outcomes from different environment inputs are distinguishable. -/
example : outcome false (tokenRun false) ≠ outcome false (tokenRun true) := by
  intro h
  cases h

def abortNetwork : Network Unit PortBoundary.empty Bool where
  effect := fun _ => noEffect
  ports := fun _ => ports
  component _ := DynComputation.ofFreeM fun _ => .pure .aborted
  route _ packet := .inl ⟨(), packet⟩
  ingress packet := packet.1.elim
  environment := ()

/-- An explicit abort is a terminal outcome, distinct from a residual process. -/
example : outcome () (initial abortNetwork ()) = some .aborted := rfl

end Interaction.UC.ReactiveNetwork.Tests
