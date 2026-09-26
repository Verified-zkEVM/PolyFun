/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Examples.Tutorials.Requests
import Examples.Tutorials.Machines
import Examples.Tutorials.IndexedPrograms
import Examples.Tutorials.InteractionTrees
import PolyFun.Interaction.Interface
import PolyFun.Interaction.Execution.ReactiveProcess
import PolyFun.Interaction.Execution.RequestNetwork
import PolyFun.Interaction.Open.OpenSyntax.Expr
import PolyFun.Interaction.Open.Emulates

/-!
# Documentation examples as a separate package

Ordinary imports expose the teaching programs and the interface, execution, and open-system
APIs. These checks consume public equations and constructor contracts across a package boundary.
-/

open PolyFunExamples
open Interaction

example : Requests.twoRequests.liftM Requests.increment = (4, 5) := rfl

example : Requests.twoRequests.liftM Requests.double = (6, 12) :=
  Requests.twoRequests_double

example (initial : Nat) (xs ys : List Nat) :
    Machines.counter.run initial (xs ++ ys) =
      Machines.counter.run (Machines.counter.run initial xs) ys :=
  Machines.counter_run_append initial xs ys

example : IPFunctor.FreeM₂ IPFunctor.Examples.proto
    IPFunctor.Examples.Phase.opn IPFunctor.Examples.Phase.counting Nat :=
  IPFunctor.Examples.TwoIndex.run

example (I : Interface) : Type := Interface.Packet I

example (effect : PFunctor.{0, 0}) (boundary : PortBoundary) :
    (Execution.ReactiveProcess.signature effect boundary).A := .tick

example : Execution.RequestNetwork.Activation Unit := .deliver

example (T : Open.OpenTheory) (Δ : PortBoundary) (system : T.Obj Δ) :
    Open.Emulates system system (Open.Observation.eq T) :=
  Open.Emulates.refl _ _
