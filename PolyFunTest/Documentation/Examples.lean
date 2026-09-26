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

/-!
# Ordinary-import consumers of the documentation examples

These checks exercise the documented results across module boundaries. They also make
the tutorial library part of `lake test` without importing examples into production.
-/

open PolyFunExamples

example : Requests.twoRequests.liftM Requests.increment = (4, 5) := rfl

example : Requests.twoRequests.liftM Requests.double = (6, 12) := Requests.twoRequests_double

example (xs ys : List Nat) : Machines.counter.run 0 (xs ++ ys) =
    Machines.counter.run (Machines.counter.run 0 xs) ys := Machines.counter_run_append 0 xs ys

example : IPFunctor.FreeM₂ IPFunctor.Examples.proto
    IPFunctor.Examples.Phase.opn IPFunctor.Examples.Phase.counting Nat :=
  IPFunctor.Examples.TwoIndex.run
