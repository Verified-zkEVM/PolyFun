/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.Trace

/-!
# Ordinary-import canaries for composed orbits and labeled traces

A counter emits its current value at each step. Through ordinary imports, its orbits join and
split, `Prefix.append` reduces by its public equations, and its labeled traces concatenate and
project to counted reachability. A system with independent state, position, direction and
event universes checks that the statements do not tie them together.
-/

@[expose] public section

universe u uA uB w

namespace PolyFunTest.ModuleAPI.LabeledTraces

open PFunctor PFunctor.DynSystem

/-- A counter over the terminal interface. -/
abbrev counter : DynSystem ℕ y.{0, 0} := (fun _ => PUnit.unit) ⇆ fun n _ => n + 1

/-- The counter labels each step with the value it leaves. -/
abbrev labeled : Labeled y.{0, 0} where
  State := ℕ
  toDynSystem := counter
  Event := ℕ
  event n _ := n

/-- One step of the counter. -/
def tick (n : ℕ) : counter.Prefix n 1 := .step PUnit.unit .nil

example : (tick 0).append (tick 1) = .step PUnit.unit (.step PUnit.unit .nil) := rfl

example : ((tick 0).append (tick 1)).last = 2 := rfl

example : ((tick 0).append (tick 1)).events labeled.event = [0, 1] := rfl

example : ((tick 3).append (tick 4)).events labeled.event =
    (tick 3).events labeled.event ++ (tick 4).events labeled.event :=
  Prefix.events_append labeled.event (tick 3) (tick 4)

example : counter.ReachableIn 2 0 2 :=
  ReachableIn.add (m := 1) (n := 1) ⟨tick 0, rfl⟩ ⟨tick 1, rfl⟩

example : ∃ mid, counter.ReachableIn 1 0 mid ∧ counter.ReachableIn 1 mid 2 :=
  ReachableIn.split (n := 1) (m := 1) ⟨(tick 0).append (tick 1), rfl⟩

example : labeled.Trace 0 [0, 1] 2 :=
  Labeled.Trace.append (m := labeled) (first := [0]) (second := [1])
    ⟨1, tick 0, rfl, rfl⟩ ⟨1, tick 1, rfl, rfl⟩

example (n : ℕ) : labeled.Trace n [] n := Labeled.Trace.nil (m := labeled) n

example (trace : labeled.Trace 0 [0, 1] 2) : counter.ReachableIn 2 0 2 := trace.reachableIn

/-! ## Independent universes -/

variable {p : PFunctor.{uA, uB}}

example (m : Labeled.{u, uA, uB, w} p) {s mid t : m.State} {first second : List m.Event}
    (left : m.Trace s first mid) (right : m.Trace mid second t) :
    m.Trace s (first ++ second) t :=
  left.append right

example {S : Type u} (s : DynSystem S p) {m n : ℕ} {st st' : S}
    (h : s.ReachableIn (n + m) st st') :
    ∃ mid, s.ReachableIn m st mid ∧ s.ReachableIn n mid st' :=
  ReachableIn.split h

end PolyFunTest.ModuleAPI.LabeledTraces
