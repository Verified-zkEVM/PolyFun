/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Run

/-!
# Event traces of labeled systems

`DynSystem.Labeled.Trace m s events t` says that some finite orbit of the labeled system `m`
from `s` ends at `t` and emits exactly `events`. It is the labeled counterpart of
`DynSystem.ReachableIn`:
* `Trace.nil` is the empty trace;
* `Trace.append` concatenates traces at a shared state, through `Prefix.append`;
* `Trace.reachableIn` forgets the events and keeps the trace's length.
-/

@[expose] public section

universe u uA uB w

namespace PFunctor.DynSystem.Labeled

variable {p : PFunctor.{uA, uB}} (m : Labeled.{u, uA, uB, w} p)

/-- Some finite orbit from `s` ends at `t` with exactly the event trace `events`. -/
def Trace (s : m.State) (events : List m.Event) (t : m.State) : Prop :=
  ∃ (n : ℕ) (orbit : m.toDynSystem.Prefix s n), orbit.events m.event = events ∧ orbit.last = t

variable {m}

/-- The empty trace stays put. -/
theorem Trace.nil (s : m.State) : m.Trace s [] s := ⟨0, .nil, rfl, rfl⟩

/-- Traces concatenate at their shared state. -/
theorem Trace.append {s mid t : m.State} {first second : List m.Event}
    (left : m.Trace s first mid) (right : m.Trace mid second t) :
    m.Trace s (first ++ second) t := by
  obtain ⟨_, pre, rfl, rfl⟩ := left
  obtain ⟨_, post, rfl, rfl⟩ := right
  exact ⟨_, pre.append post, pre.events_append m.event post, pre.last_append post⟩

/-- A trace witnesses reachability in as many steps as it has events. -/
theorem Trace.reachableIn {s t : m.State} {events : List m.Event} (trace : m.Trace s events t) :
    m.toDynSystem.ReachableIn events.length s t := by
  obtain ⟨n, orbit, rfl, rfl⟩ := trace
  rw [orbit.length_events m.event]
  exact ⟨orbit, rfl⟩

end PFunctor.DynSystem.Labeled
