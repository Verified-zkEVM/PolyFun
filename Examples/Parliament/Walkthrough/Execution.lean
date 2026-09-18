/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.Interaction
public import PolyFun.PFunctor.Dynamical.Run

/-! # Certified meeting paths as ordinary PolyFun execution prefixes

The meeting model carries commands and event batches in its certified directions.
A generic prefix remembers the same choices. Labels recover the domain journal,
while `SafetySpec` packages the initialization and preservation obligation.
-/

public section

namespace Parliament.Walkthrough

open PFunctor.DynSystem

variable {D : MotionDomain} {rules : Rules}

/-- Commands label the legal directions of the meeting machine. -/
def commandLabel : (meetingSystem D rules).EventMap (Command D) := fun _ input => input.command

/-- Each accepted direction emits one batch of parliamentary events. -/
def receiptLabel : (meetingSystem D rules).EventMap (List Event) := fun _ input => input.events

/-- Forget domain-specific indices while retaining every chosen legal direction. -/
def toPrefix {s last : AssemblyState D} {commands : List (Command D)} {events : List Event} :
    MeetingPath rules s commands last events → Prefix (meetingSystem D rules) s commands.length
  | .nil _ => .nil
  | .cons input tail => .step input (toPrefix tail)

theorem toPrefix_last {s last : AssemblyState D} {commands : List (Command D)}
    {events : List Event} (path : MeetingPath rules s commands last events) :
    (toPrefix path).last = last := by
  induction path with
  | nil => rfl
  | cons input tail ih => exact ih

theorem toPrefix_commands {s last : AssemblyState D} {commands : List (Command D)}
    {events : List Event} (path : MeetingPath rules s commands last events) :
    (toPrefix path).events commandLabel = commands := by
  induction path with
  | nil => rfl
  | cons input tail ih => exact congrArg (List.cons input.command) ih

theorem toPrefix_events {s last : AssemblyState D} {commands : List (Command D)}
    {events : List Event} (path : MeetingPath rules s commands last events) :
    ((toPrefix path).events receiptLabel).flatten = events := by
  induction path with
  | nil => rfl
  | cons input tail ih => exact congrArg (input.events ++ ·) ih

/-- Initialization and safety predicates attached to the existing meeting dynamics. -/
@[expose] def meetingSafety (rules : Rules) (initial : AssemblyState D) :
    SafetySpec (MeetingP D rules).sigmaPFunctor where
  State := AssemblyState D
  toDynSystem := meetingSystem D rules
  init state := state = initial ∧ state.WellFormed
  safe := AssemblyState.WellFormed

/-- Safety follows arbitrary environment choices, not only a scripted meeting. -/
theorem prefix_wellFormed {s : AssemblyState D} {n : Nat}
    (orbit : Prefix (meetingSystem D rules) s n) (valid : s.WellFormed) :
    orbit.last.WellFormed := by
  induction orbit with
  | nil => exact valid
  | step input tail ih => exact ih input.legal.wellFormed

/-- Every finite execution from an initialized safety specification ends safely. -/
theorem meetingSafety_safe (initial s : AssemblyState D) {n : Nat}
    (orbit : Prefix (meetingSafety rules initial).toDynSystem s n)
    (initialized : (meetingSafety rules initial).init s) :
    (meetingSafety rules initial).safe orbit.last := prefix_wellFormed orbit initialized.2

end Parliament.Walkthrough
