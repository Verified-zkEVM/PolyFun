/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Concurrent.MutualSafetyRefinement

/-!
# Common concurrent equivalence notions

This file packages the mutual-refinement-based equivalence notions that are most
useful in practice.

The underlying `Refinement.MutualSafetyRefinement` API is intentionally general: it can
talk about any step relation whatsoever. For actual protocol work, however, one
usually wants a smaller family of standard questions:

* do the two systems expose the same controller at each step?
* do they expose the same full controller path?
* do they produce the same external event trace?
* do they preserve the same fairness tickets?
* does a chosen party observe the same thing in both systems?

This file packages exactly those questions as named equivalence notions,
provides their `refl`, `symm`, and `trans` operations, and records the immediate
preservation lemmas for finite run prefixes. Trace and ticket transitivity use
one shared map on the intermediate system, making the compared observation
type explicit rather than hiding a change of representation.

Each `*_eq` preservation lemma is a thin equivalence-level wrapper around the
generic simulation-level `DynSystem.ForwardSimulation.*_mapRun`, specialized at
`equiv.forth`. Keeping the packaged form lets protocol proofs transport
observations directly from an equivalence without first projecting a forward
simulation.
-/

universe u v w

namespace Interaction
namespace Concurrent
namespace Equivalence

/--
`Controller left right` means that `left` and `right` are mutually safety-refining while
preserving the current controlling party chosen at each executed step.
-/
abbrev Controller {Party : Type u}
    (left right : Process.SafetySpec Party) :=
  Refinement.MutualSafetyRefinement left right
    Observation.Process.StepRel.byController
    (Observation.Process.StepRel.byController
      (left := right.toProcess) (right := left.toProcess))

/--
`ControllerPath left right` means that `left` and `right` are mutually safety-refining while
preserving the full controller path of each executed step.
-/
abbrev ControllerPath {Party : Type u}
    (left right : Process.SafetySpec Party) :=
  Refinement.MutualSafetyRefinement left right
    Observation.Process.StepRel.byPath
    (Observation.Process.StepRel.byPath
      (left := right.toProcess) (right := left.toProcess))

/--
`Trace left right eventLeft eventRight` means that `left` and `right` are
mutually safety-refining while preserving the stable external event label attached to each
complete step path.
-/
abbrev Trace {Party : Type u} {Event : Type w}
    (left right : Process.SafetySpec Party)
    (eventLeft : left.toProcess.EventMap Event)
    (eventRight : right.toProcess.EventMap Event) :=
  Refinement.MutualSafetyRefinement left right
    (Observation.Process.StepRel.byEvent eventLeft eventRight)
    (Observation.Process.StepRel.byEvent
      (left := right.toProcess) (right := left.toProcess) eventRight eventLeft)

/--
`Ticket left right ticketLeft ticketRight` means that `left` and `right` are
mutually safety-refining while preserving the stable tickets attached to complete step
paths.
-/
abbrev Ticket {Party : Type u} {TicketTy : Type w}
    (left right : Process.SafetySpec Party)
    (ticketLeft : left.toProcess.Tickets TicketTy)
    (ticketRight : right.toProcess.Tickets TicketTy) :=
  Refinement.MutualSafetyRefinement left right
    (Observation.Process.StepRel.byTicket ticketLeft ticketRight)
    (Observation.Process.StepRel.byTicket
      (left := right.toProcess) (right := left.toProcess) ticketRight ticketLeft)

/--
`Observation me left right` means that `left` and `right` are mutually safety-refining while
preserving the packed local observations exposed to the fixed party `me` at
every executed step.
-/
abbrev Observation {Party : Type u} [DecidableEq Party]
    (me : Party)
    (left right : Process.SafetySpec Party) :=
  Refinement.MutualSafetyRefinement left right
    (Observation.Process.StepRel.byObservation me)
    (Observation.Process.StepRel.byObservation
      (left := right.toProcess) (right := left.toProcess) me)

namespace Controller

/-- Controller equivalence is reflexive. -/
@[refl]
def refl {Party : Type u} (system : Process.SafetySpec Party) :
    Controller system system :=
  PFunctor.DynSystem.MutualSafetyRefinement.refl system
    Observation.Process.StepRel.byController
    Observation.Process.StepRel.byController
    (fun _ => rfl) (fun _ => rfl)

/-- Controller equivalence is symmetric. -/
@[symm]
def symm {Party : Type u} {left right : Process.SafetySpec Party}
    (equiv : Controller left right) : Controller right left :=
  PFunctor.DynSystem.MutualSafetyRefinement.symm equiv

/-- Controller equivalence is transitive. -/
@[trans]
def trans {Party : Type u} {left middle right : Process.SafetySpec Party}
    (first : Controller left middle) (second : Controller middle right) :
    Controller left right :=
  PFunctor.DynSystem.MutualSafetyRefinement.trans first second
    (by
      rintro ⟨pLeft, trLeft⟩ ⟨pRight, trRight⟩
        ⟨⟨pMiddle, trMiddle⟩, hFirst, hSecond⟩
      exact hFirst.trans hSecond)
    (by
      rintro ⟨pRight, trRight⟩ ⟨pLeft, trLeft⟩
        ⟨⟨pMiddle, trMiddle⟩, hSecond, hFirst⟩
      exact hSecond.trans hFirst)

/--
Along the forward direction of a controller equivalence, the current controller
sequence of every finite run prefix is preserved.
-/
theorem currentControllersUpTo_eq {Party : Type u}
    {left right : Process.SafetySpec Party}
    (equiv : Controller left right)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    Process.Run.currentControllersUpTo run n =
      Process.Run.currentControllersUpTo (equiv.forth.mapRun run hrel) n :=
  Refinement.SafetyRefinement.currentControllersUpTo_mapRun equiv.forth run hrel n

end Controller

namespace ControllerPath

/-- Controller-path equivalence is reflexive. -/
@[refl]
def refl {Party : Type u} (system : Process.SafetySpec Party) :
    ControllerPath system system :=
  PFunctor.DynSystem.MutualSafetyRefinement.refl system
    Observation.Process.StepRel.byPath
    Observation.Process.StepRel.byPath
    (fun _ => rfl) (fun _ => rfl)

/-- Controller-path equivalence is symmetric. -/
@[symm]
def symm {Party : Type u} {left right : Process.SafetySpec Party}
    (equiv : ControllerPath left right) : ControllerPath right left :=
  PFunctor.DynSystem.MutualSafetyRefinement.symm equiv

/-- Controller-path equivalence is transitive. -/
@[trans]
def trans {Party : Type u} {left middle right : Process.SafetySpec Party}
    (first : ControllerPath left middle) (second : ControllerPath middle right) :
    ControllerPath left right :=
  PFunctor.DynSystem.MutualSafetyRefinement.trans first second
    (by
      rintro ⟨pLeft, trLeft⟩ ⟨pRight, trRight⟩
        ⟨⟨pMiddle, trMiddle⟩, hFirst, hSecond⟩
      exact hFirst.trans hSecond)
    (by
      rintro ⟨pRight, trRight⟩ ⟨pLeft, trLeft⟩
        ⟨⟨pMiddle, trMiddle⟩, hSecond, hFirst⟩
      exact hSecond.trans hFirst)

/--
Along the forward direction of a controller-path equivalence, the full
controller-path sequence of every finite run prefix is preserved.
-/
theorem controllerPathsUpTo_eq {Party : Type u}
    {left right : Process.SafetySpec Party}
    (equiv : ControllerPath left right)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    Process.Run.controllerPathsUpTo run n =
      Process.Run.controllerPathsUpTo (equiv.forth.mapRun run hrel) n :=
  Refinement.SafetyRefinement.controllerPathsUpTo_mapRun equiv.forth run hrel n

end ControllerPath

namespace Trace

/-- Trace equivalence is reflexive for any fixed event map. -/
@[refl]
def refl {Party : Type u} {Event : Type w}
    (system : Process.SafetySpec Party)
    (event : system.toProcess.EventMap Event) : Trace system system event event :=
  PFunctor.DynSystem.MutualSafetyRefinement.refl system
    (Observation.Process.StepRel.byEvent event event)
    (Observation.Process.StepRel.byEvent event event)
    (fun _ => rfl) (fun _ => rfl)

/-- Trace equivalence is symmetric. -/
@[symm]
def symm {Party : Type u} {Event : Type w}
    {left right : Process.SafetySpec Party}
    {eventLeft : left.toProcess.EventMap Event}
    {eventRight : right.toProcess.EventMap Event}
    (equiv : Trace left right eventLeft eventRight) :
    Trace right left eventRight eventLeft :=
  PFunctor.DynSystem.MutualSafetyRefinement.symm equiv

/-- Trace equivalence is transitive through a shared middle event map. -/
@[trans]
def trans {Party : Type u} {Event : Type w}
    {left middle right : Process.SafetySpec Party}
    {eventLeft : left.toProcess.EventMap Event}
    {eventMiddle : middle.toProcess.EventMap Event}
    {eventRight : right.toProcess.EventMap Event}
    (first : Trace left middle eventLeft eventMiddle)
    (second : Trace middle right eventMiddle eventRight) :
    Trace left right eventLeft eventRight :=
  PFunctor.DynSystem.MutualSafetyRefinement.trans first second
    (by
      rintro ⟨pLeft, trLeft⟩ ⟨pRight, trRight⟩
        ⟨⟨pMiddle, trMiddle⟩, hFirst, hSecond⟩
      exact hFirst.trans hSecond)
    (by
      rintro ⟨pRight, trRight⟩ ⟨pLeft, trLeft⟩
        ⟨⟨pMiddle, trMiddle⟩, hSecond, hFirst⟩
      exact hSecond.trans hFirst)

/--
Along the forward direction of a trace equivalence, the stable event trace of
every finite run prefix is preserved.
-/
theorem eventsUpTo_eq {Party : Type u} {Event : Type w}
    {left right : Process.SafetySpec Party}
    {eventLeft : left.toProcess.EventMap Event}
    {eventRight : right.toProcess.EventMap Event}
    (equiv : Trace left right eventLeft eventRight)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    Process.Run.eventsUpTo eventLeft run n =
      Process.Run.eventsUpTo eventRight (equiv.forth.mapRun run hrel) n :=
  Refinement.SafetyRefinement.eventsUpTo_mapRun equiv.forth run hrel n

end Trace

namespace Ticket

/-- Ticket equivalence is reflexive for any fixed ticket map. -/
@[refl]
def refl {Party : Type u} {TicketTy : Type w}
    (system : Process.SafetySpec Party)
    (ticket : system.toProcess.Tickets TicketTy) : Ticket system system ticket ticket :=
  PFunctor.DynSystem.MutualSafetyRefinement.refl system
    (Observation.Process.StepRel.byTicket ticket ticket)
    (Observation.Process.StepRel.byTicket ticket ticket)
    (fun _ => rfl) (fun _ => rfl)

/-- Ticket equivalence is symmetric. -/
@[symm]
def symm {Party : Type u} {TicketTy : Type w}
    {left right : Process.SafetySpec Party}
    {ticketLeft : left.toProcess.Tickets TicketTy}
    {ticketRight : right.toProcess.Tickets TicketTy}
    (equiv : Ticket left right ticketLeft ticketRight) :
    Ticket right left ticketRight ticketLeft :=
  PFunctor.DynSystem.MutualSafetyRefinement.symm equiv

/-- Ticket equivalence is transitive through a shared middle ticket map. -/
@[trans]
def trans {Party : Type u} {TicketTy : Type w}
    {left middle right : Process.SafetySpec Party}
    {ticketLeft : left.toProcess.Tickets TicketTy}
    {ticketMiddle : middle.toProcess.Tickets TicketTy}
    {ticketRight : right.toProcess.Tickets TicketTy}
    (first : Ticket left middle ticketLeft ticketMiddle)
    (second : Ticket middle right ticketMiddle ticketRight) :
    Ticket left right ticketLeft ticketRight :=
  PFunctor.DynSystem.MutualSafetyRefinement.trans first second
    (by
      rintro ⟨pLeft, trLeft⟩ ⟨pRight, trRight⟩
        ⟨⟨pMiddle, trMiddle⟩, hFirst, hSecond⟩
      exact hFirst.trans hSecond)
    (by
      rintro ⟨pRight, trRight⟩ ⟨pLeft, trLeft⟩
        ⟨⟨pMiddle, trMiddle⟩, hSecond, hFirst⟩
      exact hSecond.trans hFirst)

/--
Along the forward direction of a ticket equivalence, the stable ticket
sequence of every finite run prefix is preserved.
-/
theorem ticketsUpTo_eq {Party : Type u} {TicketTy : Type w}
    {left right : Process.SafetySpec Party}
    {ticketLeft : left.toProcess.Tickets TicketTy}
    {ticketRight : right.toProcess.Tickets TicketTy}
    (equiv : Ticket left right ticketLeft ticketRight)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    Process.Run.ticketsUpTo ticketLeft run n =
      Process.Run.ticketsUpTo ticketRight (equiv.forth.mapRun run hrel) n :=
  Refinement.SafetyRefinement.ticketsUpTo_mapRun equiv.forth run hrel n

end Ticket

namespace Observation

/-- Observational equivalence for one party is reflexive. -/
@[refl]
def refl {Party : Type u} [DecidableEq Party] (me : Party)
    (system : Process.SafetySpec Party) : Observation me system system :=
  PFunctor.DynSystem.MutualSafetyRefinement.refl system
    (_root_.Interaction.Concurrent.Observation.Process.StepRel.byObservation me)
    (_root_.Interaction.Concurrent.Observation.Process.StepRel.byObservation me)
    (fun _ => rfl) (fun _ => rfl)

/-- Observational equivalence for one party is symmetric. -/
@[symm]
def symm {Party : Type u} [DecidableEq Party] (me : Party)
    {left right : Process.SafetySpec Party}
    (equiv : Observation me left right) : Observation me right left :=
  PFunctor.DynSystem.MutualSafetyRefinement.symm equiv

/-- Observational equivalence for one party is transitive. -/
@[trans]
def trans {Party : Type u} [DecidableEq Party] (me : Party)
    {left middle right : Process.SafetySpec Party}
    (first : Observation me left middle) (second : Observation me middle right) :
    Observation me left right :=
  PFunctor.DynSystem.MutualSafetyRefinement.trans first second
    (by
      rintro ⟨pLeft, trLeft⟩ ⟨pRight, trRight⟩
        ⟨⟨pMiddle, trMiddle⟩, hFirst, hSecond⟩
      exact hFirst.trans hSecond)
    (by
      rintro ⟨pRight, trRight⟩ ⟨pLeft, trLeft⟩
        ⟨⟨pMiddle, trMiddle⟩, hSecond, hFirst⟩
      exact hSecond.trans hFirst)

/--
Along the forward direction of an observational equivalence, the packed local
observations of the chosen party are preserved on every finite run prefix.
-/
theorem observationsUpTo_eq {Party : Type u} [DecidableEq Party]
    (me : Party)
    {left right : Process.SafetySpec Party}
    (equiv : Observation me left right)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    Observation.Process.Run.observationsUpTo me run n =
      Observation.Process.Run.observationsUpTo me (equiv.forth.mapRun run hrel) n :=
  Refinement.SafetyRefinement.observationsUpTo_mapRun me equiv.forth run hrel n

end Observation

end Equivalence
end Concurrent
end Interaction
