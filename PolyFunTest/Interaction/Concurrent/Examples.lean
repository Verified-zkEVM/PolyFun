/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Concurrent.Execution
import PolyFun.Interaction.Concurrent.Equivalence
import PolyFun.Interaction.Concurrent.Fairness
import PolyFun.Interaction.Concurrent.Interleaving
import PolyFun.Interaction.Concurrent.Independence
import PolyFun.Interaction.Concurrent.Liveness
import PolyFun.Interaction.Concurrent.Observation
import PolyFun.Interaction.Concurrent.Policy
import PolyFun.Interaction.Concurrent.Refinement
import PolyFun.Interaction.Concurrent.Run
import PolyFun.Interaction.Concurrent.Tree
import PolyFun.Interaction.Concurrent.Machine

/-!
# Concurrent interaction examples

This file gives small definitional examples for the current concurrent layer.

The examples are intentionally focused on:

* binary structural parallelism;
* frontier events and residuals;
* per-party observation profiles over concurrently live components.
* scheduler ownership versus atomic payload ownership;
* the combined current local view of the next frontier event.
* process executions, controller paths, and observed local traces.
* interleaving equivalence under commuting independent steps.
* executable scheduler and controller policies over finite traces.

They are meant to exercise the current expressivity surface before later layers
such as fairness or richer execution semantics are added.
-/

universe u

namespace Interaction
namespace Concurrent
namespace Examples

/-- Three parties for the toy concurrent examples: two honest parties and a
network adversary. -/
inductive Party where
  | alice
  | bob
  | adv

deriving instance DecidableEq for Party

/-- One atomic message-delivery step whose payload is a pair of a public header
and a private payload bit. -/
def delivery : Spec :=
  .node (Nat × Bool) (fun _ => .done)

/-- A profile where Alice originates the payload, Bob sees the whole message,
and the adversary sees only the public header. -/
def deliveryProfile : Profile Party delivery :=
  .node (fun
      | .alice => .pick
      | .bob => .observe
      | .adv => .react ⟨Nat, Prod.fst⟩)
    (fun _ => .done)

example : Profile.ObsType Party.alice deliveryProfile = (Nat × Bool) := rfl

example : Profile.ObsType Party.bob deliveryProfile = (Nat × Bool) := rfl

example : Profile.ObsType Party.adv deliveryProfile = Nat := rfl

example :
    Profile.observe Party.adv deliveryProfile (.move (3, true)) = (3 : Nat) := rfl

/-- A second atomic node that only Bob fully observes, while the adversary
learns nothing. -/
def ack : Spec :=
  .node Bool (fun _ => .done)

/-- Local observations for the acknowledgement node. -/
def ackProfile : Profile Party ack :=
  .node (fun
      | .alice => .hidden
      | .bob => .observe
      | .adv => .hidden)
    (fun _ => .done)

/-- A concurrent system where delivery and acknowledgement are both live. -/
def inFlight : Spec :=
  .par delivery ack

/-- The corresponding concurrent observation profile. -/
def inFlightProfile : Profile Party inFlight :=
  .par deliveryProfile ackProfile

/-- Control ownership for the delivery step: Alice chooses the payload. -/
def deliveryControl : Control Party delivery :=
  .node .alice (fun _ => .done)

/-- Control ownership for the acknowledgement step: Bob chooses the bit. -/
def ackControl : Control Party ack :=
  .node .bob (fun _ => .done)

/-- The adversary controls scheduling between the two concurrently live
subsystems, while Alice and Bob still control their respective atomic nodes. -/
def inFlightControl : Control Party inFlight :=
  .par .adv deliveryControl ackControl

example :
    Profile.ObsType Party.adv inFlightProfile = Sum Nat PUnit := rfl

example :
    Profile.ObsType Party.bob inFlightProfile = Sum (Nat × Bool) Bool := rfl

example :
    Profile.observe Party.adv inFlightProfile (.left (.move (5, false))) =
      (Sum.inl (α := Nat) (β := PUnit) 5) := rfl

example :
    Profile.observe Party.adv inFlightProfile (.right (.move true)) = Sum.inr PUnit.unit := rfl

example :
    Profile.residual inFlightProfile (.left (.move (7, true))) = .par .done ackProfile := rfl

example :
    Profile.residual inFlightProfile (.right (.move false)) = .par deliveryProfile .done := rfl

example : Control.scheduler? inFlightControl = some .adv := rfl

example : Control.current? inFlightControl = some .adv := rfl

example :
    Control.controllers inFlightControl (.left (.move (5, false))) = [.adv, .alice] := rfl

example :
    Control.controllers inFlightControl (.right (.move true)) = [.adv, .bob] := rfl

def afterDelivery : Control Party (.par .done ack) :=
  Control.residual inFlightControl (.left (.move (7, true)))

example : Control.scheduler? afterDelivery = none := rfl

example : Control.current? afterDelivery = some .bob := rfl

example : Control.controllers afterDelivery (.right (.move false)) = [.bob] := rfl

example : Current.controller? inFlightControl = some .adv := rfl

example : Current.scheduler? inFlightControl = some .adv := rfl

example :
    Current.view Party.adv inFlightControl inFlightProfile = Multiparty.ViewMode.pick := by
  rfl

example :
    Current.observe Party.adv inFlightControl inFlightProfile
      (Front.left (.move (5, false))) =
      (Front.left (.move (5, false))) := rfl

example :
    Current.observe Party.alice inFlightControl inFlightProfile (.left (.move (5, false))) =
      (show PLift (Sum (Nat × Bool) PUnit) from ⟨Sum.inl (5, false)⟩) := rfl

example :
    Current.observe Party.bob inFlightControl inFlightProfile (.right (.move true)) =
      (show PLift (Sum (Nat × Bool) Bool) from ⟨Sum.inr true⟩) := rfl

def afterDeliveryProfile : Profile Party (.par .done ack) :=
  Profile.residual inFlightProfile (.left (.move (7, true)))

example : Current.controller? afterDelivery = some .bob := rfl

example : Current.scheduler? afterDelivery = none := rfl

example :
    Current.view Party.bob afterDelivery afterDeliveryProfile = Multiparty.ViewMode.pick := by
  rfl

example :
    Current.view Party.adv afterDelivery afterDeliveryProfile = Multiparty.ViewMode.hidden := by
  rfl

example :
    Current.observe Party.adv afterDelivery afterDeliveryProfile (.right (.move false)) =
      PUnit.unit := rfl

/-- A concrete structural trace where the adversary schedules delivery first and the
remaining acknowledgement second. -/
def deliveryThenAck : Trace inFlight :=
  .step (.left (.move (7, true)))
    (.step (.right (.move false)) (Trace.doneOfNotLive rfl))

/-- The dynamic process compiled from the structural tree frontend. -/
def inFlightProcess : Process (Tree.State Party) Party :=
  Tree.toProcess (Party := Party)

/-- The packaged initial structural state of the in-flight system. -/
def inFlightState : Tree.State Party :=
  Tree.init inFlightControl inFlightProfile

/-- The process execution induced by `deliveryThenAck`. -/
def deliveryThenAckExec :
    Process.Trace inFlightProcess inFlightState :=
  Tree.ofLinearization inFlightControl inFlightProfile deliveryThenAck

example :
    Process.Trace.currentControllers deliveryThenAckExec = [some .adv, some .bob] := rfl

example :
    Process.Trace.controllerPaths deliveryThenAckExec = [[.adv, .alice], [.bob]] := rfl

example :
    (Step.observe Party.adv inFlightState.currentStep
      (inFlightState.transcriptOfEvent (.left (.move (7, true))))).length = 1 := rfl

def afterDeliveryState : Tree.State Party :=
  Tree.init afterDelivery afterDeliveryProfile

example :
    (Step.observe Party.alice inFlightState.currentStep
      (inFlightState.transcriptOfEvent (.left (.move (7, true))))).length = 1 := rfl

example :
    ((Step.observe Party.bob afterDeliveryState.currentStep
      (afterDeliveryState.transcriptOfEvent (.right (.move false)))).length = 1) := rfl

example :
    (Process.ObservedTrace.ofTrace Party.bob inFlightProcess deliveryThenAckExec).length =
      2 := rfl

/-- A concrete structural trace where the adversary schedules the acknowledgement before
the delivery event. -/
def ackThenDelivery : Trace inFlight :=
  .step (.right (.move true))
    (.step (.left (.move (9, false))) (Trace.doneOfNotLive rfl))

def afterAck : Control Party (.par delivery .done) :=
  Control.residual inFlightControl (.right (.move true))

def afterAckProfile : Profile Party (.par delivery .done) :=
  Profile.residual inFlightProfile (.right (.move true))

/-- The process execution induced by `ackThenDelivery`. -/
def ackThenDeliveryExec :
    Process.Trace inFlightProcess inFlightState :=
  Tree.ofLinearization inFlightControl inFlightProfile ackThenDelivery

example :
    Process.Trace.currentControllers ackThenDeliveryExec = [some .adv, some .alice] := rfl

example :
    Process.Trace.controllerPaths ackThenDeliveryExec = [[.adv, .bob], [.alice]] := rfl

example :
    ((Step.observe Party.adv inFlightState.currentStep
      (inFlightState.transcriptOfEvent (.right (.move true)))).length = 1) := rfl

def afterAckState : Tree.State Party :=
  Tree.init afterAck afterAckProfile

example :
    (Step.observe Party.adv afterAckState.currentStep
      (afterAckState.transcriptOfEvent (.left (.move (9, false))))).length = 1 := rfl

def deliveryEvent : Front inFlight :=
  .left (.move (4, true))

def ackEvent : Front inFlight :=
  .right (.move false)

def leftThenRight : Trace inFlight :=
  .step deliveryEvent
    (.step (Independent.afterLeft (Independent.left_right (.move (4, true)) (.move false)))
      (Trace.doneOfNotLive rfl))

def rightThenLeft : Trace inFlight :=
  .step ackEvent
    (.step (Independent.afterRight (Independent.left_right (.move (4, true)) (.move false)))
      (Trace.doneOfNotLive rfl))

example : Trace.Equiv leftThenRight rightThenLeft :=
  .swap (Independent.left_right (.move (4, true)) (.move false)) (Trace.doneOfNotLive rfl)

example :
    Trace.Equiv.length_eq
      (.swap (Independent.left_right (.move (4, true)) (.move false)) (Trace.doneOfNotLive rfl) :
        Trace.Equiv leftThenRight rightThenLeft) = rfl := rfl

/-- When both sides of a live `par` are available, prefer the left branch. -/
def preferLeft : Process.StepPolicy inFlightProcess :=
  fun {p} tr =>
    match p with
    | ⟨.par _ _, .par _ leftControl rightControl, _⟩ =>
        match tr with
        | ⟨event, _⟩ =>
            match leftControl.isLive, rightControl.isLive, event with
            | true, true, .left _ => true
            | true, true, .right _ => false
            | _, _, _ => true
    | _ => true

/-- When both sides of a live `par` are available, prefer the right branch. -/
def preferRight : Process.StepPolicy inFlightProcess :=
  fun {p} tr =>
    match p with
    | ⟨.par _ _, .par _ leftControl rightControl, _⟩ =>
        match tr with
        | ⟨event, _⟩ =>
            match leftControl.isLive, rightControl.isLive, event with
            | true, true, .left _ => false
            | true, true, .right _ => true
            | _, _, _ => true
    | _ => true

example : Process.Trace.respects preferLeft deliveryThenAckExec = true := rfl

example : Process.Trace.respects preferLeft ackThenDeliveryExec = false := rfl

example : Process.Trace.respects preferRight ackThenDeliveryExec = true := rfl

example : Process.Trace.respects preferRight deliveryThenAckExec = false := rfl

example :
    Process.Trace.respects (Process.StepPolicy.byController (fun | .adv => true | _ => false))
      deliveryThenAckExec = false := rfl

example :
    Process.Trace.respects (Process.StepPolicy.byController (fun | .bob => false | _ => true))
      deliveryThenAckExec = false := rfl

example :
    Process.Trace.respects (Process.StepPolicy.byController (fun | .bob => false | _ => true))
      ackThenDeliveryExec = true := rfl

/-- A three-way concurrent system used to illustrate recursive independence
inside one branch of a larger parallel spec. -/
def threeWay : Spec :=
  .par delivery (.par ack ack)

example :
    Independent
      (Front.left (right := ack) (.move (4, true)) : Front inFlight)
      (Front.right (left := delivery) (.move false)) :=
  .left_right (.move (4, true)) (.move false)

example :
    Independent.afterLeft
      (Independent.left_right
        (left := delivery) (right := ack) (.move (4, true)) (.move false)) =
      Front.right (.move false) := rfl

example :
    Independent.afterRight
      (Independent.left_right
        (left := delivery) (right := ack) (.move (4, true)) (.move false)) =
      Front.left (.move (4, true)) := rfl

example :
    Independent.diamond
      (Independent.left_right
        (left := delivery) (right := ack) (.move (4, true)) (.move false)) = rfl := rfl

example :
    Independent
      (Front.right (left := delivery) (Front.left (.move true)) : Front threeWay)
      (Front.right (left := delivery) (Front.right (.move false))) :=
  .right (.left_right (.move true) (.move false))

example :
    Independent.diamond
      (.right
        (Independent.left_right
          (left := ack) (right := ack) (.move true) (.move false)) :
        Independent
          (Front.right (left := delivery) (Front.left (.move true)) : Front threeWay)
          (Front.right (left := delivery) (Front.right (.move false)))) = rfl := rfl

section PhaseOneExamples

/-- Node semantics for a tiny looping process:
the adversary actively chooses the boolean step, Bob observes it, and Alice is
hidden from it. -/
def loopNode : NodeProfile Party Bool where
  controllers := fun _ => [.adv]
  views
    | .adv => .pick
    | .bob => .observe
    | .alice => .hidden

/-- A tiny one-state looping process used to exercise runs, tickets, fairness,
and refinement. -/
def loopProcess : Process PUnit Party :=
  ProcessOver.ofStep PUnit fun _ =>
    { spec := .node Bool (fun _ => .done)
      semantics := ⟨loopNode, fun _ => PUnit.unit⟩
      next := fun _ => PUnit.unit }

/-- A ticketed view of `loopProcess` using the chosen boolean as the stable
ticket. -/
def loopTicketed : Process.Ticketed Party where
  State := PUnit
  toDynSystem := loopProcess
  Ticket := Bool
  ticket := fun _ tr =>
    match tr with
    | ⟨b, _⟩ => b

/-- A simple always-true infinite run of `loopProcess`. -/
def trueRun : Process.Run loopProcess where
  state _ := PUnit.unit
  dir _ := ⟨true, PUnit.unit⟩
  next_state _ := rfl

example : Process.Run.initial trueRun = PUnit.unit := rfl

example :
    Process.Run.ticketsUpTo loopTicketed.ticket trueRun 3 = [true, true, true] := by
  simp only [ProcessOver.Run.ticketsUpTo_succ, ProcessOver.Run.ticketsUpTo_zero,
    PFunctor.DynSystem.Run.ticket, PFunctor.DynSystem.Run.tail, loopTicketed, trueRun]

example :
    (Observation.Process.Run.observationsUpTo Party.adv trueRun 2).length = 2 := rfl

example :
    (Observation.Process.Run.observationsUpTo Party.bob trueRun 2).length = 2 := rfl

example :
    Process.Ticketed.firedAt loopTicketed trueRun true 5 := by
  simp [ProcessOver.Ticketed.firedAt, loopTicketed, trueRun]

example :
    Process.Ticketed.enabledAt loopTicketed trueRun true 7 := by
  refine ⟨⟨true, PUnit.unit⟩, ?_⟩
  simp [loopTicketed]

example :
    Process.Ticketed.WeakFairOn loopTicketed trueRun true := by
  intro _ N
  refine ⟨N, Nat.le_refl _, ?_⟩
  simp [ProcessOver.Ticketed.firedAt, loopTicketed, trueRun]

example :
    Process.Ticketed.StrongFairOn loopTicketed trueRun true := by
  intro _ N
  refine ⟨N, Nat.le_refl _, ?_⟩
  simp [ProcessOver.Ticketed.firedAt, loopTicketed, trueRun]

/-- A trivial system wrapper around `loopProcess`. -/
def loopSystem : Process.SafetySpec Party where
  State := PUnit
  toDynSystem := loopProcess
  init _ := True
  assumptions _ := True
  safe _ := True

/-- The identity simulation on `loopSystem`, preserving the boolean ticket. -/
def loopSim :
    Refinement.SafetyRefinement loopSystem loopSystem
      (Observation.Process.TranscriptRel.byTicket
        loopTicketed.ticket loopTicketed.ticket) where
  stateRel _ _ := True
  init p hp := ⟨p, hp, trivial⟩
  assumptions _ _ := trivial
  step _
    | ⟨b, tail⟩ => ⟨⟨b, tail⟩, rfl, trivial⟩
  safe _ _ := trivial

/-- The specification-side run obtained by matching `trueRun` through
`loopSim`. -/
noncomputable def loopMappedRun : Process.Run loopSystem.toProcess :=
  loopSim.mapRun (stSpec := PUnit.unit) trueRun trivial

/-- The identity simulation on `loopSystem`, preserving Bob's local
observations. -/
def loopObsSimBob :
    Refinement.SafetyRefinement loopSystem loopSystem
      (Observation.Process.TranscriptRel.byObservation Party.bob) where
  stateRel _ _ := True
  init p hp := ⟨p, hp, trivial⟩
  assumptions _ _ := trivial
  step _
    | ⟨b, tail⟩ => ⟨⟨b, tail⟩, rfl, trivial⟩
  safe _ _ := trivial

/-- The specification-side run obtained by matching `trueRun` through
`loopObsSimBob`. -/
noncomputable def loopObsMappedRunBob : Process.Run loopSystem.toProcess :=
  loopObsSimBob.mapRun (stSpec := PUnit.unit) trueRun trivial

/-- The identity ticket mutual safety refinement on `loopSystem`. -/
def loopTicketMutual :
    Refinement.MutualSafetyRefinement loopSystem loopSystem
      (Observation.Process.TranscriptRel.byTicket
        loopTicketed.ticket loopTicketed.ticket)
      (Observation.Process.TranscriptRel.byTicket
        loopTicketed.ticket loopTicketed.ticket) where
  forth := loopSim
  back := loopSim

/-- The identity observational mutual safety refinement on `loopSystem` for Bob. -/
def loopObsMutualBob :
    Refinement.MutualSafetyRefinement loopSystem loopSystem
      (Observation.Process.TranscriptRel.byObservation Party.bob)
      (Observation.Process.TranscriptRel.byObservation Party.bob) where
  forth := loopObsSimBob
  back := loopObsSimBob

/-! The standard two-way comparisons expose actual equivalence operations. -/

example : Equivalence.Controller loopSystem loopSystem :=
  (Equivalence.Controller.refl loopSystem).trans
    (Equivalence.Controller.refl loopSystem)

example : Equivalence.ControllerPath loopSystem loopSystem :=
  (Equivalence.ControllerPath.refl loopSystem).symm

example : Equivalence.Trace loopSystem loopSystem
    loopTicketed.ticket loopTicketed.ticket :=
  (Equivalence.Trace.refl loopSystem loopTicketed.ticket).trans
    (Equivalence.Trace.refl loopSystem loopTicketed.ticket)

example : Equivalence.Ticket loopSystem loopSystem
    loopTicketed.ticket loopTicketed.ticket :=
  (Equivalence.Ticket.refl loopSystem loopTicketed.ticket).symm

example : Equivalence.Observation Party.bob loopSystem loopSystem :=
  Equivalence.Observation.trans Party.bob
    (Equivalence.Observation.refl Party.bob loopSystem)
    (Equivalence.Observation.refl Party.bob loopSystem)

example : loopMappedRun.state 4 = PUnit.unit := rfl

example :
    Observation.Process.TranscriptRel.byTicket loopTicketed.ticket loopTicketed.ticket
      ⟨trueRun.state 3, trueRun.transcript 3⟩
      ⟨loopMappedRun.state 3, loopMappedRun.transcript 3⟩ := by
  exact loopSim.match_mapRun (stSpec := PUnit.unit) trueRun trivial 3

example : Process.SafetySpec.Safe loopSystem loopMappedRun := by
  intro _
  trivial

example :
    Process.SafetySpec.Satisfies loopSystem (fun _ => True)
      (Process.SafetySpec.Safe loopSystem) := by
  intro run _ _ _ n
  trivial

example :
    Process.SafetySpec.Satisfies loopSystem (fun _ => True)
      (Process.SafetySpec.Safe loopSystem) := by
  apply Refinement.SafetyRefinement.safe_of_satisfies loopSim
    (fairImpl := fun _ => True) (fairSpec := fun _ => True)
  · intro _ _ _
    trivial
  · intro run _ _ _ n
    trivial

example :
    Process.Run.ticketsUpTo loopTicketed.ticket trueRun 4 =
      Process.Run.ticketsUpTo loopTicketed.ticket loopMappedRun 4 := by
  exact Refinement.SafetyRefinement.ticketsUpTo_mapRun loopSim
    (pSpec := PUnit.unit) trueRun trivial 4

example :
    Observation.Process.Run.observationsUpTo Party.bob trueRun 3 =
      Observation.Process.Run.observationsUpTo Party.bob loopObsMappedRunBob 3 := by
  exact Refinement.SafetyRefinement.observationsUpTo_mapRun Party.bob loopObsSimBob
    (pSpec := PUnit.unit) trueRun trivial 3

example :
    Observation.Process.Run.Rel
      (Observation.Process.TranscriptRel.byTicket loopTicketed.ticket loopTicketed.ticket)
      trueRun loopMappedRun := by
  exact Observation.Process.Run.rel_of_pointwise
    (Observation.Process.TranscriptRel.byTicket loopTicketed.ticket loopTicketed.ticket)
    trueRun loopMappedRun
    (loopSim.match_mapRun (stSpec := PUnit.unit) trueRun trivial)

example :
    Process.Run.ticketsUpTo loopTicketed.ticket trueRun 5 =
      Process.Run.ticketsUpTo loopTicketed.ticket
        (loopTicketMutual.forth.mapRun trueRun (stSpec := PUnit.unit) trivial) 5 := by
  exact Equivalence.Ticket.ticketsUpTo_eq loopTicketMutual trueRun
    (pRight := PUnit.unit) trivial 5

example :
    Observation.Process.Run.observationsUpTo Party.bob trueRun 4 =
      Observation.Process.Run.observationsUpTo Party.bob
        (loopObsMutualBob.forth.mapRun trueRun (stSpec := PUnit.unit) trivial) 4 := by
  exact Equivalence.Observation.observationsUpTo_eq Party.bob loopObsMutualBob
    trueRun (pRight := PUnit.unit) trivial 4

example :
    Process.SafetySpec.Satisfies loopSystem (fun _ => True)
      (Process.SafetySpec.Safe loopSystem) := by
  exact
    (Refinement.MutualSafetyRefinement.safe_iff_of_satisfies loopTicketMutual
      (fairLeft := fun _ => True) (fairRight := fun _ => True)
      (hfairLeft := by
        intro _ _ _ _
        trivial)
      (hfairRight := by
        intro _ _ _ _
        trivial)).mp
      (by
        intro run _ _ _ n
        trivial)

end PhaseOneExamples

section MachineExamples

/-! ## Flat machines as dynamical systems

`Machine` is `PFunctor.DynSystem PFunctor.univ`, so the classical vocabulary
(`mk'`, `Enabled`, `step`) coexists with the whole dynamical-system toolkit
(`out`, `ObsEq`, `SafetySpec`, …) via dot notation through the abbrev. -/

/-- A counter machine via the classical constructor: at every state a boolean
event is enabled — `true` increments, `false` stays. -/
def counterMachine : Machine ℕ :=
  Machine.mk' ℕ (fun _ => Bool) (fun n b => if b then n + 1 else n)

example : counterMachine.step (3 : ℕ) true = (4 : ℕ) := rfl

example : counterMachine.Enabled (3 : ℕ) = Bool := rfl

/-- The generic coalgebra structure map applies to machines directly. -/
example : counterMachine.out (3 : ℕ) = ⟨Bool, fun b => if b then (4 : ℕ) else (3 : ℕ)⟩ := rfl

/-- Observational equivalence of machine states. -/
example : PFunctor.DynSystem.ObsEq counterMachine counterMachine (3 : ℕ) (3 : ℕ) := rfl

/-- A machine system with verification predicates, using the generic bundle. -/
def counterSystem : Machine.SafetySpec where
  State := ℕ
  toDynSystem := counterMachine
  init := fun (n : ℕ) => n = 0

example : counterSystem.init (0 : ℕ) := rfl

example : counterSystem.safe (5 : ℕ) := trivial

example : counterSystem.toMachine = counterMachine := rfl

/-- Node semantics for compiling the counter machine into a process. -/
def counterProfile :
    (σ : ℕ) → NodeProfile Party (counterMachine.Enabled σ) :=
  fun _ => { controllers := fun _ => [.adv], views := fun _ => .observe }

/-- The one-node-step process compiled from the counter machine. -/
def counterProcess : Process ℕ Party := counterMachine.toProcess counterProfile

example :
    (counterProcess.step (3 : ℕ)).spec
      = .node (counterMachine.Enabled (3 : ℕ)) (fun _ => .done) := rfl

example : (counterProcess.step (3 : ℕ)).next ⟨true, PUnit.unit⟩ = (4 : ℕ) := rfl

end MachineExamples

end Examples
end Concurrent
end Interaction
