/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Concurrent.Liveness
import PolyFun.Interaction.Concurrent.Observation
import PolyFun.PFunctor.Dynamical.Refinement

/-!
# Forward refinement for dynamic concurrent processes

The process-level refinement notion for the dynamic concurrent core:
`Refinement.SafetyRefinement` between two `ProcessOver.SafetySpec`s is the
generic dynamical-system forward simulation
`PFunctor.DynSystem.SafetyRefinement` at the step polynomial, with the
step-matching relation ranging over complete step transcripts
(`ProcessOver.TranscriptRel`).

It captures the usual implementation/specification picture:

* implementation and specification states are related by a simulation
  invariant;
* every admissible implementation start state can be matched by some
  specification start state;
* every concrete implementation step can be simulated by a specification step;
* the simulation may additionally insist that the two steps agree on events,
  tickets, controller data, or local observations; and
* safety obligations may be transferred from the specification side back to
  the implementation side.

The state-transport machinery — `matchDir`, `matchedState`, `mapRun`, and the
`stateRel_mapRun` / `match_mapRun` / `safe_of_mapRun` / `relUpTo_mapRun` /
`rel_mapRun` transport lemmas — lives at the generic layer and applies to
processes directly. This file adds the transcript-flavoured vocabulary
(`matchTranscript`), the admissibility form of assumption transport
(`admissible_mapRun`), the observation-preservation corollaries for the
concrete `TranscriptRel`s, and the top-level `safe_of_satisfies` transfer.
-/

universe u v w w₂ w₃

namespace Interaction
namespace Concurrent
namespace Refinement

/--
`SafetyRefinement impl spec matchStep` is a forward simulation from the
implementation system `impl` to the specification system `spec`: the generic
`PFunctor.DynSystem.SafetyRefinement` at the step polynomial.

The meaning is:

* every initial implementation state is related to some initial specification
  state;
* assumptions are preserved from implementation to specification;
* every implementation step transcript can be matched by some specification
  step transcript satisfying `matchStep`;
* related safe specification states imply safe implementation states.

The parameter `matchStep` determines what behavioral information the
simulation preserves at each step. Choosing different transcript relations
recovers event-preserving, ticket-preserving, controller-preserving, or
observation-preserving refinements.
-/
abbrev SafetyRefinement
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    (impl : ProcessOver.SafetySpec Γ)
    (spec : ProcessOver.SafetySpec Δ)
    (matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess :=
        ProcessOver.TranscriptRel.top) :=
  PFunctor.DynSystem.SafetyRefinement impl spec matchStep

namespace SafetyRefinement

/--
Choose the matching specification transcript for one implementation
transcript: the specification-side step selected by the simulation for the
given implementation step, as the generic `matchDir` read at the
step-polynomial interface.
-/
noncomputable abbrev matchTranscript
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.SafetySpec Γ} {spec : ProcessOver.SafetySpec Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : SafetyRefinement impl spec matchStep)
    {pImpl pSpec : _}
    (hrel : sim.stateRel pImpl pSpec)
    (trImpl : (impl.step pImpl).spec.Transcript) :
    (spec.step pSpec).spec.Transcript :=
  sim.matchDir hrel trImpl

/--
If an implementation run is admissible, then its mapped specification run is
also admissible.

So ambient assumptions are preserved along the run translation induced by the
simulation.
-/
theorem admissible_mapRun
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.SafetySpec Γ} {spec : ProcessOver.SafetySpec Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : SafetyRefinement impl spec matchStep)
    (run : ProcessOver.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec)
    (hadm : ProcessOver.SafetySpec.Admissible impl run) :
    ProcessOver.SafetySpec.Admissible spec (sim.mapRun run hrel) :=
  sim.assumptions_mapRun run hrel hadm

/-- A controller-preserving simulation preserves the current controller sequence
of every finite run prefix. -/
theorem currentControllersUpTo_mapRun {Party : Type u}
    {impl spec : Process.SafetySpec Party}
    (sim : SafetyRefinement impl spec Observation.Process.TranscriptRel.byController)
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) (n : Nat) :
    Process.Run.currentControllersUpTo run n =
      Process.Run.currentControllersUpTo (sim.mapRun run hrel) n :=
  Observation.Process.Run.currentControllersUpTo_eq_of_relUpTo_byController
    run (sim.mapRun run hrel)
    (Observation.Process.Run.relUpTo_of_pointwise
      Observation.Process.TranscriptRel.byController
      run (sim.mapRun run hrel) (sim.match_mapRun run hrel) n)

/-- A controller-path-preserving simulation preserves the controller-path
sequence of every finite run prefix. -/
theorem controllerPathsUpTo_mapRun {Party : Type u}
    {impl spec : Process.SafetySpec Party}
    (sim : SafetyRefinement impl spec Observation.Process.TranscriptRel.byPath)
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) (n : Nat) :
    Process.Run.controllerPathsUpTo run n =
      Process.Run.controllerPathsUpTo (sim.mapRun run hrel) n :=
  Observation.Process.Run.controllerPathsUpTo_eq_of_relUpTo_byPath
    run (sim.mapRun run hrel)
    (Observation.Process.Run.relUpTo_of_pointwise
      Observation.Process.TranscriptRel.byPath
      run (sim.mapRun run hrel) (sim.match_mapRun run hrel) n)

/-- An event-preserving simulation preserves the stable event sequence of every
finite run prefix. -/
theorem eventsUpTo_mapRun {Party : Type u}
    {impl spec : Process.SafetySpec Party} {Event : Type w}
    {eventImpl : impl.toProcess.EventMap Event}
    {eventSpec : spec.toProcess.EventMap Event}
    (sim : SafetyRefinement impl spec
      (Observation.Process.TranscriptRel.byEvent eventImpl eventSpec))
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) (n : Nat) :
    Process.Run.eventsUpTo eventImpl run n =
      Process.Run.eventsUpTo eventSpec (sim.mapRun run hrel) n :=
  Observation.Process.Run.eventsUpTo_eq_of_relUpTo_byEvent
    eventImpl eventSpec run (sim.mapRun run hrel)
    (Observation.Process.Run.relUpTo_of_pointwise
      (Observation.Process.TranscriptRel.byEvent eventImpl eventSpec)
      run (sim.mapRun run hrel) (sim.match_mapRun run hrel) n)

/-- A ticket-preserving simulation preserves the stable ticket sequence of every
finite run prefix. -/
theorem ticketsUpTo_mapRun {Party : Type u}
    {impl spec : Process.SafetySpec Party} {Ticket : Type w}
    {ticketImpl : impl.toProcess.Tickets Ticket}
    {ticketSpec : spec.toProcess.Tickets Ticket}
    (sim : SafetyRefinement impl spec
      (Observation.Process.TranscriptRel.byTicket ticketImpl ticketSpec))
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) (n : Nat) :
    Process.Run.ticketsUpTo ticketImpl run n =
      Process.Run.ticketsUpTo ticketSpec (sim.mapRun run hrel) n :=
  Observation.Process.Run.ticketsUpTo_eq_of_relUpTo_byTicket
    ticketImpl ticketSpec run (sim.mapRun run hrel)
    (Observation.Process.Run.relUpTo_of_pointwise
      (Observation.Process.TranscriptRel.byTicket ticketImpl ticketSpec)
      run (sim.mapRun run hrel) (sim.match_mapRun run hrel) n)

/-- An observation-preserving simulation preserves one party's packed
observations of every finite run prefix. -/
theorem observationsUpTo_mapRun {Party : Type u} [DecidableEq Party]
    (me : Party)
    {impl spec : Process.SafetySpec Party}
    (sim : SafetyRefinement impl spec
      (Observation.Process.TranscriptRel.byObservation me))
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) (n : Nat) :
    Observation.Process.Run.observationsUpTo me run n =
      Observation.Process.Run.observationsUpTo me (sim.mapRun run hrel) n :=
  Observation.Process.Run.observationsUpTo_eq_of_relUpTo_byObservation
    me run (sim.mapRun run hrel)
    (Observation.Process.Run.relUpTo_of_pointwise
      (Observation.Process.TranscriptRel.byObservation me)
      run (sim.mapRun run hrel) (sim.match_mapRun run hrel) n)

/--
If the specification system satisfies safety under some fairness assumption,
then the implementation system also satisfies safety under any implementation
fairness assumption that transfers along the simulation.

This is the top-level preservation theorem: once fairness is known to transfer,
forward simulation lets one discharge implementation-side safety obligations by
proving them on the specification side.
-/
theorem safe_of_satisfies
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.SafetySpec Γ} {spec : ProcessOver.SafetySpec Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : SafetyRefinement impl spec matchStep)
    (fairImpl : ProcessOver.Run.Pred impl.toProcess)
    (fairSpec : ProcessOver.Run.Pred spec.toProcess)
    (hfair :
      ∀ (run : ProcessOver.Run impl.toProcess) {pSpec : spec.Proc},
        (hrel : sim.stateRel run.initial pSpec) →
          fairImpl run → fairSpec (sim.mapRun run hrel))
    (hspec : ProcessOver.SafetySpec.Satisfies spec fairSpec (ProcessOver.SafetySpec.Safe spec)) :
    ProcessOver.SafetySpec.Satisfies impl fairImpl (ProcessOver.SafetySpec.Safe impl) := by
  intro run hInit hAdm hFair
  rcases sim.init run.initial hInit with ⟨pSpec, hInitSpec, hrel⟩
  have hAdmSpec : ProcessOver.SafetySpec.Admissible spec (sim.mapRun run hrel) :=
    admissible_mapRun sim run hrel hAdm
  have hSafeSpec : ProcessOver.SafetySpec.Safe spec (sim.mapRun run hrel) :=
    hspec (sim.mapRun run hrel) hInitSpec hAdmSpec (hfair run hrel hFair)
  exact sim.safe_of_mapRun run hrel hSafeSpec

end SafetyRefinement

end Refinement
end Concurrent
end Interaction
