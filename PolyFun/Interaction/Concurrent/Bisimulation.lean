/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Concurrent.Refinement

/-!
# Bisimulation for dynamic concurrent processes

This file adds the symmetric refinement layer on top of
`Concurrent.Refinement.ForwardSimulation`.

`ForwardSimulation` is intentionally one-way: it shows that every behavior of
an implementation can be matched by some behavior of a specification. The
purpose of this file is to package the corresponding two-way notion used when
two systems should count as behaviorally equivalent rather than merely
implementing one another.

The construction is deliberately simple:

* a backward simulation is just a forward simulation with the two systems
  swapped;
* a bisimulation packages one simulation in each direction; and
* once both directions are available, safety results can be transported either
  way, provided the chosen fairness assumptions also transfer.

The packagings themselves — `BackwardSimulation`, `Bisimulation`, and their
`refl` / `symm` principles — are the generic dynamical-system notions
(`PFunctor.DynSystem.BackwardSimulation` / `Bisimulation`) at the step
polynomial; this file adds the fairness-aware safety-transport theorems phrased
through `ProcessOver.System.Satisfies`.
-/

universe u v w w₂ w₃

namespace Interaction
namespace Concurrent

namespace Refinement

/--
`BackwardSimulation impl spec matchStep` is just a forward simulation from
`spec` to `impl`, with the transcript-matching relation reversed accordingly.

So "backward simulation" is only a change of viewpoint, not a second primitive
notion.
-/
abbrev BackwardSimulation
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    (impl : ProcessOver.System Γ)
    (spec : ProcessOver.System Δ)
    (matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess :=
        ProcessOver.TranscriptRel.top) :=
  PFunctor.DynSystem.BackwardSimulation impl spec matchStep

/--
`Bisimulation left right matchForth matchBack` packages one forward simulation
in each direction between `left` and `right`.

By default, the backward transcript-matching relation is the reversal of the
forward one.

This is the library's main process-level equivalence witness: each side can
match the other's executions while preserving the chosen step relation.
-/
abbrev Bisimulation
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    (left : ProcessOver.System Γ)
    (right : ProcessOver.System Δ)
    (matchForth :
      ProcessOver.TranscriptRel left.toProcess right.toProcess :=
        ProcessOver.TranscriptRel.top)
    (matchBack :
      ProcessOver.TranscriptRel right.toProcess left.toProcess :=
        ProcessOver.TranscriptRel.reverse matchForth) :=
  PFunctor.DynSystem.Bisimulation left right matchForth matchBack

namespace Bisimulation

/--
Transport safety from the right system to the left system under a bisimulation,
assuming the chosen fairness predicates transfer along the forward direction.

This is the "use the right-hand system as the proof-oriented model" direction.
-/
theorem left_safe_of_satisfies
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver.System Γ} {right : ProcessOver.System Δ}
    {matchForth :
      ProcessOver.TranscriptRel left.toProcess right.toProcess}
    {matchBack :
      ProcessOver.TranscriptRel right.toProcess left.toProcess}
    (bisim : Bisimulation left right matchForth matchBack)
    (fairLeft : ProcessOver.Run.Pred left.toProcess)
    (fairRight : ProcessOver.Run.Pred right.toProcess)
    (hfair :
      ∀ (run : ProcessOver.Run left.toProcess) {pRight : right.Proc},
        (hrel : bisim.forth.stateRel run.initial pRight) →
          fairLeft run → fairRight (bisim.forth.mapRun run hrel))
    (hright : ProcessOver.System.Satisfies right fairRight (ProcessOver.System.Safe right)) :
    ProcessOver.System.Satisfies left fairLeft (ProcessOver.System.Safe left) :=
  ForwardSimulation.safe_of_satisfies bisim.forth fairLeft fairRight hfair hright

/--
Transport safety from the left system to the right system under a bisimulation,
assuming the chosen fairness predicates transfer along the backward direction.

This is the same transport principle in the opposite direction.
-/
theorem right_safe_of_satisfies
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver.System Γ} {right : ProcessOver.System Δ}
    {matchForth :
      ProcessOver.TranscriptRel left.toProcess right.toProcess}
    {matchBack :
      ProcessOver.TranscriptRel right.toProcess left.toProcess}
    (bisim : Bisimulation left right matchForth matchBack)
    (fairLeft : ProcessOver.Run.Pred left.toProcess)
    (fairRight : ProcessOver.Run.Pred right.toProcess)
    (hfair :
      ∀ (run : ProcessOver.Run right.toProcess) {pLeft : left.Proc},
        (hrel : bisim.back.stateRel run.initial pLeft) →
          fairRight run → fairLeft (bisim.back.mapRun run hrel))
    (hleft : ProcessOver.System.Satisfies left fairLeft (ProcessOver.System.Safe left)) :
    ProcessOver.System.Satisfies right fairRight (ProcessOver.System.Safe right) :=
  ForwardSimulation.safe_of_satisfies bisim.back fairRight fairLeft hfair hleft

/--
Safety under fairness assumptions is equivalent across a bisimulation when the
fairness assumptions themselves transfer in both directions.

So once fairness transport is established, either side of a bisimulation may be
used as the proof-oriented presentation of the protocol.
-/
theorem safe_iff_of_satisfies
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver.System Γ} {right : ProcessOver.System Δ}
    {matchForth :
      ProcessOver.TranscriptRel left.toProcess right.toProcess}
    {matchBack :
      ProcessOver.TranscriptRel right.toProcess left.toProcess}
    (bisim : Bisimulation left right matchForth matchBack)
    (fairLeft : ProcessOver.Run.Pred left.toProcess)
    (fairRight : ProcessOver.Run.Pred right.toProcess)
    (hfairLeft :
      ∀ (run : ProcessOver.Run left.toProcess) {pRight : right.Proc},
        (hrel : bisim.forth.stateRel run.initial pRight) →
          fairLeft run → fairRight (bisim.forth.mapRun run hrel))
    (hfairRight :
      ∀ (run : ProcessOver.Run right.toProcess) {pLeft : left.Proc},
        (hrel : bisim.back.stateRel run.initial pLeft) →
          fairRight run → fairLeft (bisim.back.mapRun run hrel)) :
    ProcessOver.System.Satisfies left fairLeft (ProcessOver.System.Safe left) ↔
      ProcessOver.System.Satisfies right fairRight (ProcessOver.System.Safe right) := by
  constructor
  · exact right_safe_of_satisfies bisim fairLeft fairRight hfairRight
  · exact left_safe_of_satisfies bisim fairLeft fairRight hfairLeft

end Bisimulation

end Refinement
end Concurrent
end Interaction
