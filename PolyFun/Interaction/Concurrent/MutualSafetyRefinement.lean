/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Concurrent.Refinement

/-!
# MutualSafetyRefinement for dynamic concurrent processes

This file adds the symmetric refinement layer on top of
`Concurrent.Refinement.SafetyRefinement`.

`SafetyRefinement` is intentionally one-way: it shows that every behavior of
an implementation can be matched by some behavior of a specification. The
purpose of this file is to package the corresponding two-way notion. The two
directions may use independent state relations, so this is mutual refinement,
not coalgebraic bisimulation.

The construction is deliberately simple:

* a reverse refinement is the same relation viewed with the systems swapped;
* a mutual safety refinement packages one refinement in each direction; and
* once both directions are available, safety results can be transported either
  way, provided the chosen fairness assumptions also transfer.

The packagings themselves — `ReverseSafetyRefinement`,
`MutualSafetyRefinement`, and their `refl` / `symm` principles — are the generic
dynamical-system notions at the step polynomial. This file adds fairness-aware
safety-transport theorems phrased through `ProcessOver.SafetySpec.Satisfies`.
-/

universe u v w w₂ w₃

namespace Interaction
namespace Concurrent

namespace Refinement

/--
`ReverseSafetyRefinement impl spec matchStep` is the refinement from
`spec` to `impl`, with the transcript-matching relation reversed accordingly.

So "backward simulation" is only a change of viewpoint, not a second primitive
notion.
-/
abbrev ReverseSafetyRefinement
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    (impl : ProcessOver.SafetySpec Γ)
    (spec : ProcessOver.SafetySpec Δ)
    (matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess :=
        ProcessOver.TranscriptRel.top) :=
  PFunctor.DynSystem.ReverseSafetyRefinement impl spec matchStep

/--
`MutualSafetyRefinement left right matchForth matchBack` packages one safety
refinement in each direction between `left` and `right`.

By default, the backward transcript-matching relation is the reversal of the
forward one.

This is a process-level mutual-refinement witness: each side can match the
other's executions while preserving the chosen step relation.
-/
abbrev MutualSafetyRefinement
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    (left : ProcessOver.SafetySpec Γ)
    (right : ProcessOver.SafetySpec Δ)
    (matchForth :
      ProcessOver.TranscriptRel left.toProcess right.toProcess :=
        ProcessOver.TranscriptRel.top)
    (matchBack :
      ProcessOver.TranscriptRel right.toProcess left.toProcess :=
        ProcessOver.TranscriptRel.reverse matchForth) :=
  PFunctor.DynSystem.MutualSafetyRefinement left right matchForth matchBack

namespace MutualSafetyRefinement

/--
Transport safety from the right system to the left system under a mutual safety refinement,
assuming the chosen fairness predicates transfer along the forward direction.

This is the "use the right-hand system as the proof-oriented model" direction.
-/
theorem left_safe_of_satisfies
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver.SafetySpec Γ} {right : ProcessOver.SafetySpec Δ}
    {matchForth :
      ProcessOver.TranscriptRel left.toProcess right.toProcess}
    {matchBack :
      ProcessOver.TranscriptRel right.toProcess left.toProcess}
    (both : MutualSafetyRefinement left right matchForth matchBack)
    (fairLeft : ProcessOver.Run.Pred left.toProcess)
    (fairRight : ProcessOver.Run.Pred right.toProcess)
    (hfair :
      ∀ (run : ProcessOver.Run left.toProcess) {pRight : right.Proc},
        (hrel : both.forth.stateRel run.initial pRight) →
          fairLeft run → fairRight (both.forth.mapRun run hrel))
    (hright : ProcessOver.SafetySpec.Satisfies right fairRight
      (ProcessOver.SafetySpec.Safe right)) :
    ProcessOver.SafetySpec.Satisfies left fairLeft (ProcessOver.SafetySpec.Safe left) :=
  SafetyRefinement.safe_of_satisfies both.forth fairLeft fairRight hfair hright

/--
Transport safety from the left system to the right system under a both
safety refinement,
assuming the chosen fairness predicates transfer along the backward direction.

This is the same transport principle in the opposite direction.
-/
theorem right_safe_of_satisfies
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver.SafetySpec Γ} {right : ProcessOver.SafetySpec Δ}
    {matchForth :
      ProcessOver.TranscriptRel left.toProcess right.toProcess}
    {matchBack :
      ProcessOver.TranscriptRel right.toProcess left.toProcess}
    (both : MutualSafetyRefinement left right matchForth matchBack)
    (fairLeft : ProcessOver.Run.Pred left.toProcess)
    (fairRight : ProcessOver.Run.Pred right.toProcess)
    (hfair :
      ∀ (run : ProcessOver.Run right.toProcess) {pLeft : left.Proc},
        (hrel : both.back.stateRel run.initial pLeft) →
          fairRight run → fairLeft (both.back.mapRun run hrel))
    (hleft : ProcessOver.SafetySpec.Satisfies left fairLeft (ProcessOver.SafetySpec.Safe left)) :
    ProcessOver.SafetySpec.Satisfies right fairRight (ProcessOver.SafetySpec.Safe right) :=
  SafetyRefinement.safe_of_satisfies both.back fairRight fairLeft hfair hleft

/--
Safety under fairness assumptions is equivalent across a mutual safety refinement when the
fairness assumptions themselves transfer in both directions.

So once fairness transport is established, either side of a mutual safety refinement may be
used as the proof-oriented presentation of the protocol.
-/
theorem safe_iff_of_satisfies
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver.SafetySpec Γ} {right : ProcessOver.SafetySpec Δ}
    {matchForth :
      ProcessOver.TranscriptRel left.toProcess right.toProcess}
    {matchBack :
      ProcessOver.TranscriptRel right.toProcess left.toProcess}
    (both : MutualSafetyRefinement left right matchForth matchBack)
    (fairLeft : ProcessOver.Run.Pred left.toProcess)
    (fairRight : ProcessOver.Run.Pred right.toProcess)
    (hfairLeft :
      ∀ (run : ProcessOver.Run left.toProcess) {pRight : right.Proc},
        (hrel : both.forth.stateRel run.initial pRight) →
          fairLeft run → fairRight (both.forth.mapRun run hrel))
    (hfairRight :
      ∀ (run : ProcessOver.Run right.toProcess) {pLeft : left.Proc},
        (hrel : both.back.stateRel run.initial pLeft) →
          fairRight run → fairLeft (both.back.mapRun run hrel)) :
    ProcessOver.SafetySpec.Satisfies left fairLeft (ProcessOver.SafetySpec.Safe left) ↔
      ProcessOver.SafetySpec.Satisfies right fairRight (ProcessOver.SafetySpec.Safe right) := by
  constructor
  · exact right_safe_of_satisfies both fairLeft fairRight hfairRight
  · exact left_safe_of_satisfies both fairLeft fairRight hfairLeft

end MutualSafetyRefinement

end Refinement
end Concurrent
end Interaction
