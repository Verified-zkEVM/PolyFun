/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all PolyFun.Interaction.UC.OpenProcessSamplerFactorization
import all PolyFun.Interaction.UC.Scheduler
public import PolyFun.Interaction.UC.OpenProcessSamplerFactorization
public import PolyFun.Interaction.UC.Scheduler

/-!
# Path-sampler factorization for mass-aware scheduling

The structural UC factorization maps already identify the leaves of the
source and reassociated binary process trees. This module proves the missing
sampler statement for the mass-aware scheduler: after applying those path
maps, both hierarchical samplers bind the same component sampler whenever the
binary scheduler satisfies `BinaryScheduler.IsCoherent`.

This is the generic bridge between the scheduler algebra and process-level UC
factorization. It remains independent of probability; downstream models only
need to prove the scheduler coherence law for their observation relation.
-/

public section

universe w w'

namespace Interaction
namespace UC

open Concurrent OpenProcessFactorization

namespace BinaryScheduler

/-- Binding the source-shaped mass-aware draw against a continuation exposes
the two scheduler calls used by the nested process sampler. -/
theorem sourceDraw_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (scheduler : BinaryScheduler m) (first second context : ScheduleMass)
    {α : Type w} (h : ULift.{w, 0} Leaf → m α) :
    sourceDraw scheduler first second context >>= h =
      scheduler (first + second) context >>= fun outer =>
        if outer.down then
          scheduler first second >>= fun inner =>
            if inner.down then h ⟨.first⟩ else h ⟨.second⟩
        else
          h ⟨.context⟩ := by
  simp only [sourceDraw, bind_assoc]
  refine bind_congr fun outer => ?_
  obtain ⟨choice⟩ := outer
  cases choice
  · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  · simp only [↓reduceIte, bind_assoc]
    refine bind_congr fun inner => ?_
    obtain ⟨choice⟩ := inner
    cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]

/-- Binding the left-factored mass-aware draw exposes the scheduler calls used
by the left-reassociated process sampler. -/
theorem leftDraw_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (scheduler : BinaryScheduler m) (first second context : ScheduleMass)
    {α : Type w} (h : ULift.{w, 0} Leaf → m α) :
    leftDraw scheduler first second context >>= h =
      scheduler first (context + second) >>= fun outer =>
        if outer.down then
          h ⟨.first⟩
        else
          scheduler context second >>= fun inner =>
            if inner.down then h ⟨.context⟩ else h ⟨.second⟩ := by
  simp only [leftDraw, bind_assoc]
  refine bind_congr fun outer => ?_
  obtain ⟨choice⟩ := outer
  cases choice
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
    refine bind_congr fun inner => ?_
    obtain ⟨choice⟩ := inner
    cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  · simp only [↓reduceIte, pure_bind]

/-- Binding the right-factored mass-aware draw exposes the scheduler calls
used by the right-reassociated process sampler. -/
theorem rightDraw_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (scheduler : BinaryScheduler m) (first second context : ScheduleMass)
    {α : Type w} (h : ULift.{w, 0} Leaf → m α) :
    rightDraw scheduler first second context >>= h =
      scheduler second (context + first) >>= fun outer =>
        if outer.down then
          h ⟨.second⟩
        else
          scheduler context first >>= fun inner =>
            if inner.down then h ⟨.context⟩ else h ⟨.first⟩ := by
  simp only [rightDraw, bind_assoc]
  refine bind_congr fun outer => ?_
  obtain ⟨choice⟩ := outer
  cases choice
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
    refine bind_congr fun inner => ?_
    obtain ⟨choice⟩ := inner
    cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  · simp only [↓reduceIte, pure_bind]

end BinaryScheduler

/-! ## Reassociated path samplers -/

/-- The source-shaped and left-factored nested path samplers are related after
applying the structural left-reassociation path equivalence. -/
theorem samplePath_interleave_assoc_left {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] (R : MonadRelFamily m)
    (scheduler : BinaryScheduler m) (coherent : scheduler.IsCoherent R)
    (firstMass secondMass contextMass : ScheduleMass)
    (firstTree secondTree contextTree : TypeTree.{w})
    (firstSampler : TypeTree.Sampler m firstTree)
    (secondSampler : TypeTree.Sampler m secondTree)
    (contextSampler : TypeTree.Sampler m contextTree) :
    R.rel
      ((fun path => parLeftPathEquiv firstTree secondTree contextTree path) <$>
        TypeTree.samplePath _
          (TypeTree.Sampler.interleave
            (scheduler (firstMass + secondMass) contextMass)
            (TypeTree.Sampler.interleave (scheduler firstMass secondMass)
              firstSampler secondSampler)
            contextSampler))
      (TypeTree.samplePath _
        (TypeTree.Sampler.interleave
          (scheduler firstMass (contextMass + secondMass)) firstSampler
          (TypeTree.Sampler.interleave (scheduler contextMass secondMass)
            contextSampler secondSampler))) := by
  let continuation : ULift.{w, 0} Leaf →
      m (TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
        | ⟨true⟩ => firstTree
        | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => contextTree
          | ⟨false⟩ => secondTree)) := fun leaf =>
    match leaf with
    | ⟨.first⟩ => TypeTree.samplePath _ firstSampler >>= fun path =>
        pure ⟨⟨true⟩, path⟩
    | ⟨.second⟩ => TypeTree.samplePath _ secondSampler >>= fun path =>
        pure ⟨⟨false⟩, ⟨⟨false⟩, path⟩⟩
    | ⟨.context⟩ => TypeTree.samplePath _ contextSampler >>= fun path =>
        pure ⟨⟨false⟩, ⟨⟨true⟩, path⟩⟩
  have source_eq :
      ((fun path => parLeftPathEquiv firstTree secondTree contextTree path) <$>
        TypeTree.samplePath _
          (TypeTree.Sampler.interleave
            (scheduler (firstMass + secondMass) contextMass)
            (TypeTree.Sampler.interleave (scheduler firstMass secondMass)
              firstSampler secondSampler)
            contextSampler)) =
        BinaryScheduler.sourceDraw scheduler firstMass secondMass contextMass >>=
          continuation := by
    rw [BinaryScheduler.sourceDraw_bind]
    simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind]
    refine bind_congr fun outer => ?_
    obtain ⟨choice⟩ := outer
    cases choice
    · simp only [Bool.false_eq_true, ↓reduceIte, map_pure]
      rfl
    · simp only [↓reduceIte, TypeTree.samplePath, bind_assoc, map_pure,
        pure_bind]
      refine bind_congr fun inner => ?_
      obtain ⟨choice⟩ := inner
      cases choice <;> rfl
  have target_eq :
      TypeTree.samplePath _
        (TypeTree.Sampler.interleave
          (scheduler firstMass (contextMass + secondMass)) firstSampler
          (TypeTree.Sampler.interleave (scheduler contextMass secondMass)
            contextSampler secondSampler)) =
        BinaryScheduler.leftDraw scheduler firstMass secondMass contextMass >>=
          continuation := by
    rw [BinaryScheduler.leftDraw_bind]
    simp only [TypeTree.Sampler.interleave, TypeTree.samplePath]
    refine bind_congr fun outer => ?_
    obtain ⟨choice⟩ := outer
    cases choice
    · simp only [Bool.false_eq_true, ↓reduceIte, TypeTree.samplePath, bind_assoc,
        pure_bind]
      refine bind_congr fun inner => ?_
      obtain ⟨choice⟩ := inner
      cases choice <;> rfl
    · simp only [↓reduceIte]
      rfl
  have draws_related := R.bind_congr continuation
    (coherent.left firstMass secondMass contextMass)
  exact Eq.mp
    (congrArg₂ (fun left right => R.rel left right)
      source_eq.symm target_eq.symm)
    draws_related

/-- The source-shaped and right-factored nested path samplers are related after
applying the structural right-reassociation path equivalence. -/
theorem samplePath_interleave_assoc_right {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] (R : MonadRelFamily m)
    (scheduler : BinaryScheduler m) (coherent : scheduler.IsCoherent R)
    (firstMass secondMass contextMass : ScheduleMass)
    (firstTree secondTree contextTree : TypeTree.{w})
    (firstSampler : TypeTree.Sampler m firstTree)
    (secondSampler : TypeTree.Sampler m secondTree)
    (contextSampler : TypeTree.Sampler m contextTree) :
    R.rel
      ((fun path => parRightPathEquiv firstTree secondTree contextTree path) <$>
        TypeTree.samplePath _
          (TypeTree.Sampler.interleave
            (scheduler (firstMass + secondMass) contextMass)
            (TypeTree.Sampler.interleave (scheduler firstMass secondMass)
              firstSampler secondSampler)
            contextSampler))
      (TypeTree.samplePath _
        (TypeTree.Sampler.interleave
          (scheduler secondMass (contextMass + firstMass)) secondSampler
          (TypeTree.Sampler.interleave (scheduler contextMass firstMass)
            contextSampler firstSampler))) := by
  let continuation : ULift.{w, 0} Leaf →
      m (TypeTree.Path (TypeTree.node (ULift.{w, 0} Bool) fun
        | ⟨true⟩ => secondTree
        | ⟨false⟩ => TypeTree.node (ULift.{w, 0} Bool) fun
          | ⟨true⟩ => contextTree
          | ⟨false⟩ => firstTree)) := fun leaf =>
    match leaf with
    | ⟨.first⟩ => TypeTree.samplePath _ firstSampler >>= fun path =>
        pure ⟨⟨false⟩, ⟨⟨false⟩, path⟩⟩
    | ⟨.second⟩ => TypeTree.samplePath _ secondSampler >>= fun path =>
        pure ⟨⟨true⟩, path⟩
    | ⟨.context⟩ => TypeTree.samplePath _ contextSampler >>= fun path =>
        pure ⟨⟨false⟩, ⟨⟨true⟩, path⟩⟩
  have source_eq :
      ((fun path => parRightPathEquiv firstTree secondTree contextTree path) <$>
        TypeTree.samplePath _
          (TypeTree.Sampler.interleave
            (scheduler (firstMass + secondMass) contextMass)
            (TypeTree.Sampler.interleave (scheduler firstMass secondMass)
              firstSampler secondSampler)
            contextSampler)) =
        BinaryScheduler.sourceDraw scheduler firstMass secondMass contextMass >>=
          continuation := by
    rw [BinaryScheduler.sourceDraw_bind]
    simp only [TypeTree.Sampler.interleave, TypeTree.samplePath, map_bind]
    refine bind_congr fun outer => ?_
    obtain ⟨choice⟩ := outer
    cases choice
    · simp only [Bool.false_eq_true, ↓reduceIte, map_pure]
      rfl
    · simp only [↓reduceIte, TypeTree.samplePath, bind_assoc, map_pure,
        pure_bind]
      refine bind_congr fun inner => ?_
      obtain ⟨choice⟩ := inner
      cases choice <;> rfl
  have target_eq :
      TypeTree.samplePath _
        (TypeTree.Sampler.interleave
          (scheduler secondMass (contextMass + firstMass)) secondSampler
          (TypeTree.Sampler.interleave (scheduler contextMass firstMass)
            contextSampler firstSampler)) =
        BinaryScheduler.rightDraw scheduler firstMass secondMass contextMass >>=
          continuation := by
    rw [BinaryScheduler.rightDraw_bind]
    simp only [TypeTree.Sampler.interleave, TypeTree.samplePath]
    refine bind_congr fun outer => ?_
    obtain ⟨choice⟩ := outer
    cases choice
    · simp only [Bool.false_eq_true, ↓reduceIte, TypeTree.samplePath, bind_assoc,
        pure_bind]
      refine bind_congr fun inner => ?_
      obtain ⟨choice⟩ := inner
      cases choice <;> rfl
    · simp only [↓reduceIte]
      rfl
  have draws_related := R.bind_congr continuation
    (coherent.right firstMass secondMass contextMass)
  exact Eq.mp
    (congrArg₂ (fun left right => R.rel left right)
      source_eq.symm target_eq.symm)
    draws_related

end UC
end Interaction
