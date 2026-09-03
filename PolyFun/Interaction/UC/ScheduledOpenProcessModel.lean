/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all PolyFun.Interaction.UC.OpenProcessModel
public import PolyFun.Interaction.UC.OpenProcessModel
public import PolyFun.Interaction.UC.Scheduler

/-!
# Mass-aware open-process composition

This module provides an additive migration model for reassociation-stable UC
scheduling. A `ScheduledOpenProcess` pairs an ordinary `OpenProcess` with the
positive mass of its scheduler frontier. Composition adds masses and asks a
`BinaryScheduler` to choose proportionally or otherwise coherently between
the two resulting frontiers.

The underlying process representation remains binary, so existing structural
process APIs continue to apply. Unlike `openTheory`, however, the scheduler
sampler at a composition node depends on the masses of both subtrees.
`BinaryScheduler.IsFlat` is the scheduler contract needed by the separate
sampler-factorization layer to prove that this choice is independent of how
composition is parenthesized. The theory is `IsLawful`: every naturality law
is the corresponding `openTheory` law at the scheduler draw for the component
masses, since boundary adaptation preserves mass.
-/

public section

universe u v w w'

namespace Interaction
namespace UC

/-- An open process together with the total positive mass of its scheduler
frontier. Atomic processes conventionally use mass `1`; composition adds the
two component masses. -/
@[ext]
structure ScheduledOpenProcess (m : Type w → Type w') (Party : Type u)
    (Delta : PortBoundary) where
  /-- Total mass of the atomic scheduler frontier represented by `process`. -/
  mass : ℕ+
  /-- The underlying open process and its protocol-local samplers. -/
  process : OpenProcess.{u, v, w, w'} m Party Delta

namespace ScheduledOpenProcess

/-- Equip an open process with an explicit positive scheduler mass. -/
def withMass {m : Type w → Type w'} {Party : Type u} {Delta : PortBoundary}
    (mass : ℕ+) (process : OpenProcess.{u, v, w, w'} m Party Delta) :
    ScheduledOpenProcess.{u, v, w, w'} m Party Delta :=
  ⟨mass, process⟩

@[simp]
theorem mass_withMass {m : Type w → Type w'} {Party : Type u} {Delta : PortBoundary}
    (mass : ℕ+) (process : OpenProcess.{u, v, w, w'} m Party Delta) :
    (withMass mass process).mass = mass :=
  (rfl)

@[simp]
theorem process_withMass {m : Type w → Type w'} {Party : Type u} {Delta : PortBoundary}
    (mass : ℕ+) (process : OpenProcess.{u, v, w, w'} m Party Delta) :
    (withMass mass process).process = process :=
  (rfl)

/-- Equip an atomic open process with one scheduler slot. -/
def atom {m : Type w → Type w'} {Party : Type u} {Delta : PortBoundary}
    (process : OpenProcess.{u, v, w, w'} m Party Delta) :
    ScheduledOpenProcess.{u, v, w, w'} m Party Delta :=
  withMass 1 process

@[simp]
theorem mass_atom {m : Type w → Type w'} {Party : Type u} {Delta : PortBoundary}
    (process : OpenProcess.{u, v, w, w'} m Party Delta) :
    (atom process).mass = 1 :=
  (rfl)

@[simp]
theorem process_atom {m : Type w → Type w'} {Party : Type u} {Delta : PortBoundary}
    (process : OpenProcess.{u, v, w, w'} m Party Delta) :
    (atom process).process = process :=
  (rfl)

/-- Adapt the boundary while preserving scheduler mass. -/
@[expose]
def mapBoundary {m : Type w → Type w'} {Party : Type u}
    {Delta₁ Delta₂ : PortBoundary} (phi : PortBoundary.Hom Delta₁ Delta₂)
    (process : ScheduledOpenProcess.{u, v, w, w'} m Party Delta₁) :
    ScheduledOpenProcess.{u, v, w, w'} m Party Delta₂ :=
  ⟨process.mass, process.process.mapBoundary phi⟩

@[simp]
theorem mass_mapBoundary {m : Type w → Type w'} {Party : Type u}
    {Delta₁ Delta₂ : PortBoundary} (phi : PortBoundary.Hom Delta₁ Delta₂)
    (process : ScheduledOpenProcess.{u, v, w, w'} m Party Delta₁) :
    (process.mapBoundary phi).mass = process.mass :=
  (rfl)

@[simp]
theorem process_mapBoundary {m : Type w → Type w'} {Party : Type u}
    {Delta₁ Delta₂ : PortBoundary} (phi : PortBoundary.Hom Delta₁ Delta₂)
    (process : ScheduledOpenProcess.{u, v, w, w'} m Party Delta₁) :
    (process.mapBoundary phi).process = process.process.mapBoundary phi :=
  (rfl)

/-- Interleave two scheduled processes. The composite records their summed
mass, and the root sampler receives both component masses. -/
@[expose]
def interleave {m : Type w → Type w'} {Party : Type u}
    {Delta₁ Delta₂ Delta : PortBoundary}
    (scheduler : BinaryScheduler m)
    (left : ScheduledOpenProcess.{u, v, w, w'} m Party Delta₁)
    (right : ScheduledOpenProcess.{u, v, w, w'} m Party Delta₂)
    (leftMap : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Delta₁) (OpenNodeContext.{u, w} Party Delta))
    (rightMap : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Delta₂) (OpenNodeContext.{u, w} Party Delta))
    (schedulerCtx : OpenNodeContext.{u, w} Party Delta (ULift.{w, 0} Bool)) :
    ScheduledOpenProcess.{u, v, w, w'} m Party Delta :=
  ⟨left.mass + right.mass,
    left.process.interleave right.process leftMap rightMap schedulerCtx
      (scheduler left.mass right.mass)⟩

@[simp]
theorem mass_interleave {m : Type w → Type w'} {Party : Type u}
    {Delta₁ Delta₂ Delta : PortBoundary}
    (scheduler : BinaryScheduler m)
    (left : ScheduledOpenProcess.{u, v, w, w'} m Party Delta₁)
    (right : ScheduledOpenProcess.{u, v, w, w'} m Party Delta₂)
    (leftMap : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Delta₁) (OpenNodeContext.{u, w} Party Delta))
    (rightMap : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Delta₂) (OpenNodeContext.{u, w} Party Delta))
    (schedulerCtx : OpenNodeContext.{u, w} Party Delta (ULift.{w, 0} Bool)) :
    (left.interleave scheduler right leftMap rightMap schedulerCtx).mass =
      left.mass + right.mass :=
  (rfl)

@[simp]
theorem process_interleave {m : Type w → Type w'} {Party : Type u}
    {Delta₁ Delta₂ Delta : PortBoundary}
    (scheduler : BinaryScheduler m)
    (left : ScheduledOpenProcess.{u, v, w, w'} m Party Delta₁)
    (right : ScheduledOpenProcess.{u, v, w, w'} m Party Delta₂)
    (leftMap : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Delta₁) (OpenNodeContext.{u, w} Party Delta))
    (rightMap : TypeTree.Node.ContextHom
      (OpenNodeContext.{u, w} Party Delta₂) (OpenNodeContext.{u, w} Party Delta))
    (schedulerCtx : OpenNodeContext.{u, w} Party Delta (ULift.{w, 0} Bool)) :
    (left.interleave scheduler right leftMap rightMap schedulerCtx).process =
      left.process.interleave right.process leftMap rightMap schedulerCtx
        (scheduler left.mass right.mass) :=
  (rfl)

end ScheduledOpenProcess

/-- The mass-aware open-composition theory. This is additive alongside the
legacy `openTheory`: callers can migrate atoms with `ScheduledOpenProcess.atom`
without changing `OpenProcess` itself. -/
@[expose]
def scheduledOpenTheory (Party : Type u) (m : Type w → Type w')
    (scheduler : BinaryScheduler m) : OpenTheory where
  Obj Delta := ScheduledOpenProcess.{u, v, w, w'} m Party Delta
  map phi process := process.mapBoundary phi
  par {Delta₁} {Delta₂} left right :=
    left.interleave scheduler right
      (OpenNodeContext.inlTensor Party Delta₁ Delta₂)
      (OpenNodeContext.inrTensor Party Delta₁ Delta₂)
      (schedulerNode Party (PortBoundary.tensor Delta₁ Delta₂))
  wire {Delta₁} {Gamma} {Delta₂} left right :=
    left.interleave scheduler right
      (OpenNodeContext.wireLeft Party Delta₁ Gamma Delta₂)
      (OpenNodeContext.wireRight Party Delta₁ Gamma Delta₂)
      (schedulerNode Party (PortBoundary.tensor Delta₁ Delta₂))
  plug {Delta} process context :=
    process.interleave scheduler context
      (OpenNodeContext.close Party Delta)
      (OpenNodeContext.close Party (PortBoundary.swap Delta))
      (schedulerNode Party PortBoundary.empty)

/-- Boundary adaptation in the mass-aware theory is functorial. Scheduling
mass is unchanged, while the underlying proof is the corresponding
`openTheory` map law. -/
instance lawfulMap_scheduledOpenTheory (Party : Type u) (m : Type w → Type w')
    (scheduler : BinaryScheduler m) :
    OpenTheory.IsLawfulMap
      (scheduledOpenTheory.{u, v, w, w'} Party m scheduler) where
  map_id process := by
    cases process with
    | mk mass process =>
      apply ScheduledOpenProcess.ext
      · rfl
      · exact OpenTheory.IsLawfulMap.map_id
          (T := openTheory Party m (scheduler mass mass)) process
  map_comp g f process := by
    cases process with
    | mk mass process =>
      apply ScheduledOpenProcess.ext
      · rfl
      · exact OpenTheory.IsLawfulMap.map_comp
          (T := openTheory Party m (scheduler mass mass)) g f process

/-- Parallel composition in the mass-aware theory is natural in boundary
adaptation: masses add on both sides, and the underlying process law is the
`openTheory` law at the scheduler draw for the two component masses. -/
instance lawfulPar_scheduledOpenTheory (Party : Type u) (m : Type w → Type w')
    (scheduler : BinaryScheduler m) :
    OpenTheory.IsLawfulPar
      (scheduledOpenTheory.{u, v, w, w'} Party m scheduler) where
  __ := lawfulMap_scheduledOpenTheory Party m scheduler
  map_par f₁ f₂ W₁ W₂ := by
    apply ScheduledOpenProcess.ext
    · rfl
    · exact OpenTheory.IsLawfulPar.map_par
        (T := openTheory Party m (scheduler W₁.mass W₂.mass)) f₁ f₂ W₁.process W₂.process

/-- Wiring in the mass-aware theory is natural in the still-exposed outer
boundaries. -/
instance lawfulWire_scheduledOpenTheory (Party : Type u) (m : Type w → Type w')
    (scheduler : BinaryScheduler m) :
    OpenTheory.IsLawfulWire
      (scheduledOpenTheory.{u, v, w, w'} Party m scheduler) where
  __ := lawfulMap_scheduledOpenTheory Party m scheduler
  map_wire f₁ f₂ W₁ W₂ := by
    apply ScheduledOpenProcess.ext
    · rfl
    · exact OpenTheory.IsLawfulWire.map_wire
        (T := openTheory Party m (scheduler W₁.mass W₂.mass)) f₁ f₂ W₁.process W₂.process

/-- Plugging in the mass-aware theory is natural in boundary adaptation. -/
instance lawfulPlug_scheduledOpenTheory (Party : Type u) (m : Type w → Type w')
    (scheduler : BinaryScheduler m) :
    OpenTheory.IsLawfulPlug
      (scheduledOpenTheory.{u, v, w, w'} Party m scheduler) where
  __ := lawfulMap_scheduledOpenTheory Party m scheduler
  map_plug f W K := by
    apply ScheduledOpenProcess.ext
    · rfl
    · exact OpenTheory.IsLawfulPlug.map_plug
        (T := openTheory Party m (scheduler W.mass K.mass)) f W.process K.process

instance (Party : Type u) (m : Type w → Type w') (scheduler : BinaryScheduler m) :
    OpenTheory.IsLawful (scheduledOpenTheory.{u, v, w, w'} Party m scheduler) where

end UC
end Interaction
