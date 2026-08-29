/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all PolyFun.Interaction.UC.OpenProcessFactorization
import all PolyFun.Interaction.UC.OpenProcessSamplerEquiv
public import PolyFun.Interaction.UC.OpenProcessFactorization
public import PolyFun.Interaction.UC.OpenProcessSamplerEquiv

/-!
# Reassociation-stable schedulers for open composition

The process-backed UC model combines systems through binary scheduler nodes.
Using one fixed Boolean sampler at every node makes the distribution of the
selected component depend on the parenthesization of the composition tree.

This module separates the abstract scheduling policy from that binary
encoding. A `BinaryScheduler m` chooses between two positive scheduling
masses. `BinaryScheduler.IsFlat` states that every hierarchical three-way
choice agrees with one common flat choice. Its derived `IsCoherent` contract
is exactly the swap and reassociation surface consumed by sampler-aware UC
factorization.

The definitions are monad-parametric and contain no probability. Downstream
models may instantiate the relation family by equality of probabilistic
denotations and implement `choose` by proportional weighted sampling.
-/

public section

universe w w'

namespace Interaction
namespace UC

/-! ## Positive scheduling mass -/

/-- A strictly positive number of scheduler slots represented by a natural
number. Positivity makes proportional downstream schedulers total and is
preserved by composition. -/
@[ext]
structure ScheduleMass where
  /-- The number of scheduler slots. -/
  value : Nat
  /-- Every schedulable component contributes at least one slot. -/
  positive : 0 < value
  deriving DecidableEq, Repr

namespace ScheduleMass

/-- One scheduler slot, the canonical mass of an atomic component. -/
@[expose]
def one : ScheduleMass := ⟨1, by omega⟩

/-- Combine the scheduler slots of two component frontiers. -/
@[expose]
def add (left right : ScheduleMass) : ScheduleMass :=
  ⟨left.value + right.value, Nat.add_pos_left left.positive _⟩

instance : One ScheduleMass := ⟨one⟩

instance : Add ScheduleMass := ⟨add⟩

@[simp]
theorem value_one : (1 : ScheduleMass).value = 1 := rfl

@[simp]
theorem value_add (left right : ScheduleMass) :
    (left + right).value = left.value + right.value :=
  rfl

theorem add_assoc (first second third : ScheduleMass) :
    (first + second) + third = first + (second + third) := by
  apply ScheduleMass.ext
  simp [Nat.add_assoc]

theorem add_comm (left right : ScheduleMass) : left + right = right + left := by
  apply ScheduleMass.ext
  simp [Nat.add_comm]

end ScheduleMass

/-! ## Binary and flat scheduler choices -/

/-- A scheduler policy for a binary split. The two arguments record the total
mass of the left and right component frontiers. -/
abbrev BinaryScheduler (m : Type w → Type w') :=
  ScheduleMass → ScheduleMass → m (ULift.{w, 0} Bool)

/-- Negate a binary scheduler choice. -/
@[expose]
def BinaryScheduler.flip : ULift.{w, 0} Bool → ULift.{w, 0} Bool :=
  fun choice => ULift.up !choice.down

@[simp]
theorem BinaryScheduler.flip_up_true :
    BinaryScheduler.flip (ULift.up true : ULift.{w, 0} Bool) = ULift.up false :=
  rfl

@[simp]
theorem BinaryScheduler.flip_up_false :
    BinaryScheduler.flip (ULift.up false : ULift.{w, 0} Bool) = ULift.up true :=
  rfl

namespace BinaryScheduler

/-- Source-shaped hierarchical scheduling: choose the composed pair first,
then choose its first or second component. -/
@[expose]
def sourceDraw {m : Type w → Type w'} [Monad m]
    (scheduler : BinaryScheduler m)
    (first second context : ScheduleMass) :
    m (ULift.{w, 0} OpenProcessFactorization.Leaf) := do
  let outer ← scheduler (first + second) context
  if outer.down then
    let inner ← scheduler first second
    if inner.down then
      pure (ULift.up OpenProcessFactorization.Leaf.first)
    else
      pure (ULift.up OpenProcessFactorization.Leaf.second)
  else
    pure (ULift.up OpenProcessFactorization.Leaf.context)

/-- Left-factored hierarchical scheduling: choose the first component or the
combined context/second frontier. -/
@[expose]
def leftDraw {m : Type w → Type w'} [Monad m]
    (scheduler : BinaryScheduler m)
    (first second context : ScheduleMass) :
    m (ULift.{w, 0} OpenProcessFactorization.Leaf) := do
  let outer ← scheduler first (context + second)
  if outer.down then
    pure (ULift.up OpenProcessFactorization.Leaf.first)
  else
    let inner ← scheduler context second
    if inner.down then
      pure (ULift.up OpenProcessFactorization.Leaf.context)
    else
      pure (ULift.up OpenProcessFactorization.Leaf.second)

/-- Right-factored hierarchical scheduling: choose the second component or
the combined context/first frontier. -/
@[expose]
def rightDraw {m : Type w → Type w'} [Monad m]
    (scheduler : BinaryScheduler m)
    (first second context : ScheduleMass) :
    m (ULift.{w, 0} OpenProcessFactorization.Leaf) := do
  let outer ← scheduler second (context + first)
  if outer.down then
    pure (ULift.up OpenProcessFactorization.Leaf.second)
  else
    let inner ← scheduler context first
    if inner.down then
      pure (ULift.up OpenProcessFactorization.Leaf.context)
    else
      pure (ULift.up OpenProcessFactorization.Leaf.first)

/-- The scheduler's direct, parenthesization-free three-way choice. -/
abbrev FlatChoice (m : Type w → Type w') :=
  ScheduleMass → ScheduleMass → ScheduleMass →
    m (ULift.{w, 0} OpenProcessFactorization.Leaf)

/-- The transport laws needed by binary open composition: swapping two
frontiers and reassociating three frontiers do not change the scheduler's
semantic choice, relative to `R`. -/
structure IsCoherent {m : Type w → Type w'} [Monad m]
    (R : MonadRelFamily m) (scheduler : BinaryScheduler m) : Prop where
  /-- Swapping the two branches is represented by negating the Boolean draw. -/
  swap : ∀ left right,
    R.rel (scheduler left right) (BinaryScheduler.flip <$> scheduler right left)
  /-- Source and left-factored three-way choices agree. -/
  left : ∀ first second context,
    R.rel (sourceDraw scheduler first second context)
      (leftDraw scheduler first second context)
  /-- Source and right-factored three-way choices agree. -/
  right : ∀ first second context,
    R.rel (sourceDraw scheduler first second context)
      (rightDraw scheduler first second context)

/-- A binary scheduler factors through a flat scheduler when every hierarchical
encoding of a three-way choice is related to the same direct draw. This is the
preferred proof interface for downstream schedulers: establish one semantic
categorical choice, rather than proving reassociation pairwise. -/
structure IsFlat {m : Type w → Type w'} [Monad m]
    (R : MonadRelFamily m) (scheduler : BinaryScheduler m)
    (flat : FlatChoice m) : Prop where
  /-- Binary choice is equivariant under swapping its two masses. -/
  swap : ∀ left right,
    R.rel (scheduler left right) (BinaryScheduler.flip <$> scheduler right left)
  /-- The source-shaped hierarchy denotes the flat choice. -/
  source : ∀ first second context,
    R.rel (sourceDraw scheduler first second context) (flat first second context)
  /-- The left-factored hierarchy denotes the flat choice. -/
  left : ∀ first second context,
    R.rel (leftDraw scheduler first second context) (flat first second context)
  /-- The right-factored hierarchy denotes the flat choice. -/
  right : ∀ first second context,
    R.rel (rightDraw scheduler first second context) (flat first second context)

/-- Factoring every hierarchical encoding through one flat choice supplies the
pairwise scheduler-coherence laws used by UC factorization. -/
theorem IsFlat.isCoherent {m : Type w → Type w'} [Monad m]
    {R : MonadRelFamily m} {scheduler : BinaryScheduler m}
    {flat : FlatChoice m} (h : IsFlat R scheduler flat) :
    IsCoherent R scheduler where
  swap := h.swap
  left first second context :=
    R.trans (h.source first second context) (R.symm (h.left first second context))
  right first second context :=
    R.trans (h.source first second context) (R.symm (h.right first second context))

end BinaryScheduler

end UC
end Interaction
