/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.Set.Functor
public import PolyFun.Interaction.UC.ScheduledSamplerFactorization

/-!
# Sampler-coherence examples

The nondeterministic scheduler uses Mathlib's `SetM` and permits both branches.
All three hierarchical draws yield exactly the set of all leaves, so its
coherence is equality of computations, including which outcomes are possible.
This gives a concrete instance of the scheduled observation's factorization
and composition laws without probability or a relation that erases results.

The shared-sampler laws and component congruence are checked through ordinary
public imports as well.
-/

@[expose] public section

universe u v w w'

namespace Interaction.UC.SamplerCoherenceExamples

open OpenProcessFactorization

variable {Party : Type u} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
  {schedulerSampler : m (ULift.{w, 0} Bool)} {scheduler : BinaryScheduler m}

/-- The exact and forgetful relation families are bind-congruent. -/
example : (MonadRelFamily.eq m).IsBindCongr := inferInstance
example : (MonadRelFamily.top m).IsBindCongr := inferInstance

/-! ## Exact nondeterministic semantics -/

/-- Both scheduler branches are possible, independently of subtree masses. -/
def nondetScheduler : BinaryScheduler SetM.{w} := fun _ _ => Set.univ

/-- Swapping the two possible choices leaves the set unchanged. -/
theorem flip_nondetScheduler (a b : ℕ+) :
    BinaryScheduler.flip <$> nondetScheduler a b = nondetScheduler b a := by
  change BinaryScheduler.flip '' Set.univ = Set.univ
  ext x
  simp only [Set.mem_image, Set.mem_univ, true_and, iff_true]
  exact ⟨BinaryScheduler.flip x, by cases x with | up x => cases x <;> rfl⟩

/-- Each leaf is possible in the source nesting, with no other result. -/
theorem sourceDraw_nondetScheduler (a b c : ℕ+) :
    BinaryScheduler.sourceDraw nondetScheduler a b c =
      (Set.univ : SetM (ULift.{w, 0} Leaf)) := by
  change (⋃ outer : ULift Bool, ⋃ (_ : outer ∈ (Set.univ : Set (ULift Bool))),
    if outer.down then
      ⋃ inner : ULift Bool, ⋃ (_ : inner ∈ (Set.univ : Set (ULift Bool))),
        if inner.down then {ULift.up Leaf.first} else {ULift.up Leaf.second}
    else {ULift.up Leaf.context}) = Set.univ
  ext ⟨x⟩
  cases x <;> simp [Set.mem_iUnion, ULift.exists, Bool.exists_bool]

/-- Left factorization retains exactly the same three possible leaves. -/
theorem leftDraw_nondetScheduler (a b c : ℕ+) :
    BinaryScheduler.leftDraw nondetScheduler a b c =
      (Set.univ : SetM (ULift.{w, 0} Leaf)) := by
  change (⋃ outer : ULift Bool, ⋃ (_ : outer ∈ (Set.univ : Set (ULift Bool))),
    if outer.down then {ULift.up Leaf.first}
    else ⋃ inner : ULift Bool, ⋃ (_ : inner ∈ (Set.univ : Set (ULift Bool))),
      if inner.down then {ULift.up Leaf.context} else {ULift.up Leaf.second}) = Set.univ
  ext ⟨x⟩
  cases x <;> simp [Set.mem_iUnion, ULift.exists, Bool.exists_bool]

/-- Right factorization also retains exactly the same three possible leaves. -/
theorem rightDraw_nondetScheduler (a b c : ℕ+) :
    BinaryScheduler.rightDraw nondetScheduler a b c =
      (Set.univ : SetM (ULift.{w, 0} Leaf)) := by
  change (⋃ outer : ULift Bool, ⋃ (_ : outer ∈ (Set.univ : Set (ULift Bool))),
    if outer.down then {ULift.up Leaf.second}
    else ⋃ inner : ULift Bool, ⋃ (_ : inner ∈ (Set.univ : Set (ULift Bool))),
      if inner.down then {ULift.up Leaf.context} else {ULift.up Leaf.first}) = Set.univ
  ext ⟨x⟩
  cases x <;> simp [Set.mem_iUnion, ULift.exists, Bool.exists_bool]

/-- Exact equality of nondeterministic computations satisfies all coherence
laws, without identifying different sets of results. -/
theorem nondetScheduler_isCoherent :
    nondetScheduler.{w}.IsCoherent (MonadRelFamily.eq SetM) where
  swap a b := (MonadRelFamily.eq_rel _ _).mpr (flip_nondetScheduler b a).symm
  left a b c := (MonadRelFamily.eq_rel _ _).mpr
    ((sourceDraw_nondetScheduler a b c).trans (leftDraw_nondetScheduler a b c).symm)
  right a b c := (MonadRelFamily.eq_rel _ _).mpr
    ((sourceDraw_nondetScheduler a b c).trans (rightDraw_nondetScheduler a b c).symm)

/-- The observation compares exact sampled-path result sets. -/
example :
    (Observation.scheduledSampler.{u, v, w, w} Party SetM nondetScheduler
      (MonadRelFamily.eq SetM)).RespectsFactorization :=
  Observation.respectsFactorization_scheduledSampler Party SetM nondetScheduler
    (MonadRelFamily.eq SetM) nondetScheduler_isCoherent

/-- Parallel composition applies to this exact-semantic instance. -/
example {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : (scheduledOpenTheory.{u, v, w, w} Party SetM nondetScheduler).Obj Δ₁}
    {real₂ ideal₂ : (scheduledOpenTheory.{u, v, w, w} Party SetM nondetScheduler).Obj Δ₂}
    (h₁ : Emulates real₁ ideal₁
      (Observation.scheduledSampler Party SetM nondetScheduler (MonadRelFamily.eq SetM)))
    (h₂ : Emulates real₂ ideal₂
      (Observation.scheduledSampler Party SetM nondetScheduler (MonadRelFamily.eq SetM))) :
    Emulates ((scheduledOpenTheory Party SetM nondetScheduler).par real₁ real₂)
      ((scheduledOpenTheory Party SetM nondetScheduler).par ideal₁ ideal₂)
      (Observation.scheduledSampler Party SetM nondetScheduler (MonadRelFamily.eq SetM)) :=
  letI := Observation.respectsFactorization_scheduledSampler Party SetM nondetScheduler
    (MonadRelFamily.eq SetM) nondetScheduler_isCoherent
  Emulates.par_compose h₁ h₂

/-! ## Shared-sampler and component laws -/

/-- Sampler equivalence of a component lifts through any closing context: the
congruence laws chain along the structure of the composite. -/
example (R : MonadRelFamily m) [R.IsBindCongr] {Δ₁ Δ₂ : PortBoundary}
    {real ideal : OpenProcess.{u, v, w, w'} m Party Δ₁}
    (W : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)))
    (h : OpenProcessSamplerEquiv R real ideal) :
    OpenProcessSamplerEquiv R
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).par real W) K)
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).par ideal W) K) :=
  openTheory_plug_congr_left_sampler_equiv Party m schedulerSampler R K
    (openTheory_par_congr_left_sampler_equiv Party m schedulerSampler R W h)

/-- The shared-sampler associativity law also holds at exact nondeterministic
semantics, using the same draw at each composition node. -/
example {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w} SetM Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w} SetM Party Δ₂)
    (W₃ : OpenProcess.{u, v, w, w} SetM Party Δ₃) :
    OpenProcessSamplerEquiv (MonadRelFamily.eq SetM)
      (OpenProcess.mapBoundary (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom
        ((openTheory Party SetM (nondetScheduler 1 1)).par
          ((openTheory Party SetM (nondetScheduler 1 1)).par W₁ W₂) W₃))
      ((openTheory Party SetM (nondetScheduler 1 1)).par W₁
        ((openTheory Party SetM (nondetScheduler 1 1)).par W₂ W₃)) := by
  apply openTheory_par_assoc_sampler_equiv
  · exact nondetScheduler_isCoherent.swap 1 1
  · exact nondetScheduler_isCoherent.nestedDrawLeft_rel_factorLeft 1 1 1

/-- The shared-sampler plug factorization is the mass-aware one at constant
mass: the hierarchical draws coincide, so the transport facts do. -/
example (σ : m (ULift.{w, 0} Bool)) :
    BinaryScheduler.sourceDraw (fun _ _ => σ) 1 1 1 = sourceDraw σ :=
  BinaryScheduler.sourceDraw_eq_nestedDrawLeft (fun _ _ => σ) 1 1 1

end Interaction.UC.SamplerCoherenceExamples
