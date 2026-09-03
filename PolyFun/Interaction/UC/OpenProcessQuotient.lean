/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.ActivationObservation
public import PolyFun.Interaction.UC.EmulatesQuotient
public import PolyFun.Interaction.UC.OpenProcessSamplerFactorization
public import PolyFun.Interaction.UC.SamplerObservation
public import PolyFun.Interaction.UC.ScheduledSamplerFactorization

/-!
# Quotients of the process models

The coherence laws of the process model `openTheory` hold only up to
equivalence: unconditionally up to activation equivalence, and conditionally
up to sampler equivalence. Both equivalences are congruences — the
congruence theorems of `OpenProcessCoherence` and
`OpenProcessSamplerCoherence` are their fields — so the model has quotient
theories on which the laws are equalities.

* `openTheory.activationCongruence`: activation equivalence. The laws modulo
  it are exactly the activation-equivalence theorems, so the quotient is
  strictly `HasPlugWireFactor`; this is the interim behaviour carrier of
  `docs/wiki/uc.md`. `Observation.activation` is the pull-back of equality on
  this quotient.
* `openTheory.samplerCongruence R`: sampler equivalence at a bind-congruent
  relation family. Under the three scheduler-transport facts the plug laws
  hold modulo it, so the quotient satisfies `HasPlugFactorization`;
  `Observation.sampler` is the pull-back of equality on this quotient.
* `scheduledOpenTheory.samplerCongruence R`: on the mass-aware theory the
  congruence also fixes the scheduler mass, since composition draws with the
  component masses. Scheduler coherence alone makes the quotient satisfy
  `HasPlugFactorization`.

In every case the composition suite of `Emulates` on the quotient, at plain
equality, is the suite on the model at the corresponding observation
(`Emulates.quotient_iff`).
-/

public section

universe u v w w'

namespace Interaction
namespace UC

open OpenTheory OpenNodeContext

variable (Party : Type u) (m : Type w → Type w') (schedulerSampler : m (ULift.{w, 0} Bool))

/-! ## The activation congruence -/

namespace openTheory

/-- Activation equivalence is a congruence on the process model: boundary
adaptation and the three compositions preserve it. -/
@[expose]
def activationCongruence : (openTheory.{u, v, w, w'} Party m schedulerSampler).Congruence where
  setoid _ :=
    ⟨OpenProcessActivationEquiv,
      ⟨OpenProcessActivationEquiv.refl, OpenProcessActivationEquiv.symm,
        OpenProcessActivationEquiv.trans⟩⟩
  map_congr := by
    intro _ _ φ _ _ h
    exact OpenProcess.mapHom_congr (preservesActivation_map φ) h
  par_congr := by
    intro Δ₁ Δ₂ W₁ W₁' W₂ W₂' h₁ h₂
    exact (OpenProcess.interleave_congr_left W₁ W₂ (preservesActivation_inlTensor Δ₁ Δ₂)
      (preservesActivation_inrTensor Δ₁ Δ₂) (schedulerNode_isActivated Party _)
      schedulerSampler h₁ schedulerSampler).trans
      (OpenProcess.interleave_congr_right W₁' W₂ (preservesActivation_inlTensor Δ₁ Δ₂)
        (preservesActivation_inrTensor Δ₁ Δ₂) (schedulerNode_isActivated Party _)
        schedulerSampler h₂ schedulerSampler)
  wire_congr := by
    intro Δ₁ Γ Δ₂ W₁ W₁' W₂ W₂' h₁ h₂
    exact (OpenProcess.interleave_congr_left W₁ W₂ (preservesActivation_wireLeft Δ₁ Γ Δ₂)
      (preservesActivation_wireRight Δ₁ Γ Δ₂) (schedulerNode_isActivated Party _)
      schedulerSampler h₁ schedulerSampler).trans
      (OpenProcess.interleave_congr_right W₁' W₂ (preservesActivation_wireLeft Δ₁ Γ Δ₂)
        (preservesActivation_wireRight Δ₁ Γ Δ₂) (schedulerNode_isActivated Party _)
        schedulerSampler h₂ schedulerSampler)
  plug_congr := by
    intro Δ W W' K K' h₁ h₂
    exact (OpenProcess.interleave_congr_left W K (preservesActivation_close Δ)
      (preservesActivation_close _) (schedulerNode_isActivated Party _)
      schedulerSampler h₁ schedulerSampler).trans
      (OpenProcess.interleave_congr_right W' K (preservesActivation_close Δ)
        (preservesActivation_close _) (schedulerNode_isActivated Party _)
        schedulerSampler h₂ schedulerSampler)

@[simp]
theorem activationCongruence_rel {Δ : PortBoundary}
    {W W' : OpenProcess.{u, v, w, w'} m Party Δ} :
    (activationCongruence Party m schedulerSampler).rel W W' ↔
      OpenProcessActivationEquiv W W' :=
  Iff.rfl

/-- Every law of the plug-wire ladder holds on the process model modulo
activation equivalence: each field is the corresponding
`openTheory_*_activation_equiv` theorem. -/
instance : HasPlugWireFactorMod (activationCongruence.{u, v, w, w'} Party m schedulerSampler) where
  __ := isLawfulMod_of_isLawful (activationCongruence Party m schedulerSampler)
  par_assoc W₁ W₂ W₃ := openTheory_par_assoc_activation_equiv Party m schedulerSampler W₁ W₂ W₃
  par_comm W₁ W₂ := openTheory_par_comm_activation_equiv Party m schedulerSampler W₁ W₂
  par_leftUnit W := openTheory_par_left_unit_activation_equiv Party m schedulerSampler W
  par_rightUnit W := openTheory_par_right_unit_activation_equiv Party m schedulerSampler W
  wire_assoc W₁ W₂ W₃ :=
    openTheory_wire_assoc_activation_equiv Party m schedulerSampler W₁ W₂ W₃
  wire_par_superpose W₁ W₂ W₃ :=
    openTheory_wire_par_superpose_activation_equiv Party m schedulerSampler W₁ W₂ W₃
  wire_comm W₁ W₂ := openTheory_wire_comm_activation_equiv Party m schedulerSampler W₁ W₂
  wire_idWire Γ _ W₂ := openTheory_wire_id_wire_activation_equiv Party m schedulerSampler Γ W₂
  wire_idWire_right Γ _ W₁ :=
    openTheory_wire_id_wire_right_activation_equiv Party m schedulerSampler Γ W₁
  unit_eq := openTheory_unit_eq_activation_equiv Party m
  plug_eq_wire W K := openTheory_plug_eq_wire_activation_equiv Party m schedulerSampler W K
  plug_par_left W₁ W₂ K :=
    openTheory_plug_par_left_activation_equiv Party m schedulerSampler W₁ W₂ K
  plug_wire_left W₁ W₂ K :=
    openTheory_plug_wire_left_activation_equiv Party m schedulerSampler W₁ W₂ K

/-- The quotient of the process model by activation equivalence is a strict
compact-closed theory with plug-wire factorization. -/
example :
    HasPlugWireFactor
      ((openTheory.{u, v, w, w'} Party m schedulerSampler).quotient
        (activationCongruence Party m schedulerSampler)) :=
  inferInstance

end openTheory

/-- The activation observation is the pull-back of equality on the activation
quotient. -/
theorem Observation.activation_rel_iff_comap
    {c₁ c₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Closed} :
    (Observation.activation Party m schedulerSampler).rel c₁ c₂ ↔
      ((Observation.eq _).comap (openTheory.activationCongruence Party m schedulerSampler)).rel
        c₁ c₂ := by
  rw [Observation.activation_rel, Observation.comap_eq_rel]
  exact (openTheory.activationCongruence_rel Party m schedulerSampler).symm

/-! ## The sampler congruence -/

section Sampler

variable [Monad m] [LawfulMonad m] (R : MonadRelFamily m) [R.IsBindCongr]

namespace openTheory

/-- Sampler equivalence at a bind-congruent relation family is a congruence
on the process model. -/
@[expose]
def samplerCongruence : (openTheory.{u, v, w, w'} Party m schedulerSampler).Congruence where
  setoid _ :=
    ⟨OpenProcessSamplerEquiv R,
      ⟨OpenProcessSamplerEquiv.refl, OpenProcessSamplerEquiv.symm,
        OpenProcessSamplerEquiv.trans⟩⟩
  map_congr := by
    intro _ _ φ _ _ h
    exact openTheory_map_congr_sampler_equiv Party m schedulerSampler R φ h
  par_congr h₁ h₂ :=
    (openTheory_par_congr_left_sampler_equiv Party m schedulerSampler R _ h₁).trans
      (openTheory_par_congr_right_sampler_equiv Party m schedulerSampler R _ h₂)
  wire_congr h₁ h₂ :=
    (openTheory_wire_congr_left_sampler_equiv Party m schedulerSampler R _ h₁).trans
      (openTheory_wire_congr_right_sampler_equiv Party m schedulerSampler R _ h₂)
  plug_congr h₁ h₂ :=
    (openTheory_plug_congr_left_sampler_equiv Party m schedulerSampler R _ h₁).trans
      (openTheory_plug_congr_right_sampler_equiv Party m schedulerSampler R _ h₂)

@[simp]
theorem samplerCongruence_rel {Δ : PortBoundary}
    {W W' : OpenProcess.{u, v, w, w'} m Party Δ} :
    (samplerCongruence Party m schedulerSampler R).rel W W' ↔
      OpenProcessSamplerEquiv R W W' :=
  Iff.rfl

/-- Under the three scheduler-transport facts, the plug laws hold on the
process model modulo sampler equivalence. A theorem rather than an instance:
the transport facts are genuine hypotheses. -/
theorem hasPlugFactorizationMod_samplerCongruence
    (hfair : R.rel schedulerSampler (schedulerFlip <$> schedulerSampler))
    (hleft : R.rel (OpenProcessFactorization.sourceDraw schedulerSampler)
      (OpenProcessFactorization.leftDraw schedulerSampler))
    (hright : R.rel (OpenProcessFactorization.sourceDraw schedulerSampler)
      (OpenProcessFactorization.rightDraw schedulerSampler)) :
    HasPlugFactorizationMod (samplerCongruence.{u, v, w, w'} Party m schedulerSampler R) where
  __ := isLawfulMod_of_isLawful (samplerCongruence Party m schedulerSampler R)
  plug_comm W K := openTheory_plug_comm_sampler_equiv Party m schedulerSampler R hfair W K
  close_par_left W₁ W₂ K :=
    openTheory_plug_par_left_sampler_equiv Party m schedulerSampler R hleft W₁ W₂ K
  close_par_right W₁ W₂ K :=
    openTheory_plug_par_right_sampler_equiv Party m schedulerSampler R hright W₁ W₂ K
  close_wire_left W₁ W₂ K :=
    openTheory_plug_wire_left_sampler_equiv Party m schedulerSampler R hleft W₁ W₂ K
  close_wire_right W₁ W₂ K :=
    openTheory_plug_wire_right_sampler_equiv Party m schedulerSampler R hright W₁ W₂ K

/-- Under the three scheduler-transport facts, the quotient of the process
model by sampler equivalence satisfies plug factorization. -/
theorem hasPlugFactorization_quotient_samplerCongruence
    (hfair : R.rel schedulerSampler (schedulerFlip <$> schedulerSampler))
    (hleft : R.rel (OpenProcessFactorization.sourceDraw schedulerSampler)
      (OpenProcessFactorization.leftDraw schedulerSampler))
    (hright : R.rel (OpenProcessFactorization.sourceDraw schedulerSampler)
      (OpenProcessFactorization.rightDraw schedulerSampler)) :
    HasPlugFactorization
      ((openTheory.{u, v, w, w'} Party m schedulerSampler).quotient
        (samplerCongruence Party m schedulerSampler R)) :=
  letI := hasPlugFactorizationMod_samplerCongruence Party m schedulerSampler R hfair hleft hright
  inferInstance

end openTheory

/-- The sampler observation is the pull-back of equality on the sampler
quotient. -/
theorem Observation.sampler_rel_iff_comap
    {c₁ c₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Closed} :
    (Observation.sampler Party m schedulerSampler R).rel c₁ c₂ ↔
      ((Observation.eq _).comap (openTheory.samplerCongruence Party m schedulerSampler R)).rel
        c₁ c₂ := by
  rw [Observation.sampler_rel, Observation.comap_eq_rel]
  exact (openTheory.samplerCongruence_rel Party m schedulerSampler R).symm

/-- `Observation.respectsFactorization_sampler`, re-derived through the
quotient: plug factorization on the quotient pulls back along `comap`. -/
theorem Observation.respectsFactorization_sampler_of_quotient
    (hfair : R.rel schedulerSampler (schedulerFlip <$> schedulerSampler))
    (hleft : R.rel (OpenProcessFactorization.sourceDraw schedulerSampler)
      (OpenProcessFactorization.leftDraw schedulerSampler))
    (hright : R.rel (OpenProcessFactorization.sourceDraw schedulerSampler)
      (OpenProcessFactorization.rightDraw schedulerSampler)) :
    (Observation.sampler.{u, v, w, w'} Party m schedulerSampler R).RespectsFactorization :=
  letI := openTheory.hasPlugFactorization_quotient_samplerCongruence Party m schedulerSampler R
    hfair hleft hright
  Observation.RespectsFactorization.of_rel_iff fun _ _ =>
    Observation.sampler_rel_iff_comap Party m schedulerSampler R

end Sampler

/-! ## The mass-aware sampler congruence -/

section Scheduled

variable [Monad m] [LawfulMonad m] (scheduler : BinaryScheduler m) (R : MonadRelFamily m)
  [R.IsBindCongr]

namespace scheduledOpenTheory

/-- Sampler equivalence of the underlying processes together with equal
scheduler mass is a congruence on the mass-aware theory. Equal mass is needed:
composition draws with the component masses. -/
@[expose]
def samplerCongruence : (scheduledOpenTheory.{u, v, w, w'} Party m scheduler).Congruence where
  setoid _ :=
    ⟨fun c₁ c₂ => c₁.mass = c₂.mass ∧ OpenProcessSamplerEquiv R c₁.process c₂.process,
      ⟨fun c => ⟨rfl, OpenProcessSamplerEquiv.refl c.process⟩,
        fun h => ⟨h.1.symm, h.2.symm⟩,
        fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩⟩
  map_congr := by
    rintro Δ₁ Δ₂ φ (W : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₁)
      (W' : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₁) ⟨hm, hp⟩
    exact ⟨hm, OpenProcess.mapHom_congr_samplerEquiv R (preservesActivation_map φ)
      (emitsAlong_map φ) hp⟩
  par_congr := by
    rintro Δ₁ Δ₂ (W₁ : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₁)
      (W₁' : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₁)
      (W₂ : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₂)
      (W₂' : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₂) ⟨hm₁, hp₁⟩ ⟨hm₂, hp₂⟩
    refine ⟨?_, ?_⟩
    · simp only [scheduledOpenTheory, ScheduledOpenProcess.mass_interleave, hm₁, hm₂]
    · simp only [scheduledOpenTheory, ScheduledOpenProcess.process_interleave]
      rw [hm₁, hm₂]
      exact (OpenProcess.interleave_congr_left_samplerEquiv R W₁.process W₂.process
        (preservesActivation_inlTensor Δ₁ Δ₂) (emitsAlong_inlTensor Δ₁ Δ₂) _ hp₁).trans
        (OpenProcess.interleave_congr_right_samplerEquiv R W₁'.process W₂.process
          (preservesActivation_inrTensor Δ₁ Δ₂) (emitsAlong_inrTensor Δ₁ Δ₂) _ hp₂)
  wire_congr := by
    rintro Δ₁ Γ Δ₂ (W₁ : ScheduledOpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
      (W₁' : ScheduledOpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
      (W₂ : ScheduledOpenProcess.{u, v, w, w'} m Party
        (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
      (W₂' : ScheduledOpenProcess.{u, v, w, w'} m Party
        (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) ⟨hm₁, hp₁⟩ ⟨hm₂, hp₂⟩
    refine ⟨?_, ?_⟩
    · simp only [scheduledOpenTheory, ScheduledOpenProcess.mass_interleave, hm₁, hm₂]
    · simp only [scheduledOpenTheory, ScheduledOpenProcess.process_interleave]
      rw [hm₁, hm₂]
      exact (OpenProcess.interleave_congr_left_samplerEquiv R W₁.process W₂.process
        (preservesActivation_wireLeft Δ₁ Γ Δ₂) (emitsAlong_wireLeft Δ₁ Γ Δ₂) _ hp₁).trans
        (OpenProcess.interleave_congr_right_samplerEquiv R W₁'.process W₂.process
          (preservesActivation_wireRight Δ₁ Γ Δ₂) (emitsAlong_wireRight Δ₁ Γ Δ₂) _ hp₂)
  plug_congr := by
    rintro Δ (W : ScheduledOpenProcess.{u, v, w, w'} m Party Δ)
      (W' : ScheduledOpenProcess.{u, v, w, w'} m Party Δ)
      (K : ScheduledOpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ))
      (K' : ScheduledOpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ)) ⟨hm₁, hp₁⟩ ⟨hm₂, hp₂⟩
    refine ⟨?_, ?_⟩
    · simp only [scheduledOpenTheory, ScheduledOpenProcess.mass_interleave, hm₁, hm₂]
    · simp only [scheduledOpenTheory, ScheduledOpenProcess.process_interleave]
      rw [hm₁, hm₂]
      exact (OpenProcess.interleave_congr_left_samplerEquiv R W.process K.process
        (preservesActivation_close Δ) (emitsAlong_close Δ) _ hp₁).trans
        (OpenProcess.interleave_congr_right_samplerEquiv R W'.process K.process
          (preservesActivation_close _) (emitsAlong_close _) _ hp₂)

@[simp]
theorem samplerCongruence_rel {Δ : PortBoundary}
    {W W' : ScheduledOpenProcess.{u, v, w, w'} m Party Δ} :
    (samplerCongruence Party m scheduler R).rel W W' ↔
      W.mass = W'.mass ∧ OpenProcessSamplerEquiv R W.process W'.process :=
  Iff.rfl

/-- Under a coherent scheduler, the plug laws hold on the mass-aware theory
modulo its sampler congruence: the masses agree by associativity and
commutativity of addition, the processes by the scheduled sampler laws. -/
theorem hasPlugFactorizationMod_samplerCongruence (coherent : scheduler.IsCoherent R) :
    HasPlugFactorizationMod (samplerCongruence.{u, v, w, w'} Party m scheduler R) where
  __ := isLawfulMod_of_isLawful (samplerCongruence Party m scheduler R)
  plug_comm := by
    rintro Δ (W : ScheduledOpenProcess.{u, v, w, w'} m Party Δ)
      (K : ScheduledOpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ))
    refine ⟨?_, scheduledOpenTheory_plug_comm_sampler_equiv Party m scheduler R coherent W K⟩
    simp only [scheduledOpenTheory, ScheduledOpenProcess.mass_interleave, add_comm]
  close_par_left := by
    rintro Δ₁ Δ₂ (W₁ : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₁)
      (W₂ : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₂)
      (K : ScheduledOpenProcess.{u, v, w, w'} m Party
        (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)))
    refine ⟨?_, scheduledOpenTheory_plug_par_left_sampler_equiv Party m scheduler R coherent
      W₁ W₂ K⟩
    simp only [OpenTheory.close, OpenTheory.parContextLeft, OpenTheory.mapEquiv,
      scheduledOpenTheory, ScheduledOpenProcess.mass_interleave,
      ScheduledOpenProcess.mass_mapBoundary, add_comm, add_left_comm]
  close_par_right := by
    rintro Δ₁ Δ₂ (W₁ : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₁)
      (W₂ : ScheduledOpenProcess.{u, v, w, w'} m Party Δ₂)
      (K : ScheduledOpenProcess.{u, v, w, w'} m Party
        (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)))
    refine ⟨?_, scheduledOpenTheory_plug_par_right_sampler_equiv Party m scheduler R coherent
      W₁ W₂ K⟩
    simp only [OpenTheory.close, OpenTheory.parContextRight, OpenTheory.mapEquiv,
      scheduledOpenTheory, ScheduledOpenProcess.mass_interleave,
      ScheduledOpenProcess.mass_mapBoundary, add_comm, add_left_comm]
  close_wire_left := by
    rintro Δ₁ Γ Δ₂ (W₁ : ScheduledOpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
      (W₂ : ScheduledOpenProcess.{u, v, w, w'} m Party
        (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
      (K : ScheduledOpenProcess.{u, v, w, w'} m Party
        (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)))
    refine ⟨?_, scheduledOpenTheory_plug_wire_left_sampler_equiv Party m scheduler R coherent
      W₁ W₂ K⟩
    simp only [OpenTheory.close, OpenTheory.wireContextLeft, OpenTheory.mapEquiv,
      scheduledOpenTheory, ScheduledOpenProcess.mass_interleave,
      ScheduledOpenProcess.mass_mapBoundary, add_comm, add_left_comm]
  close_wire_right := by
    rintro Δ₁ Γ Δ₂ (W₁ : ScheduledOpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
      (W₂ : ScheduledOpenProcess.{u, v, w, w'} m Party
        (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
      (K : ScheduledOpenProcess.{u, v, w, w'} m Party
        (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂)))
    refine ⟨?_, scheduledOpenTheory_plug_wire_right_sampler_equiv Party m scheduler R coherent
      W₁ W₂ K⟩
    simp only [OpenTheory.close, OpenTheory.wireContextRight, OpenTheory.mapEquiv,
      scheduledOpenTheory, ScheduledOpenProcess.mass_interleave,
      ScheduledOpenProcess.mass_mapBoundary, add_comm, add_left_comm]

/-- Under a coherent scheduler, the quotient of the mass-aware theory by its
sampler congruence satisfies plug factorization. -/
theorem hasPlugFactorization_quotient_samplerCongruence (coherent : scheduler.IsCoherent R) :
    HasPlugFactorization
      ((scheduledOpenTheory.{u, v, w, w'} Party m scheduler).quotient
        (samplerCongruence Party m scheduler R)) :=
  letI := hasPlugFactorizationMod_samplerCongruence Party m scheduler R coherent
  inferInstance

end scheduledOpenTheory

end Scheduled

end UC
end Interaction
