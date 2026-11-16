/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToCslib.MeasureTheory.Measure.Subprobability

/-!
# Couplings of measures

This file defines couplings directly at Mathlib's `Measure` boundary. A coupling is a joint
measure whose first and second marginals are the requested measures. No discreteness or
countability assumption is built into the definition.

The elementary constructors are the diagonal (`IsCoupling.refl`), the graph of a measurable map
(`IsCoupling.graph`), Dirac pairs, the swap and pushforwards. Two finite measures with the same
total mass have a coupling, the normalized product (`IsCoupling.smul_prod`), and only measures
with the same total mass do (`IsCoupling.apply_univ_eq`).

The remaining laws read a coupling concentrated on the graph of a measurable map, `z.2 = f z.1`
almost everywhere. Its second marginal is the pushforward of its first
(`IsCoupling.eq_map_of_ae_eq`), and the joint measure is the graph coupling
(`IsCoupling.joint_eq_map_of_ae_eq`). A coupling
concentrated on the diagonal therefore has equal marginals (`IsCoupling.eq_of_ae_eq`), with no
measurability assumption on the diagonal. Couplings compose with such functional couplings
(`IsCoupling.trans_of_ae_eq`); composing couplings of arbitrary relations would need a gluing
construction, which this file does not provide.

These are the measure-theoretic foundation of the relational program logic
`ExpectationWP.RelWP`, whose postconditions hold almost everywhere under the joint measure.
-/

@[expose] public section

-- upstream candidate

open MeasureTheory

universe u v w x

namespace MeasureTheory.Measure

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- `c` is a coupling of `μ` and `ν` when its two marginals are exactly `μ` and `ν`. -/
class IsCoupling (c : Measure (α × β)) (μ : Measure α) (ν : Measure β) : Prop where
  /-- The first marginal of the joint measure. -/
  fst_eq : c.fst = μ
  /-- The second marginal of the joint measure. -/
  snd_eq : c.snd = ν

/-- A joint measure together with its two marginal equations. -/
@[ext]
structure Coupling (μ : Measure α) (ν : Measure β) where
  /-- The joint response law. -/
  joint : Measure (α × β)
  /-- Its marginal equations. -/
  isCoupling : IsCoupling joint μ ν

namespace IsCoupling

variable {c : Measure (α × β)} {μ : Measure α} {ν : Measure β}

/-- A coupling has the same total mass as its first marginal. -/
theorem joint_apply_univ_eq_left (h : IsCoupling c μ ν) : c Set.univ = μ Set.univ := by
  rw [← h.fst_eq, Measure.fst_univ]

/-- A coupling has the same total mass as its second marginal. -/
theorem joint_apply_univ_eq_right (h : IsCoupling c μ ν) : c Set.univ = ν Set.univ := by
  rw [← h.snd_eq, Measure.snd_univ]

/-- Measures admitting a coupling necessarily have equal total mass. -/
theorem apply_univ_eq (h : IsCoupling c μ ν) : μ Set.univ = ν Set.univ := by
  rw [← h.joint_apply_univ_eq_left, h.joint_apply_univ_eq_right]

/-- Concentration of the marginals gives concentration of the joint pair. -/
theorem ae_mem_prod (h : IsCoupling c μ ν) {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμ : ∀ᵐ a ∂μ, a ∈ s) (hν : ∀ᵐ b ∂ν, b ∈ t) :
    ∀ᵐ z ∂c, z ∈ s ×ˢ t := by
  have ha : ∀ᵐ z ∂c, z.1 ∈ s := by
    apply (ae_map_iff measurable_fst.aemeasurable hs).1
    rw [show c.map Prod.fst = μ from h.fst_eq]
    exact hμ
  have hb : ∀ᵐ z ∂c, z.2 ∈ t := by
    apply (ae_map_iff measurable_snd.aemeasurable ht).1
    rw [show c.map Prod.snd = ν from h.snd_eq]
    exact hν
  exact ha.and hb

/-- Dirac marginals force the joint output pair almost everywhere. -/
theorem ae_eq_pair_of_dirac [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (a : α) (b : β) (h : IsCoupling c (Measure.dirac a) (Measure.dirac b)) :
    ∀ᵐ z ∂c, z = (a, b) := by
  have ha : ∀ᵐ z ∂c, z.1 = a := by
    have hmeas : MeasurableSet {x : α | x = a} := measurableSet_singleton a
    apply (ae_map_iff measurable_fst.aemeasurable hmeas).1
    rw [show c.map Prod.fst = Measure.dirac a from h.fst_eq]
    exact (ae_dirac_iff hmeas).2 rfl
  have hb : ∀ᵐ z ∂c, z.2 = b := by
    have hmeas : MeasurableSet {x : β | x = b} := measurableSet_singleton b
    apply (ae_map_iff measurable_snd.aemeasurable hmeas).1
    rw [show c.map Prod.snd = Measure.dirac b from h.snd_eq]
    exact (ae_dirac_iff hmeas).2 rfl
  filter_upwards [ha, hb] with z hz₀ hz₁
  exact Prod.ext hz₀ hz₁

/-- The diagonal pushforward is a self-coupling of any measure. -/
theorem refl (μ : Measure α) :
    IsCoupling (μ.map fun a => (a, a)) μ μ := by
  have hdiag : Measurable (fun a : α => (a, a)) :=
    measurable_id.prodMk measurable_id
  constructor
  · rw [Measure.fst, Measure.map_map measurable_fst hdiag]
    simp [Function.comp_def]
  · rw [Measure.snd, Measure.map_map measurable_snd hdiag]
    simp [Function.comp_def]

/-- The graph of a measurable map couples a measure with its pushforward. -/
theorem graph (μ : Measure α) {f : α → β} (hf : Measurable f) :
    IsCoupling (μ.map fun a => (a, f a)) μ (μ.map f) := by
  have hgraph : Measurable fun a : α => (a, f a) := measurable_id.prodMk hf
  constructor
  · rw [Measure.fst, Measure.map_map measurable_fst hgraph]
    exact Measure.map_id
  · rw [Measure.snd, Measure.map_map measurable_snd hgraph]
    rfl

/-- The product of two probability measures is an independent coupling. -/
theorem prod (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling (μ.prod ν) μ ν := by
  constructor <;> simp

/-- Two finite measures of the same total mass are coupled by their product, normalized by that
mass. -/
theorem smul_prod (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ Set.univ = ν Set.univ) :
    IsCoupling ((μ Set.univ)⁻¹ • μ.prod ν) μ ν := by
  by_cases hμ : μ Set.univ = 0
  · have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.1 hμ
    have hν0 : ν = 0 := Measure.measure_univ_eq_zero.1 (h ▸ hμ)
    subst hμ0 hν0
    constructor <;> simp
  have hcancel : (μ Set.univ)⁻¹ * μ Set.univ = 1 :=
    ENNReal.inv_mul_cancel hμ (measure_ne_top μ Set.univ)
  constructor
  · ext s hs
    rw [Measure.fst_apply hs, Measure.smul_apply, smul_eq_mul,
      show Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set β) by ext; simp, Measure.prod_prod, ← h,
      mul_comm (μ s), ← mul_assoc, hcancel, one_mul]
  · ext t ht
    rw [Measure.snd_apply ht, Measure.smul_apply, smul_eq_mul,
      show Prod.snd ⁻¹' t = (Set.univ : Set α) ×ˢ t by ext; simp, Measure.prod_prod,
      ← mul_assoc, hcancel, one_mul]

/-- A Dirac measure at a pair couples the corresponding Dirac marginals. -/
theorem dirac (a : α) (b : β) :
    IsCoupling (Measure.dirac (a, b)) (Measure.dirac a) (Measure.dirac b) := by
  constructor
  · simpa [Measure.fst] using Measure.map_dirac' measurable_fst (a, b)
  · simpa [Measure.snd] using Measure.map_dirac' measurable_snd (a, b)

/-- Swapping the coordinates of a coupling swaps its marginals. -/
theorem swap (h : IsCoupling c μ ν) :
    IsCoupling (c.map Prod.swap) ν μ := by
  constructor
  · rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
    simpa [Function.comp_def, Measure.snd] using h.snd_eq
  · rw [Measure.snd, Measure.map_map measurable_snd measurable_swap]
    simpa [Function.comp_def, Measure.fst] using h.fst_eq

/-- Measurable maps of both coordinates transport a coupling to the pushed-forward marginals. -/
theorem map (h : IsCoupling c μ ν) (f : α → γ) (g : β → δ)
    (hf : Measurable f) (hg : Measurable g) :
    IsCoupling (c.map fun z => (f z.1, g z.2)) (μ.map f) (ν.map g) := by
  have hpair : Measurable (fun z : α × β => (f z.1, g z.2)) :=
    (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)
  have hfst : c.map Prod.fst = μ := h.fst_eq
  have hsnd : c.map Prod.snd = ν := h.snd_eq
  constructor
  · rw [Measure.fst, Measure.map_map measurable_fst hpair]
    rw [show Prod.fst ∘ (fun z : α × β => (f z.1, g z.2)) = f ∘ Prod.fst by rfl,
      ← Measure.map_map hf measurable_fst, hfst]
  · rw [Measure.snd, Measure.map_map measurable_snd hpair]
    rw [show Prod.snd ∘ (fun z : α × β => (f z.1, g z.2)) = g ∘ Prod.snd by rfl,
      ← Measure.map_map hg measurable_snd, hsnd]

/-- A measurable map of the second coordinate composes a coupling with the graph coupling of
that map. -/
theorem map_right (h : IsCoupling c μ ν) {g : β → δ} (hg : Measurable g) :
    IsCoupling (c.map fun z => (z.1, g z.2)) μ (ν.map g) := by
  simpa only [Measure.map_id, id_eq] using h.map id g measurable_id hg

/-! ## Couplings concentrated on a graph -/

/-- The second marginal of a coupling concentrated on the graph of a measurable map is the
pushforward of the first marginal. -/
theorem eq_map_of_ae_eq (h : IsCoupling c μ ν) {f : α → β} (hf : Measurable f)
    (hc : ∀ᵐ z ∂c, z.2 = f z.1) : ν = μ.map f := by
  rw [← h.snd_eq, ← h.fst_eq, Measure.snd, Measure.fst, Measure.map_map hf measurable_fst]
  exact Measure.map_congr hc

/-- A coupling concentrated on the graph of a measurable map is the graph coupling of its first
marginal. -/
theorem joint_eq_map_of_ae_eq (h : IsCoupling c μ ν) {f : α → β} (hf : Measurable f)
    (hc : ∀ᵐ z ∂c, z.2 = f z.1) : c = μ.map fun a => (a, f a) := by
  rw [← h.fst_eq, Measure.fst, Measure.map_map (measurable_id'.prodMk hf) measurable_fst]
  conv_lhs => rw [← Measure.map_id (μ := c)]
  exact Measure.map_congr (hc.mono fun z hz => Prod.ext rfl hz)

/-- A coupling concentrated on the diagonal has equal marginals. The diagonal need not be a
measurable set. -/
theorem eq_of_ae_eq {c : Measure (α × α)} {μ ν : Measure α} (h : IsCoupling c μ ν)
    (hc : ∀ᵐ z ∂c, z.1 = z.2) : μ = ν := by
  simpa only [Measure.map_id] using
    (h.eq_map_of_ae_eq measurable_id (hc.mono fun _ hz => hz.symm)).symm

/-- A coupling of `μ` and `ν` composes with a coupling of `ν` and `ρ` concentrated on the graph of
a measurable map `g`: mapping the second coordinate by `g` couples `μ` and `ρ`. -/
theorem trans_of_ae_eq {ρ : Measure δ} {c' : Measure (β × δ)} (h : IsCoupling c μ ν)
    (h' : IsCoupling c' ν ρ) {g : β → δ} (hg : Measurable g) (hc' : ∀ᵐ z ∂c', z.2 = g z.1) :
    IsCoupling (c.map fun z => (z.1, g z.2)) μ ρ := by
  rw [h'.eq_map_of_ae_eq hg hc']
  exact h.map_right hg

end IsCoupling

namespace Coupling

variable {μ : Measure α} {ν : Measure β}

instance : CoeTC (Coupling μ ν) (Measure (α × β)) := ⟨Coupling.joint⟩

/-- The underlying joint measure. -/
abbrev val (c : Coupling μ ν) : Measure (α × β) := c.joint

/-- The joint law's marginal certificate. -/
abbrev property (c : Coupling μ ν) : IsCoupling c.joint μ ν := c.isCoupling

instance (c : Coupling μ ν) [IsProbabilityMeasure μ] : IsProbabilityMeasure c.joint where
  measure_univ := by rw [c.isCoupling.joint_apply_univ_eq_left, measure_univ]

instance (c : Coupling μ ν) [IsSubprobabilityMeasure μ] : IsSubprobabilityMeasure c.joint where
  measure_univ_le' := by
    rw [c.isCoupling.joint_apply_univ_eq_left]
    exact measure_univ_le μ

instance (c : Coupling μ ν) [IsFiniteMeasure μ] : IsFiniteMeasure c.joint where
  measure_univ_lt_top := by
    rw [c.isCoupling.joint_apply_univ_eq_left]
    exact measure_lt_top μ Set.univ

/-- Canonical diagonal self-coupling. -/
noncomputable def refl (μ : Measure α) : Coupling μ μ :=
  ⟨μ.map fun a => (a, a), IsCoupling.refl μ⟩

/-- The diagonal coupling's joint law is the diagonal pushforward. -/
@[simp]
theorem refl_joint (μ : Measure α) : (refl μ).joint = μ.map (fun a ↦ (a, a)) := rfl

/-- Independent-product coupling of probability measures. -/
noncomputable def prod (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : Coupling μ ν :=
  ⟨μ.prod ν, IsCoupling.prod μ ν⟩

/-- Coupling of two pure outcomes. -/
noncomputable def dirac (a : α) (b : β) :
    Coupling (Measure.dirac a) (Measure.dirac b) :=
  ⟨Measure.dirac (a, b), IsCoupling.dirac a b⟩

/-- The joint law of two pure outcomes is their paired Dirac measure. -/
@[simp]
theorem dirac_joint (a : α) (b : β) : (dirac a b).joint = Measure.dirac (a, b) := rfl

/-- Swap the coordinates of a coupling. -/
noncomputable def swap (c : Coupling μ ν) : Coupling ν μ :=
  ⟨c.joint.map Prod.swap, c.isCoupling.swap⟩

/-- Push a coupling forward through a pair of measurable functions. -/
noncomputable def map (c : Coupling μ ν) (f : α → γ) (g : β → δ)
    (hf : Measurable f) (hg : Measurable g) : Coupling (μ.map f) (ν.map g) :=
  ⟨c.joint.map fun z => (f z.1, g z.2), c.isCoupling.map f g hf hg⟩

end Coupling

end MeasureTheory.Measure
