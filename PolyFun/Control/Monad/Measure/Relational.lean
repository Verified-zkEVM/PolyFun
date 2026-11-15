/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import PolyFun.Control.Monad.Measure.EvalDistEq
public import ToCslib.MeasureTheory.Measure.Coupling

/-!
# Measure-theoretic relational program logic

This module states relational semantics directly over couplings of Mathlib measures.
`ExpectationWP.CouplingPost μ ν R` asks for a coupling of `μ` and `ν` under which `R` holds almost
everywhere, and `ExpectationWP.RelWP mx my R` asks this of the output measures of two computations,
possibly in different monads. An almost-everywhere postcondition suits continuous distributions:
it does not mistake a zero-mass singleton for an impossible output.

`ExpectationWP.eRelWP` is the quantitative counterpart. It takes a supremum over measure couplings
and integrates the post-expectation with `lintegral`. Neither definition depends on a finite
distribution, countable support, or point probabilities. This module gives witness constructors,
reflexivity, monotonicity, and pushforwards along measurable maps. The sequential rules are in
`PolyFun.Control.Monad.Measure.Relational.Bind`.

## Equality couplings

A coupling concentrated on the diagonal has equal marginals, whether or not the diagonal is a
measurable set (`ExpectationWP.CouplingPost.eq`). In the discrete structure on the outputs, a
diagonal coupling of two output measures therefore gives equality in distribution
(`EvalDistEq.of_coupling`, `EvalDistEq.of_relWP_eq`). The converse needs a diagonal coupling to
exist, which holds when the diagonal is measurable (`EvalDistEq.relWP_eq`) or the output measure is
concentrated on a countable set (`EvalDistEq.relWP_eq_of_ae_mem_countable`).

## Namespace

The coupling predicates live in the `ExpectationWP` namespace that VCVio uses for them, so VCVio
imports them without renaming. They are distinct from the `MAlgRelOrdered.RelWP` of an abstract
relational algebra. `ExpectationWP.couplingAlgebra` presents `RelWP` as such an algebra.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

universe u v w x w₁ w₂

namespace ExpectationWP

variable {α : Type u} {β : Type v}
variable [MeasurableSpace α] [MeasurableSpace β]

/-- A relation holds under some coupling of `μ` and `ν`, almost everywhere. -/
def CouplingPost (μ : Measure α) (ν : Measure β) (R : α → β → Prop) : Prop :=
  ∃ c : Measure.Coupling μ ν, ∀ᵐ z ∂c.joint, R z.1 z.2

/-- Measure-theoretic relational weakest precondition for two denoted computations. -/
def RelWP {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (R : α → β → Prop) : Prop :=
  CouplingPost (evalDist mx) (evalDist my) R

/-- Quantitative relational WP: best coupled expectation of `g`. -/
noncomputable def eRelWP {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (g : α → β → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ c : Measure.Coupling (evalDist mx) (evalDist my), ∫⁻ z, g z.1 z.2 ∂c.joint

/-- Postcondition monotonicity for measure couplings. -/
theorem CouplingPost.mono {μ : Measure α} {ν : Measure β} {R S : α → β → Prop}
    (h : CouplingPost μ ν R) (hRS : ∀ a b, R a b → S a b) :
    CouplingPost μ ν S := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.mono fun z hz => hRS z.1 z.2 hz⟩

/-- Implication of relations preserves a measure-theoretic relational judgment. -/
theorem relWP_mono {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    {mx : m₁ α} {my : m₂ β} {R S : α → β → Prop}
    (h : RelWP mx my R) (hRS : ∀ a b, R a b → S a b) : RelWP mx my S :=
  h.mono hRS

/-- Quantitative post-expectation monotonicity. -/
@[gcongr low]
theorem eRelWP_mono {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) {g h : α → β → ℝ≥0∞}
    (hgh : ∀ a b, g a b ≤ h a b) :
    eRelWP mx my g ≤ eRelWP mx my h := by
  refine iSup_mono fun c => ?_
  exact lintegral_mono fun z => hgh z.1 z.2

/-- A concrete measure coupling provides a falsifiable lower bound on the quantitative WP. -/
theorem le_eRelWP_of_isCoupling {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (g : α → β → ℝ≥0∞)
    (c : Measure.Coupling (evalDist mx) (evalDist my)) :
    (∫⁻ z, g z.1 z.2 ∂c.joint) ≤ eRelWP mx my g :=
  le_iSup (fun c' : Measure.Coupling (evalDist mx) (evalDist my) ↦
    ∫⁻ z, g z.1 z.2 ∂c'.1) c

/-- The Dirac coupling gives the expected lower bound for two pure computations. -/
theorem le_eRelWP_pure_pure
    {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulPureEvalDistSemantics m₁] [LawfulPureEvalDistSemantics m₂]
    (a : α) (b : β) (g : α → β → ℝ≥0∞)
    (hg : Measurable fun z : α × β => g z.1 z.2) :
    g a b ≤ eRelWP (pure a : m₁ α) (pure b : m₂ β) g := by
  rw [eRelWP, evalDist_pure, evalDist_pure]
  have h := le_iSup
    (fun c : Measure.Coupling (Measure.dirac a) (Measure.dirac b) ↦
      ∫⁻ z, g z.1 z.2 ∂c.joint)
    (Measure.Coupling.dirac a b)
  rw [Measure.Coupling.dirac_joint] at h
  rw [lintegral_dirac' (a, b) hg] at h
  exact h

/-- Pure computations satisfy every relation true of their returned pair. -/
theorem relWP_pure_pure
    {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulPureEvalDistSemantics m₁] [LawfulPureEvalDistSemantics m₂]
    (a : α) (b : β) {R : α → β → Prop}
    (hMeasurable : MeasurableSet {z : α × β | R z.1 z.2}) (hR : R a b) :
    RelWP (pure a : m₁ α) (pure b : m₂ β) R := by
  simp only [RelWP, evalDist_pure]
  refine ⟨Measure.Coupling.dirac a b, ?_⟩
  exact (ae_dirac_iff hMeasurable).2 hR

/-- The diagonal measure witnesses reflexivity of coupling semantics. -/
theorem couplingPost_refl [MeasurableEq α] (μ : Measure α) : CouplingPost μ μ (· = ·) := by
  refine ⟨Measure.Coupling.refl μ, ?_⟩
  exact (ae_map_iff (μ := μ) (measurable_id.prodMk measurable_id).aemeasurable
    (measurableSet_eq_fun measurable_fst measurable_snd)).2
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Countable concentration suffices for reflexivity even when equality is not globally
measurable in the product space. -/
theorem couplingPost_refl_of_ae_mem_countable [MeasurableSingletonClass α]
    (μ : Measure α) {s : Set α} (hs : s.Countable) (hμ : ∀ᵐ a ∂μ, a ∈ s) :
    CouplingPost μ μ (· = ·) := by
  have hevent : MeasurableSet {z : α × α | (z.1 ∈ s ∧ z.2 ∈ s) ∧ z.1 = z.2} :=
    ((hs.prod hs).mono fun _ hz ↦ hz.1).measurableSet
  refine ⟨Measure.Coupling.refl μ, ?_⟩
  rw [Measure.Coupling.refl_joint]
  exact ((ae_map_iff (μ := μ) (measurable_id.prodMk measurable_id).aemeasurable
    hevent).2 (hμ.mono fun _ ha ↦ ⟨⟨ha, ha⟩, rfl⟩)).mono fun _ h ↦ h.2

/-- Every computation is related to itself by equality. -/
theorem relWP_refl {m : Type u → Type w₁} [EvalDistSemantics m] [MeasurableEq α] (mx : m α) :
    RelWP mx mx (· = ·) :=
  couplingPost_refl (evalDist mx)

/-- A countably concentrated output law admits a reflexive relational witness. -/
theorem relWP_refl_of_ae_mem_countable {m : Type u → Type w₁}
    [EvalDistSemantics m] [MeasurableSingletonClass α]
    (mx : m α) {s : Set α} (hs : s.Countable) (h : ∀ᵐ a ∂evalDist mx, a ∈ s) :
    RelWP mx mx (· = ·) := couplingPost_refl_of_ae_mem_countable (evalDist mx) hs h

/-- A zero post-expectation has zero coupled expectation, including when no coupling exists. -/
@[simp]
theorem eRelWP_zero {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂] (mx : m₁ α) (my : m₂ β) :
    eRelWP mx my (fun _ _ ↦ 0) = 0 := by
  simp [eRelWP]

/-- Coupling semantics cannot relate unequal successful-output masses. -/
theorem not_relWP_of_mass_ne {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂] (mx : m₁ α) (my : m₂ β)
    (h : evalDist mx Set.univ ≠ evalDist my Set.univ) (R : α → β → Prop) : ¬RelWP mx my R := by
  rintro ⟨c, _⟩
  exact h c.isCoupling.apply_univ_eq

/-- The quantitative supremum is zero when unequal masses leave no coupling witnesses. -/
theorem eRelWP_eq_zero_of_mass_ne {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂] (mx : m₁ α) (my : m₂ β)
    (h : evalDist mx Set.univ ≠ evalDist my Set.univ) (g : α → β → ℝ≥0∞) :
    eRelWP mx my g = 0 := by
  let : IsEmpty (Measure.Coupling (evalDist mx) (evalDist my)) :=
    ⟨fun c ↦ h c.isCoupling.apply_univ_eq⟩
  simp [eRelWP]

/-- Coupled expectations respect any pointwise constant upper bound. -/
theorem eRelWP_le {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    (mx : m₁ α) (my : m₂ β) (g : α → β → ℝ≥0∞) (bound : ℝ≥0∞)
    (h : ∀ a b, g a b ≤ bound) : eRelWP mx my g ≤ bound := by
  refine iSup_le fun c ↦ ?_
  calc
    (∫⁻ z, g z.1 z.2 ∂c.joint) ≤ ∫⁻ _ : α × β, bound ∂c.joint :=
      lintegral_mono fun z ↦ h z.1 z.2
    _ = bound * evalDist mx Set.univ := by
      rw [lintegral_const, c.isCoupling.joint_apply_univ_eq_left]
    _ ≤ bound := mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx)

/-- Pure computations have their exact coupled post-expectation. -/
@[simp]
theorem eRelWP_pure_pure [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulPureEvalDistSemantics m₁] [LawfulPureEvalDistSemantics m₂]
    (a : α) (b : β) (g : α → β → ℝ≥0∞) :
    eRelWP (pure a : m₁ α) (pure b : m₂ β) g = g a b := by
  rw [eRelWP, evalDist_pure, evalDist_pure]
  apply le_antisymm
  · refine iSup_le fun c ↦ ?_
    apply le_of_eq
    calc
      (∫⁻ z, g z.1 z.2 ∂c.joint) = ∫⁻ _ : α × β, g a b ∂c.joint :=
        lintegral_congr_ae ((c.isCoupling.ae_eq_pair_of_dirac a b).mono fun z hz ↦ by rw [hz])
      _ = g a b := by
        rw [lintegral_const, c.isCoupling.joint_apply_univ_eq_left, measure_univ, mul_one]
  · simpa only [Measure.Coupling.dirac_joint, lintegral_dirac] using le_iSup
      (fun c : Measure.Coupling (Measure.dirac a) (Measure.dirac b) ↦
        ∫⁻ z, g z.1 z.2 ∂c.joint) (Measure.Coupling.dirac a b)

/-- Pure computations satisfy exactly the relation on their returned values. -/
@[simp]
theorem relWP_pure_pure_iff [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [Monad m₁] [Monad m₂] [EvalDistSemantics m₁] [EvalDistSemantics m₂]
    [LawfulPureEvalDistSemantics m₁] [LawfulPureEvalDistSemantics m₂]
    (a : α) (b : β) (R : α → β → Prop) :
    RelWP (pure a : m₁ α) (pure b : m₂ β) R ↔ R a b := by
  rw [RelWP, evalDist_pure, evalDist_pure, CouplingPost]
  constructor
  · rintro ⟨c, hc⟩
    have hpair := c.isCoupling.ae_eq_pair_of_dirac a b
    obtain ⟨z, hz, hR⟩ := (hpair.and hc).exists
    simpa [hz] using hR
  · intro hR
    exact ⟨Measure.Coupling.dirac a b, by simp [hR]⟩

/-! ## Total mass, pushforwards and functional composition -/

/-- Two finite measures are related by the trivial relation exactly when they have the same total
mass; the normalized product is the witness. -/
theorem couplingPost_true_iff {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : CouplingPost μ ν (fun _ _ ↦ True) ↔ μ Set.univ = ν Set.univ :=
  ⟨fun ⟨c, _⟩ ↦ c.isCoupling.apply_univ_eq,
    fun h ↦ ⟨⟨_, Measure.IsCoupling.smul_prod μ ν h⟩, Filter.Eventually.of_forall fun _ ↦ trivial⟩⟩

/-- Two computations are related by the trivial relation exactly when they have the same
successful-output mass. -/
theorem relWP_true_iff {m₁ : Type u → Type w₁} {m₂ : Type v → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂] (mx : m₁ α) (my : m₂ β) :
    RelWP mx my (fun _ _ ↦ True) ↔ evalDist mx Set.univ = evalDist my Set.univ :=
  couplingPost_true_iff

variable {γ : Type w} {δ : Type x} [MeasurableSpace γ] [MeasurableSpace δ]

/-- Measurable maps of both sides transport a coupling, provided the target relation is
measurable and implied on the image of the source relation. -/
theorem CouplingPost.map {μ : Measure α} {ν : Measure β} {R : α → β → Prop}
    (h : CouplingPost μ ν R) {f : α → γ} {g : β → δ} (hf : Measurable f) (hg : Measurable g)
    {S : γ → δ → Prop} (hS : MeasurableSet {z : γ × δ | S z.1 z.2})
    (hRS : ∀ a b, R a b → S (f a) (g b)) : CouplingPost (μ.map f) (ν.map g) S := by
  obtain ⟨c, hc⟩ := h
  have hpair : Measurable fun z : α × β ↦ (f z.1, g z.2) :=
    (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)
  exact ⟨c.map f g hf hg, (ae_map_iff hpair.aemeasurable hS).2
    (hc.mono fun z hz ↦ hRS z.1 z.2 hz)⟩

/-- A coupling of `μ` and `ν` composes with a coupling of `ν` and `ρ` concentrated on the graph of
a measurable map `g`. The composite relation is any measurable relation implied by `R a b` at
`(a, g b)`. -/
theorem CouplingPost.trans_graph {μ : Measure α} {ν : Measure β} {ρ : Measure δ}
    {R : α → β → Prop} (h : CouplingPost μ ν R) {g : β → δ} (hg : Measurable g)
    (h' : CouplingPost ν ρ fun b d ↦ d = g b) {S : α → δ → Prop}
    (hS : MeasurableSet {z : α × δ | S z.1 z.2}) (hRS : ∀ a b, R a b → S a (g b)) :
    CouplingPost μ ρ S := by
  obtain ⟨c', hc'⟩ := h'
  rw [c'.isCoupling.eq_map_of_ae_eq hg hc', ← Measure.map_id (μ := μ)]
  exact h.map measurable_id hg hS hRS

/-- A coupling concentrated on the diagonal has equal marginals. The diagonal need not be a
measurable set. -/
theorem CouplingPost.eq {μ ν : Measure α} (h : CouplingPost μ ν (· = ·)) : μ = ν :=
  let ⟨c, hc⟩ := h
  c.isCoupling.eq_of_ae_eq hc

/-- With a measurable diagonal, two measures are related by equality exactly when they are
equal. -/
theorem couplingPost_eq_iff [MeasurableEq α] {μ ν : Measure α} :
    CouplingPost μ ν (· = ·) ↔ μ = ν :=
  ⟨CouplingPost.eq, fun h ↦ h ▸ couplingPost_refl μ⟩

/-- Computations related by equality have the same output measure in the chosen measurable
structure. The diagonal need not be a measurable set. -/
theorem RelWP.evalDist_eq {m₁ : Type u → Type w₁} {m₂ : Type u → Type w₂}
    [EvalDistSemantics m₁] [EvalDistSemantics m₂] {mx : m₁ α} {my : m₂ α}
    (h : RelWP mx my (· = ·)) : evalDist mx = evalDist my :=
  CouplingPost.eq h

end ExpectationWP

/-! ## Equality in distribution from diagonal couplings -/

namespace EvalDistEq

open ExpectationWP

variable {m : Type → Type v} {m' : Type → Type w} [Monad m] [Monad m'] [LawfulMonad m]
  [LawfulMonad m'] [EvalDistSemantics m] [EvalDistSemantics m'] [LawfulEvalDistSemantics m]
  [LawfulEvalDistSemantics m'] {α : Type} {mx : m α} {my : m' α}

/-- A coupling of the output measures in a discrete structure, concentrated on the diagonal,
gives equality in distribution. The diagonal need not be measurable in the product structure. -/
theorem of_coupling {_ : MeasurableSpace α} [DiscreteMeasurableSpace α] {c : Measure (α × α)}
    (hc : c.IsCoupling (evalDist mx) (evalDist my)) (hdiag : ∀ᵐ z ∂c, z.1 = z.2) :
    EvalDistEq mx my :=
  of_evalDist_eq (hc.eq_of_ae_eq hdiag)

/-- Computations related by equality in a discrete structure on their outputs are equal in
distribution. -/
theorem of_relWP_eq {_ : MeasurableSpace α} [DiscreteMeasurableSpace α]
    (h : RelWP mx my (· = ·)) : EvalDistEq mx my :=
  of_evalDist_eq h.evalDist_eq

/-- Computations equal in distribution are related by equality in every structure with a
measurable diagonal; the diagonal coupling is the witness. -/
theorem relWP_eq [MeasurableSpace α] [MeasurableEq α] (h : EvalDistEq mx my) :
    RelWP mx my (· = ·) := by
  rw [RelWP, h.evalDist_eq]
  exact couplingPost_refl _

/-- Computations equal in distribution are related by equality when the output measure has
measurable singletons and is concentrated on a countable set. -/
theorem relWP_eq_of_ae_mem_countable [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : EvalDistEq mx my) {s : Set α} (hs : s.Countable) (hmx : ∀ᵐ a ∂evalDist mx, a ∈ s) :
    RelWP mx my (· = ·) := by
  rw [RelWP, ← h.evalDist_eq]
  exact couplingPost_refl_of_ae_mem_countable _ hs hmx

end EvalDistEq
