/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Semantics.Correspondence
public import PolyFun.Control.Domain.Measure
public import PolyFun.Control.Monad.Measure

/-!
# Pushforwards of certified meanings

A certified meaning `f : CertifiedMeaning input output` agrees with its native implementation on
every encoded input: `f.meaning (input x) = output (f.implementation x)`. Pushing a measure on
native inputs forward along the encoded meaning `f.meaning ∘ input` therefore gives the encoding
of the implementation's pushforward (`Control.Semantics.CertifiedMeaning.map_meaning`). A
correspondence on an admissible set gives the same equation when almost every input is admissible
(`Control.Semantics.CorrespondsOn.map_meaning_ae`).

A decoded certificate, whose output encoding is `DomainResult.valueEmbedding`, returns a value at
every input. Pushed forward along its encoded meaning, a measure on native inputs therefore has the
implementation's pushforward as its values and no failure mass
(`Control.Semantics.CertifiedMeaning.success_map_meaning`,
`Control.Semantics.CertifiedMeaning.failureMass_map_meaning`). A correspondence gives the same when
almost every input is admissible (`Control.Semantics.CorrespondsOn.success_map_meaning_ae`,
`Control.Semantics.CorrespondsOn.failureMass_map_meaning_ae`).

Under a lawful measure semantics, the output measure of a computation `mx` pushed forward along the
encoded meaning is the encoding of the output measure of `f.implementation <$> mx`
(`Control.Semantics.CertifiedMeaning.evalDist_map_meaning`,
`Control.Semantics.CorrespondsOn.evalDist_map_meaning_ae`).

The statements assume measurability of the output encoding and of the implementation only. The
decoded forms need the implementation to be measurable only almost everywhere. The input encoding
and the semantic carrier of inputs need no measurable structure, because the encoded meaning
equals `output ∘ f.implementation` on every input, or on almost every input.
-/

public section

open MeasureTheory

namespace Control.Semantics

universe u v

/-! ## Measures on native inputs -/

section measure

variable {A B D E : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace E]
  {input : A ↪ D} {output : B ↪ E}

/-- Pushing a measure on native inputs forward along the encoded meaning gives the encoding of the
implementation's pushforward. -/
theorem CertifiedMeaning.map_meaning (f : CertifiedMeaning input output) (μ : Measure A)
    (houtput : Measurable output) (himplementation : Measurable f.implementation) :
    μ.map (f.meaning ∘ input) = (μ.map f.implementation).map output := by
  have hcomp : f.meaning ∘ input = output ∘ f.implementation := funext f.correct
  rw [hcomp, Measure.map_map houtput himplementation]

/-- A correspondence on the admissible inputs gives the pushforward equation of
`CertifiedMeaning.map_meaning` when almost every input is admissible. -/
theorem CorrespondsOn.map_meaning_ae {valid : A → Prop} {meaning : D → E} {implementation : A → B}
    (h : CorrespondsOn input output valid meaning implementation) {μ : Measure A}
    (hvalid : ∀ᵐ x ∂μ, valid x) (houtput : Measurable output)
    (himplementation : Measurable implementation) :
    μ.map (meaning ∘ input) = (μ.map implementation).map output := by
  rw [Measure.map_map houtput himplementation]
  exact Measure.map_congr (hvalid.mono fun x hx ↦ h x hx)

end measure

/-! ## Decoded meanings: values and failure -/

section result

variable {A D B ε : Type*} [MeasurableSpace A] [MeasurableSpace B] {input : A ↪ D}

/-- A decoded certificate's encoded meaning pushes a measure on native inputs to a measure whose
values are the implementation's pushforward. -/
theorem CertifiedMeaning.success_map_meaning
    (f : CertifiedMeaning input (DomainResult.valueEmbedding : B ↪ DomainResult ε B))
    {μ : Measure A} (himplementation : AEMeasurable f.implementation μ) :
    DomainResult.success (μ.map (f.meaning ∘ input)) = μ.map f.implementation := by
  have hcomp : f.meaning ∘ input = DomainResult.value ∘ f.implementation := funext f.correct
  rw [hcomp, ← DomainResult.measurable_value.aemeasurable.map_map_of_aemeasurable himplementation,
    DomainResult.success_map_value]

/-- A decoded certificate's encoded meaning pushes a measure on native inputs to a measure with no
failure mass: it neither diverges nor fails at any native input. -/
theorem CertifiedMeaning.failureMass_map_meaning
    (f : CertifiedMeaning input (DomainResult.valueEmbedding : B ↪ DomainResult ε B))
    {μ : Measure A} (himplementation : AEMeasurable f.implementation μ) :
    DomainResult.failureMass (μ.map (f.meaning ∘ input)) = 0 := by
  have hcomp : f.meaning ∘ input = DomainResult.value ∘ f.implementation := funext f.correct
  rw [hcomp, ← DomainResult.measurable_value.aemeasurable.map_map_of_aemeasurable himplementation,
    DomainResult.failureMass_map_value]

/-- A decoded correspondence gives the values of `CertifiedMeaning.success_map_meaning` when
almost every input is admissible. -/
theorem CorrespondsOn.success_map_meaning_ae {valid : A → Prop} {meaning : D → DomainResult ε B}
    {implementation : A → B}
    (h : CorrespondsOn input DomainResult.valueEmbedding valid meaning implementation)
    {μ : Measure A} (hvalid : ∀ᵐ x ∂μ, valid x) (himplementation : AEMeasurable implementation μ) :
    DomainResult.success (μ.map (meaning ∘ input)) = μ.map implementation := by
  have hmap : μ.map (meaning ∘ input) = μ.map (DomainResult.value ∘ implementation) :=
    Measure.map_congr (hvalid.mono fun x hx ↦ h x hx)
  rw [hmap, ← DomainResult.measurable_value.aemeasurable.map_map_of_aemeasurable himplementation,
    DomainResult.success_map_value]

/-- A decoded correspondence gives no failure mass when almost every input is admissible. -/
theorem CorrespondsOn.failureMass_map_meaning_ae {valid : A → Prop}
    {meaning : D → DomainResult ε B} {implementation : A → B}
    (h : CorrespondsOn input DomainResult.valueEmbedding valid meaning implementation)
    {μ : Measure A} (hvalid : ∀ᵐ x ∂μ, valid x) (himplementation : AEMeasurable implementation μ) :
    DomainResult.failureMass (μ.map (meaning ∘ input)) = 0 := by
  have hmap : μ.map (meaning ∘ input) = μ.map (DomainResult.value ∘ implementation) :=
    Measure.map_congr (hvalid.mono fun x hx ↦ h x hx)
  rw [hmap, ← DomainResult.measurable_value.aemeasurable.map_map_of_aemeasurable himplementation,
    DomainResult.failureMass_map_value]

end result

/-! ## Output measures of computations -/

section evalDist

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {A B : Type u} {D E : Type*}
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace E] {input : A ↪ D} {output : B ↪ E}

/-- The output measure of a computation, pushed forward along the encoded meaning, is the encoding
of the output measure of the implementation run on its result. -/
theorem CertifiedMeaning.evalDist_map_meaning (f : CertifiedMeaning input output) (mx : m A)
    (houtput : Measurable output) (himplementation : Measurable f.implementation) :
    (evalDist mx).map (f.meaning ∘ input) = (evalDist (f.implementation <$> mx)).map output := by
  rw [evalDist_map mx himplementation, f.map_meaning _ houtput himplementation]

/-- A correspondence gives the equation of `CertifiedMeaning.evalDist_map_meaning` when almost
every output of the computation is admissible. -/
theorem CorrespondsOn.evalDist_map_meaning_ae {valid : A → Prop} {meaning : D → E}
    {implementation : A → B} (h : CorrespondsOn input output valid meaning implementation)
    {mx : m A} (hvalid : ∀ᵐ x ∂evalDist mx, valid x) (houtput : Measurable output)
    (himplementation : Measurable implementation) :
    (evalDist mx).map (meaning ∘ input) = (evalDist (implementation <$> mx)).map output := by
  rw [evalDist_map mx himplementation, h.map_meaning_ae hvalid houtput himplementation]

end evalDist

end Control.Semantics
