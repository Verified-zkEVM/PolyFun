/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Almost-everywhere postconditions through a Giry bind

A measurable event that holds almost everywhere under every continuation, for almost every
initial point, holds almost everywhere under the bind. The second form needs only an
almost-everywhere measurable continuation.
-/

@[expose] public section

namespace MeasureTheory.Measure

universe u v

variable {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]

/-- An almost-everywhere postcondition is preserved by a measurable bind. -/
theorem ae_bind_of_ae {μ : Measure α} {k : α → Measure β} {p : β → Prop}
    (hk : Measurable k) (hp : MeasurableSet {b | p b})
    (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂k a, p b) : ∀ᵐ b ∂μ.bind k, p b := by
  change (μ.bind k) {b | p b}ᶜ = 0
  rw [bind_apply hp.compl hk.aemeasurable]
  exact (lintegral_eq_zero_iff (measurable_coe hp.compl |>.comp hk)).2
    (h.mono fun _ ha => ha)

/-- An almost-everywhere measurable bind preserves measurable almost-everywhere postconditions. -/
theorem ae_bind_of_ae_of_aemeasurable {μ : Measure α} {k : α → Measure β} {p : β → Prop}
    (hk : AEMeasurable k μ) (hp : MeasurableSet {b | p b})
    (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂k a, p b) : ∀ᵐ b ∂μ.bind k, p b := by
  rw [bind_congr_right hk.ae_eq_mk]
  apply ae_bind_of_ae hk.measurable_mk hp
  filter_upwards [h, hk.ae_eq_mk] with a ha heq
  rw [← heq]
  exact ha

end MeasureTheory.Measure
