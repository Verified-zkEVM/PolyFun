/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.SecureEmulation
public import PolyFun.Interaction.UC.ActivationObservation

/-!
# Secure-emulation examples

Regression checks for the existential-simulator judgment: reconciliation with
`Emulates` and `UCSecure`, the preorder packaging, the relativized variant,
and availability over the concrete process model at the activation
observation.
-/

@[expose] public section

universe u v w w'

namespace Interaction.UC.SecureEmulationExamples

variable {T : OpenTheory.{u}} {Δ : PortBoundary} {Obs : Observation T}

/-- Unconditional emulation gives secure emulation in both directions. -/
example {real ideal : T.Obj Δ} (h : Emulates real ideal Obs) :
    SecurelyEmulates real ideal Obs ∧ SecurelyEmulates ideal real Obs :=
  ⟨h.toSecurelyEmulates, h.symm.toSecurelyEmulates⟩

/-- Secure emulation round-trips through `UCSecure` over the full transformer
space. -/
example {real ideal : T.Obj Δ} (h : SecurelyEmulates real ideal Obs) :
    SecurelyEmulates real ideal Obs :=
  h.toUCSecure.toSecurelyEmulates

/-- The preorder's order is secure emulation, and transitivity flows through
it. -/
example (Obs : Observation T) {W₁ W₂ W₃ : T.Obj Δ}
    (h₁₂ : SecurelyEmulates W₁ W₂ Obs) (h₂₃ : SecurelyEmulates W₂ W₃ Obs) :
    (securelyEmulatesPreorder Δ Obs).le W₁ W₃ :=
  securelyEmulatesPreorder_le_iff.mpr (SecurelyEmulates.trans h₁₂ h₂₃)

/-- Relativizing to the everything-class is conservative. -/
example {real ideal : T.Obj Δ} (h : SecurelyEmulates real ideal Obs) :
    SecurelyEmulatesWithin (SubTheory.top T) real ideal Obs :=
  securelyEmulatesWithin_top_iff.mpr h

/-- The judgment applies over the concrete process model at the activation
observation. -/
example {Party : Type u} {m : Type w → Type w'}
    {schedulerSampler : m (ULift.{w, 0} Bool)} {Δ : PortBoundary}
    {real ideal : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ}
    (h : Emulates real ideal (Observation.activation Party m schedulerSampler)) :
    SecurelyEmulates real ideal
      (Observation.activation Party m schedulerSampler) :=
  h.toSecurelyEmulates

end Interaction.UC.SecureEmulationExamples
