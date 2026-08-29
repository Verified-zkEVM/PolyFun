/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.GlobalSubroutine
public import PolyFun.Interaction.UC.ActivationObservation
public import PolyFun.Interaction.UC.OpenSyntax.Expr

/-!
# Global-subroutine examples

Regression checks for unconditional emulation in the presence of a global
resource and for conversion to the directional context-transformer judgment.
The outer-composition check uses the stronger unconditional premise; it is not
a canary for the paper's secure UCGS theorem.
-/

@[expose] public section

universe u v w w'

namespace Interaction.UC.GlobalSubroutineExamples

/-! ### Free syntax model -/

section FreeModel

variable {Atom : PortBoundary → Type u}
  (Obs : Observation (OpenSyntax.Expr.theory Atom))

/-- Unconditional emulation survives sharing a global resource on the free
model, and an outer protocol composes onto the shared composite. -/
example {Δ Γ E Δ' : PortBoundary}
    {real ideal : (OpenSyntax.Expr.theory Atom).Obj (PortBoundary.tensor Δ Γ)}
    (G : (OpenSyntax.Expr.theory Atom).Obj
      (PortBoundary.tensor (PortBoundary.swap Γ) E))
    (ρ : (OpenSyntax.Expr.theory Atom).Obj
      (PortBoundary.tensor Δ' (PortBoundary.swap Δ)))
    (h : Emulates real ideal Obs) :
    Emulates
      ((OpenSyntax.Expr.theory Atom).wire (Γ := PortBoundary.swap Δ) ρ
        ((OpenSyntax.Expr.theory Atom).withGlobal real G))
      ((OpenSyntax.Expr.theory Atom).wire (Γ := PortBoundary.swap Δ) ρ
        ((OpenSyntax.Expr.theory Atom).withGlobal ideal G)) Obs :=
  (h.toEmulatesWithGlobal G).wire_outer ρ

end FreeModel

/-! ### Concrete process model at the activation observation -/

section ProcessModel

variable {Party : Type u} {m : Type w → Type w'}
  {schedulerSampler : m (ULift.{w, 0} Bool)}

/-- Unconditional activation equivalence with a global resource supplies the
directional context-transformer judgment through the identity simulator. -/
example {Δ Γ E : PortBoundary}
    {real ideal : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj
      (PortBoundary.tensor Δ Γ)}
    (G : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj
      (PortBoundary.tensor (PortBoundary.swap Γ) E))
    (h : Emulates real ideal (Observation.activation Party m schedulerSampler)) :
    SecurelyEmulatesWithGlobal G real ideal
      (Observation.activation Party m schedulerSampler) :=
  (h.toEmulatesWithGlobal G).toSecurelyEmulatesWithGlobal

end ProcessModel

end Interaction.UC.GlobalSubroutineExamples
