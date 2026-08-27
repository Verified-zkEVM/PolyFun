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

Regression checks for emulation in the presence of a global resource: the
UCGS-style composition theorem reaches the free syntax model through its
strict factorization instance, and the concrete process model through the
activation observation.
-/

@[expose] public section

universe u v w w'

namespace Interaction.UC.GlobalSubroutineExamples

/-! ### Free syntax model -/

section FreeModel

variable {Atom : PortBoundary → Type u}
  (Obs : Observation (OpenSyntax.Expr.theory Atom))

/-- Emulation survives sharing a global resource on the free model, and an
outer protocol composes onto the shared composite: the UCGS theorem shape. -/
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

/-- Replacing the global resource by an emulating one preserves the
judgment. -/
example {Δ Γ E : PortBoundary}
    {real ideal : (OpenSyntax.Expr.theory Atom).Obj (PortBoundary.tensor Δ Γ)}
    {G G' : (OpenSyntax.Expr.theory Atom).Obj
      (PortBoundary.tensor (PortBoundary.swap Γ) E)}
    (hG : Emulates G G' Obs)
    (h : EmulatesWithGlobal G real ideal Obs) :
    EmulatesWithGlobal G' real ideal Obs :=
  h.congr_global hG

end FreeModel

/-! ### Concrete process model at the activation observation -/

section ProcessModel

variable {Party : Type u} {m : Type w → Type w'}
  {schedulerSampler : m (ULift.{w, 0} Bool)}

/-- Activation-level emulation survives sharing a global resource over the
concrete process model. -/
example {Δ Γ E : PortBoundary}
    {real ideal : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj
      (PortBoundary.tensor Δ Γ)}
    (G : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj
      (PortBoundary.tensor (PortBoundary.swap Γ) E))
    (h : Emulates real ideal (Observation.activation Party m schedulerSampler)) :
    EmulatesWithGlobal G real ideal
      (Observation.activation Party m schedulerSampler) :=
  h.toEmulatesWithGlobal G

end ProcessModel

/-! ### Relativized variant -/

/-- The relativized judgment consumes an allowed global resource and an
allowed outer protocol. -/
example {T : OpenTheory.{u}} {D : SubTheory T} {Δ Γ E Δ' : PortBoundary}
    {Obs : Observation T} [Obs.RespectsFactorization]
    {real ideal : T.Obj (PortBoundary.tensor Δ Γ)}
    {G : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) E)} (hG : D.mem G)
    {ρ : T.Obj (PortBoundary.tensor Δ' (PortBoundary.swap Δ))} (hρ : D.mem ρ)
    (h : EmulatesWithin D real ideal Obs) :
    EmulatesWithin D
      (T.wire (Γ := PortBoundary.swap Δ) ρ (T.withGlobal real G))
      (T.wire (Γ := PortBoundary.swap Δ) ρ (T.withGlobal ideal G)) Obs :=
  (h.toEmulatesWithGlobalWithin hG).wire_outer hρ

end Interaction.UC.GlobalSubroutineExamples
