/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.OpenProcessEmulates
public import PolyFun.Interaction.UC.OpenSyntax.Expr

/-!
# Observation-level factorization examples

Regression checks that the UC composition theorems still reach the free
syntax models through `respectsFactorization_of_hasPlugWireFactor`, and that
the process-backed `openTheory` now reaches the `plug` half of the suite
through `Observation.IsSchedulingInsensitive`.
-/

@[expose] public section

universe u v w w'

namespace Interaction.UC.EmulatesFactorizationExamples

/-! ### Free syntax models keep the full suite -/

section FreeModel

variable {Atom : PortBoundary → Type u} (Obs : Observation (OpenSyntax.Expr.theory Atom))

/-- Strict plug/wire factorization gives every observation the factorization
laws, so instance synthesis needs no help on the free model. -/
example : Obs.RespectsFactorization := inferInstance

/-- The weaker plug-commutation layer is likewise available. -/
example : Obs.RespectsPlugComm := inferInstance

/-- Parallel composition of emulations still typechecks on the free model. -/
example {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : (OpenSyntax.Expr.theory Atom).Obj Δ₁}
    {real₂ ideal₂ : (OpenSyntax.Expr.theory Atom).Obj Δ₂}
    (h₁ : Emulates real₁ ideal₁ Obs) (h₂ : Emulates real₂ ideal₂ Obs) :
    Emulates ((OpenSyntax.Expr.theory Atom).par real₁ real₂)
      ((OpenSyntax.Expr.theory Atom).par ideal₁ ideal₂) Obs :=
  Emulates.par_compose h₁ h₂

/-- Wired composition of emulations still typechecks on the free model. -/
example {Δ₁ Γ Δ₂ : PortBoundary}
    {real₁ ideal₁ : (OpenSyntax.Expr.theory Atom).Obj (PortBoundary.tensor Δ₁ Γ)}
    {real₂ ideal₂ :
      (OpenSyntax.Expr.theory Atom).Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₁ : Emulates real₁ ideal₁ Obs) (h₂ : Emulates real₂ ideal₂ Obs) :
    Emulates ((OpenSyntax.Expr.theory Atom).wire real₁ real₂)
      ((OpenSyntax.Expr.theory Atom).wire ideal₁ ideal₂) Obs :=
  Emulates.wire_compose h₁ h₂

/-- Closing against emulating environments still typechecks on the free
model. -/
example {Δ : PortBoundary}
    {real ideal : (OpenSyntax.Expr.theory Atom).Obj Δ}
    {K_real K_ideal : (OpenSyntax.Expr.theory Atom).Obj (PortBoundary.swap Δ)}
    (hProt : Emulates real ideal Obs) (hEnv : Emulates K_real K_ideal Obs) :
    Obs.rel ((OpenSyntax.Expr.theory Atom).close real K_real)
      ((OpenSyntax.Expr.theory Atom).close ideal K_ideal) :=
  Emulates.plug_compose hProt hEnv

end FreeModel

/-! ### The process model reaches the whole suite -/

section ProcessModel

variable {Party : Type u} {m : Type w → Type w'} {schedulerSampler : m (ULift.{w, 0} Bool)}
  (Obs : Observation (openTheory.{u, v, w, w'} Party m schedulerSampler))
  [Observation.IsSchedulingInsensitive Obs]

/-- A scheduling-insensitive observation on the process model respects plug
commutation, without any `OpenTheory.HasPlugWireFactor` instance — which
`openTheory` does not have. -/
example : Obs.RespectsPlugComm := inferInstance

/-- It respects the full factorization too, so the process model meets the
same interface as the free syntax models. Note `openTheory` has neither a
`HasUnit` nor a `HasIdWire` instance, let alone `HasPlugWireFactor`. -/
example : Obs.RespectsFactorization := inferInstance

/-- **UC composition for `par` on the concrete process model.** This is the
statement the abstract layer was built for and could not previously reach. -/
example {Δ₁ Δ₂ : PortBoundary}
    {real₁ ideal₁ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ₁}
    {real₂ ideal₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ₂}
    (h₁ : Emulates real₁ ideal₁ Obs) (h₂ : Emulates real₂ ideal₂ Obs) :
    Emulates ((openTheory.{u, v, w, w'} Party m schedulerSampler).par real₁ real₂)
      ((openTheory.{u, v, w, w'} Party m schedulerSampler).par ideal₁ ideal₂) Obs :=
  Emulates.par_compose h₁ h₂

/-- **UC composition for `wire` on the concrete process model.** -/
example {Δ₁ Γ Δ₂ : PortBoundary}
    {real₁ ideal₁ :
      (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj (PortBoundary.tensor Δ₁ Γ)}
    {real₂ ideal₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₁ : Emulates real₁ ideal₁ Obs) (h₂ : Emulates real₂ ideal₂ Obs) :
    Emulates ((openTheory.{u, v, w, w'} Party m schedulerSampler).wire real₁ real₂)
      ((openTheory.{u, v, w, w'} Party m schedulerSampler).wire ideal₁ ideal₂) Obs :=
  Emulates.wire_compose h₁ h₂

/-- Consequently `Emulates.plug_compose` applies to the process model. This is
the statement that was previously out of reach: the composition theorems were
gated on strict compact-closed structure that `openTheory` cannot supply. -/
example {Δ : PortBoundary}
    {real ideal : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ}
    {K_real K_ideal :
      (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj (PortBoundary.swap Δ)}
    (hProt : Emulates real ideal Obs) (hEnv : Emulates K_real K_ideal Obs) :
    Obs.rel ((openTheory.{u, v, w, w'} Party m schedulerSampler).close real K_real)
      ((openTheory.{u, v, w, w'} Party m schedulerSampler).close ideal K_ideal) :=
  Emulates.plug_compose hProt hEnv

/-- Replacing the environment alone likewise applies. -/
example {Δ : PortBoundary}
    (W : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ)
    {K₁ K₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj (PortBoundary.swap Δ)}
    (hK : Emulates K₁ K₂ Obs) :
    Obs.rel ((openTheory.{u, v, w, w'} Party m schedulerSampler).close W K₁)
      ((openTheory.{u, v, w, w'} Party m schedulerSampler).close W K₂) :=
  Emulates.plug_right W hK

end ProcessModel

end Interaction.UC.EmulatesFactorizationExamples
