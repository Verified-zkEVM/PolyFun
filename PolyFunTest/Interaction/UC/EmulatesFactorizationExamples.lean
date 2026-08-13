/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.Emulates
import all PolyFun.Interaction.Basic.Sampler
import all PolyFun.Interaction.UC.OpenProcess
import all PolyFun.Interaction.UC.OpenProcessFactorization
public import PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.OpenProcessEmulates
public import PolyFun.Interaction.UC.OpenProcessFactorization
public import PolyFun.Interaction.UC.OpenSyntax.Expr

/-!
# UC factorization examples

Regression checks that the UC composition theorems still reach the free
syntax models through `respectsFactorization_of_hasPlugWireFactor`. For the
process model, the examples pin the four structural activation-equivalence
statements and their scheduler truth tables without promoting them to
packet-, probability-, or sampler-aware observations.
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

/-! ### Structural process-model factorization -/

section ProcessModel

variable {Party : Type u} {m : Type w → Type w'} {schedulerSampler : m (ULift.{w, 0} Bool)}

/-- The left parallel law retains its exact structural statement. -/
example {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (K : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).par W₁ W₂) K)
      ((openTheory Party m schedulerSampler).plug W₁
        (OpenProcess.mapBoundary
          (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁)).toHom
          ((openTheory Party m schedulerSampler).wire
            (Γ := PortBoundary.swap Δ₂)
            (Δ₂ := PortBoundary.empty)
            K
            (OpenProcess.mapBoundary
              (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm.toHom W₂)))) :=
  openTheory_plug_par_left_activation_equiv Party m schedulerSampler W₁ W₂ K

/-- The right parallel law retains its exact structural statement. -/
example {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (K : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).par W₁ W₂) K)
      ((openTheory Party m schedulerSampler).plug W₂
        (OpenProcess.mapBoundary
          (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₂)).toHom
          ((openTheory Party m schedulerSampler).wire
            (Γ := PortBoundary.swap Δ₁)
            (Δ₂ := PortBoundary.empty)
            (OpenProcess.mapBoundary
              (PortBoundary.Equiv.tensorComm
                (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)).toHom K)
            (OpenProcess.mapBoundary
              (PortBoundary.Equiv.tensorEmptyRight Δ₁).symm.toHom W₁)))) :=
  openTheory_plug_par_right_activation_equiv Party m schedulerSampler W₁ W₂ K

/-- The left wired law retains its exact structural statement. -/
example {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    (W₂ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).wire W₁ W₂) K)
      ((openTheory Party m schedulerSampler).plug W₁
        ((openTheory Party m schedulerSampler).wire
          (Δ₁ := PortBoundary.swap Δ₁)
          (Γ := PortBoundary.swap Δ₂)
          (Δ₂ := PortBoundary.swap Γ)
          K
          (OpenProcess.mapBoundary
            (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom W₂))) :=
  openTheory_plug_wire_left_activation_equiv Party m schedulerSampler W₁ W₂ K

/-- The right wired law retains its exact structural statement. -/
example {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party (PortBoundary.tensor Δ₁ Γ))
    (W₂ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))) :
    OpenProcessActivationEquiv
      ((openTheory Party m schedulerSampler).plug
        ((openTheory Party m schedulerSampler).wire W₁ W₂) K)
      ((openTheory Party m schedulerSampler).plug W₂
        (OpenProcess.mapBoundary
          (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₂) Γ).toHom
          ((openTheory Party m schedulerSampler).wire
            (Δ₁ := PortBoundary.swap Δ₂)
            (Γ := PortBoundary.swap Δ₁)
            (Δ₂ := Γ)
            (OpenProcess.mapBoundary
              (PortBoundary.Equiv.tensorComm
                (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂)).toHom K)
            W₁))) :=
  openTheory_plug_wire_right_activation_equiv Party m schedulerSampler W₁ W₂ K

end ProcessModel

/-! ### Scheduler truth tables -/

open OpenProcessFactorization

/-- Direct canary for `openTheory_plug_par_left_activation_equiv`: its source
and target schedules select the same three distinguishable leaves. -/
example :
    [ (sourceSchedule .first, leftSchedule .first),
      (sourceSchedule .second, leftSchedule .second),
      (sourceSchedule .context, leftSchedule .context) ] =
    [([true, true], [true]), ([true, false], [false, false]), ([false], [false, true])] :=
  rfl

/-- Direct canary for `openTheory_plug_wire_left_activation_equiv`. -/
example :
    [ (sourceSchedule .first, leftSchedule .first),
      (sourceSchedule .second, leftSchedule .second),
      (sourceSchedule .context, leftSchedule .context) ] =
    [([true, true], [true]), ([true, false], [false, false]), ([false], [false, true])] :=
  rfl

/-- Direct canary for `openTheory_plug_par_right_activation_equiv`. -/
example :
    [ (sourceSchedule .first, rightSchedule .first),
      (sourceSchedule .second, rightSchedule .second),
      (sourceSchedule .context, rightSchedule .context) ] =
    [([true, true], [false, false]), ([true, false], [true]), ([false], [false, true])] :=
  rfl

/-- Direct canary for `openTheory_plug_wire_right_activation_equiv`. -/
example :
    [ (sourceSchedule .first, rightSchedule .first),
      (sourceSchedule .second, rightSchedule .second),
      (sourceSchedule .context, rightSchedule .context) ] =
    [([true, true], [false, false]), ([true, false], [true]), ([false], [false, true])] :=
  rfl

/-! ### Activation equivalence does not compare samplers -/

def samplerTree : TypeTree :=
  .node (ULift Bool) fun _ => .done

def samplerStep : Concurrent.StepOver (OpenNodeContext Unit PortBoundary.empty) Unit where
  tree := samplerTree
  semantics := ⟨schedulerNode Unit PortBoundary.empty, fun _ => ⟨⟩⟩
  next := fun _ => ()

def samplerProcess (choice : Bool) : OpenProcess Id Unit PortBoundary.empty where
  Proc := Unit
  step := fun _ => samplerStep
  stepSampler := fun _ => ⟨⟨choice⟩, fun _ => ⟨⟩⟩

/-- The activation LTS is definitionally identical even though the intrinsic
samplers choose opposite branches. -/
example : (samplerProcess true).activationLTS = (samplerProcess false).activationLTS := rfl

example : OpenProcessActivationEquiv (samplerProcess true) (samplerProcess false) := by
  change Control.DelayBisimulationEquivalent
    (samplerProcess true).activationLTS (samplerProcess false).activationLTS
  rw [show (samplerProcess true).activationLTS =
    (samplerProcess false).activationLTS from rfl]

/-- A sampler-aware semantics distinguishes the same two processes directly. -/
example : TypeTree.samplePath samplerTree ((samplerProcess true).stepSampler ()) =
    pure ⟨⟨true⟩, ⟨⟩⟩ := rfl

example : TypeTree.samplePath samplerTree ((samplerProcess false).stepSampler ()) =
    pure ⟨⟨false⟩, ⟨⟩⟩ := rfl

end Interaction.UC.EmulatesFactorizationExamples
