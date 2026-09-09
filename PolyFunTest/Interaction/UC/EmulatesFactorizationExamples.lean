/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.Emulates
import all PolyFun.Interaction.UC.OpenProcessModel
import all PolyFun.Interaction.UC.OpenProcessFactorization
public import PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.OpenProcessModel
public import PolyFun.Interaction.UC.OpenProcessFactorization
public import PolyFun.Interaction.UC.OpenSyntax.Expr

/-!
# Observation-level factorization examples

Regression checks that the UC composition theorems still reach the free
syntax models through `respectsFactorization_of_hasPlugFactorization`, and that
the process-backed `openTheory` reaches the `plug` half of the suite from an
exact `Observation.RespectsPlugComm` assumption.

Separately, the four structural factorization laws of
`OpenProcessFactorization.lean` are pinned at their exact statements, together
with the scheduler truth tables the proofs re-encode. Those are results about
`OpenProcessActivationEquiv` alone; their promotion to the *structural*
observation `Observation.activation` lives in
`PolyFun.Interaction.UC.ActivationObservation` and is exercised in
`ActivationObservationExamples`, never as a security observation.

The final canary uses syntactic equality as a concrete, nontrivial observation
on closed processes. Two processes that differ only in `stepSampler` are
activation equivalent but are not equal. This rejects any global bridge from
the structural `OpenProcessActivationEquiv` relation to a security observation.
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

/-! ### The process model consumes an exact plug-commutation law -/

section ProcessModel

variable {Party : Type u} {m : Type w → Type w'} {schedulerSampler : m (ULift.{w, 0} Bool)}
  (Obs : Observation (openTheory.{u, v, w, w'} Party m schedulerSampler))
  [Obs.RespectsPlugComm]

/-- The exact observation-level plug-commutation law is the complete structural
assumption required by the `plug` composition theorems. -/
example : Obs.RespectsPlugComm := inferInstance

/-- `Emulates.plug_compose` applies to the process model without claiming that
activation equivalence preserves security-visible data. -/
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

/-! ### Structural factorization laws, stated on activation equivalence -/

section StructuralFactorization

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

end StructuralFactorization

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

/-! ### Activation equivalence does not imply observation equivalence -/

section ErasureCanary

/-- A one-state closed process with one activated Boolean action. The sampler
is the only component that depends on `sample`. -/
def samplerProcess (sample : Bool) :
    OpenProcess.{0, 0, 0, 0} Id PUnit PortBoundary.empty where
  Proc := PUnit
  step := fun _ =>
    { tree := .node Bool fun _ => .done
      semantics :=
        ⟨{ controllers := fun _ => []
           views := fun _ => .hidden
           boundary := .activated PortBoundary.empty Bool },
         fun _ => ⟨⟩⟩
      next := fun _ => PUnit.unit }
  stepSampler := fun _ => ⟨sample, fun _ => ⟨⟩⟩

/-- Syntactic equality is a concrete observation that retains the full closed
process, including its sampler. -/
abbrev exactProcessObservation :
    Observation (openTheory PUnit Id (ULift.up true)) :=
  Observation.eq _

/-- The activation-labelled transition systems do not depend on the sampler,
so these processes are structurally activation equivalent. -/
example : OpenProcessActivationEquiv (samplerProcess true) (samplerProcess false) := by
  unfold OpenProcessActivationEquiv
  exact Control.DelayBisimulationEquivalent.refl _

/-- Exact observation distinguishes the two sampler choices. Together with
the previous example, this rejects a bridge that erases `stepSampler`. -/
example : ¬ exactProcessObservation.rel (samplerProcess true) (samplerProcess false) := by
  intro h
  injection h with _ _ hsampler
  have hs := congrFun hsampler PUnit.unit
  have hb := congrArg Prod.fst hs
  exact Bool.noConfusion hb

end ErasureCanary

end Interaction.UC.EmulatesFactorizationExamples
