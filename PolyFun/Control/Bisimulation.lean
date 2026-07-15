/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Logic.Relation
import Batteries.Tactic.Lint

/-!
# Simulation and bisimulation for labelled transition systems

This file develops the standard strong/delay/weak spectrum for labelled
transition systems with silent (`τ`) transitions.  A transition is labelled by
`none` when it is silent and by `some o` when it exposes `o`.

There are three deliberately separate layers:

* `IsStrongSimulation`, `IsDelaySimulation`, and `IsWeakSimulation` say that a
  particular relation is preserved by transitions.  They impose no totality
  condition and are therefore suitable for invariants and reachable-state
  arguments.
* `StrongBisimilar`, `DelayBisimilar`, and `WeakBisimilar` relate two particular
  states by some bisimulation.  Each is reflexive, symmetric, and transitive.
* `StrongBisimulationEquivalent`, `DelayBisimulationEquivalent`, and
  `WeakBisimulationEquivalent` additionally require the witness relation to be total
  on both state spaces.  This whole-system notion is intentionally not baked
  into the relation-local definitions.

The matching transitions are:

* strong: exactly one transition with the same label;
* delay: `τ*` before a visible transition (and `τ*` for a silent transition);
* weak: `τ*` both before and after a visible transition (and `τ*` for a silent
  transition).

The closure lemmas below make the inclusions
`strong ⊆ delay ⊆ weak` and composition of simulations reusable by
downstream models.
-/

@[expose] public section

universe uObs uState uMove uState₁ uMove₁ uState₂ uMove₂ uState₃ uMove₃

namespace Control

set_option linter.checkUnivs false in
/-- A labelled transition system.  The universes of observations, states, and
moves are independent. -/
structure LTS (Obs : Type uObs) where
  /-- States of the transition system. -/
  State : Type uState
  /-- Moves available at a state. -/
  Move : State → Type uMove
  /-- State reached by a move. -/
  next : (s : State) → Move s → State
  /-- `none` denotes a silent move; `some o` denotes a visible move. -/
  label : (s : State) → Move s → Option Obs

namespace LTS

variable {Obs : Type uObs} (L : LTS Obs)

/-- A single transition carrying the given optional observation. -/
def Step (s : L.State) (label : Option Obs) (t : L.State) : Prop :=
  ∃ move : L.Move s, L.label s move = label ∧ L.next s move = t

/-- A single silent (`τ`) transition. -/
def SilentStep (s t : L.State) : Prop := L.Step s none t

/-- A single visible transition exposing `obs`. -/
def VisibleStep (s : L.State) (obs : Obs) (t : L.State) : Prop :=
  L.Step s (some obs) t

/-- Zero or more silent (`τ`) transitions. -/
def SilentSteps : L.State → L.State → Prop :=
  Relation.ReflTransGen L.SilentStep

/-- A delay transition: silent closure for a silent label, or silent closure
followed by one visible transition for a visible label. -/
def DelayStep (s : L.State) : Option Obs → L.State → Prop
  | none, t => L.SilentSteps s t
  | some obs, t => ∃ middle, L.SilentSteps s middle ∧ L.VisibleStep middle obs t

/-- A weak transition: silent closure for a silent label, or silent closure,
one visible transition, and another silent closure for a visible label. -/
def WeakStep (s : L.State) : Option Obs → L.State → Prop
  | none, t => L.SilentSteps s t
  | some obs, t => ∃ before after,
      L.SilentSteps s before ∧ L.VisibleStep before obs after ∧ L.SilentSteps after t

@[simp] theorem delayStep_none {s t : L.State} :
    L.DelayStep s none t ↔ L.SilentSteps s t := Iff.rfl

@[simp] theorem delayStep_some {s t : L.State} {obs : Obs} :
    L.DelayStep s (some obs) t ↔
      ∃ middle, L.SilentSteps s middle ∧ L.VisibleStep middle obs t := Iff.rfl

@[simp] theorem weakStep_none {s t : L.State} :
    L.WeakStep s none t ↔ L.SilentSteps s t := Iff.rfl

@[simp] theorem weakStep_some {s t : L.State} {obs : Obs} :
    L.WeakStep s (some obs) t ↔
      ∃ before after,
        L.SilentSteps s before ∧ L.VisibleStep before obs after ∧ L.SilentSteps after t := Iff.rfl

@[simp] theorem silentSteps_refl (s : L.State) : L.SilentSteps s s := .refl

theorem SilentStep.silentSteps {s t : L.State} (h : L.SilentStep s t) :
    L.SilentSteps s t := .single h

theorem SilentSteps.trans {s t u : L.State}
    (hst : L.SilentSteps s t) (htu : L.SilentSteps t u) : L.SilentSteps s u :=
  Relation.ReflTransGen.trans hst htu

/-- A single transition is also a delay transition. -/
theorem Step.delay {s t : L.State} {label : Option Obs}
    (h : L.Step s label t) : L.DelayStep s label t := by
  cases label with
  | none => exact .single h
  | some obs => exact ⟨s, .refl, h⟩

/-- Every delay transition is a weak transition. -/
theorem DelayStep.weak {s t : L.State} {label : Option Obs}
    (h : L.DelayStep s label t) : L.WeakStep s label t := by
  cases label with
  | none => exact h
  | some obs =>
      obtain ⟨middle, hsilent, hvis⟩ := h
      exact ⟨middle, t, hsilent, hvis, .refl⟩

end LTS

variable {Obs : Type uObs}

/-! ## Relation-local simulations -/

/-- `rel` is a strong simulation: every transition on the left is matched by
one transition with the same label on the right. -/
def IsStrongSimulation (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs)
    (rel : L₁.State → L₂.State → Prop) : Prop :=
  ∀ {s₁ s₂}, rel s₁ s₂ → ∀ {label t₁}, L₁.Step s₁ label t₁ →
    ∃ t₂, L₂.Step s₂ label t₂ ∧ rel t₁ t₂

/-- `rel` is a delay simulation: a transition on the left is matched by a
delay transition on the right. -/
def IsDelaySimulation (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs)
    (rel : L₁.State → L₂.State → Prop) : Prop :=
  ∀ {s₁ s₂}, rel s₁ s₂ → ∀ {label t₁}, L₁.Step s₁ label t₁ →
    ∃ t₂, L₂.DelayStep s₂ label t₂ ∧ rel t₁ t₂

/-- `rel` is a weak simulation: a transition on the left is matched by a weak
transition on the right. -/
def IsWeakSimulation (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs)
    (rel : L₁.State → L₂.State → Prop) : Prop :=
  ∀ {s₁ s₂}, rel s₁ s₂ → ∀ {label t₁}, L₁.Step s₁ label t₁ →
    ∃ t₂, L₂.WeakStep s₂ label t₂ ∧ rel t₁ t₂

namespace IsStrongSimulation

/-- Equality strongly simulates a system by itself. -/
protected theorem refl (L : LTS Obs) : IsStrongSimulation L L Eq := by
  rintro s _ rfl label t h
  exact ⟨t, h, rfl⟩

/-- Strong simulations compose through their relational composite. -/
protected theorem comp {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs}
    {r₁₂ : L₁.State → L₂.State → Prop} {r₂₃ : L₂.State → L₃.State → Prop}
    (h₁₂ : IsStrongSimulation L₁ L₂ r₁₂)
    (h₂₃ : IsStrongSimulation L₂ L₃ r₂₃) :
    IsStrongSimulation L₁ L₃ (fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃) := by
  rintro s₁ s₃ ⟨s₂, hrel₁₂, hrel₂₃⟩ label t₁ hstep
  obtain ⟨t₂, hstep₂, hrelt₂⟩ := h₁₂ hrel₁₂ hstep
  obtain ⟨t₃, hstep₃, hrelt₃⟩ := h₂₃ hrel₂₃ hstep₂
  exact ⟨t₃, hstep₃, t₂, hrelt₂, hrelt₃⟩

/-- Strong simulation is, in particular, delay simulation. -/
protected theorem toDelay {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {rel : L₁.State → L₂.State → Prop}
    (h : IsStrongSimulation L₁ L₂ rel) : IsDelaySimulation L₁ L₂ rel := by
  intro s₁ s₂ hrel label t₁ hstep
  obtain ⟨t₂, hmatch, hrelt⟩ := h hrel hstep
  exact ⟨t₂, hmatch.delay, hrelt⟩

end IsStrongSimulation

namespace IsDelaySimulation

/-- Equality delay-simulates a system by itself. -/
protected theorem refl (L : LTS Obs) : IsDelaySimulation L L Eq :=
  IsStrongSimulation.toDelay (IsStrongSimulation.refl L)

/-- A delay simulation lifts a silent closure to a matching silent closure. -/
theorem silentSteps {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {rel : L₁.State → L₂.State → Prop}
    (h : IsDelaySimulation L₁ L₂ rel) {s₁ t₁ : L₁.State} {s₂ : L₂.State}
    (hrel : rel s₁ s₂) (hsteps : L₁.SilentSteps s₁ t₁) :
    ∃ t₂, L₂.SilentSteps s₂ t₂ ∧ rel t₁ t₂ := by
  induction hsteps with
  | refl => exact ⟨s₂, .refl, hrel⟩
  | tail hprefix hlast ih =>
      obtain ⟨middle₂, hprefix₂, hrelMiddle⟩ := ih
      obtain ⟨t₂, hlast₂, hrelTarget⟩ := h hrelMiddle hlast
      exact ⟨t₂, LTS.SilentSteps.trans L₂ hprefix₂ hlast₂, hrelTarget⟩

/-- A delay simulation lifts a delay transition to a delay transition. -/
theorem delayStep {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {rel : L₁.State → L₂.State → Prop}
    (h : IsDelaySimulation L₁ L₂ rel) {s₁ t₁ : L₁.State} {s₂ : L₂.State}
    {label : Option Obs} (hrel : rel s₁ s₂) (hstep : L₁.DelayStep s₁ label t₁) :
    ∃ t₂, L₂.DelayStep s₂ label t₂ ∧ rel t₁ t₂ := by
  cases label with
  | none => exact h.silentSteps hrel hstep
  | some obs =>
      obtain ⟨middle₁, hsilent₁, hvis₁⟩ := hstep
      obtain ⟨middle₂, hsilent₂, hrelMiddle⟩ := h.silentSteps hrel hsilent₁
      obtain ⟨t₂, hvisible₂, hrelTarget⟩ := h hrelMiddle hvis₁
      obtain ⟨before₂, hmoreSilent₂, hvis₂⟩ := hvisible₂
      exact ⟨t₂, ⟨before₂, LTS.SilentSteps.trans L₂ hsilent₂ hmoreSilent₂, hvis₂⟩,
        hrelTarget⟩

/-- Delay simulations compose through their relational composite. -/
protected theorem comp {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs}
    {r₁₂ : L₁.State → L₂.State → Prop} {r₂₃ : L₂.State → L₃.State → Prop}
    (h₁₂ : IsDelaySimulation L₁ L₂ r₁₂)
    (h₂₃ : IsDelaySimulation L₂ L₃ r₂₃) :
    IsDelaySimulation L₁ L₃ (fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃) := by
  rintro s₁ s₃ ⟨s₂, hrel₁₂, hrel₂₃⟩ label t₁ hstep
  obtain ⟨t₂, hstep₂, hrelt₂⟩ := h₁₂ hrel₁₂ hstep
  obtain ⟨t₃, hstep₃, hrelt₃⟩ := h₂₃.delayStep hrel₂₃ hstep₂
  exact ⟨t₃, hstep₃, t₂, hrelt₂, hrelt₃⟩

end IsDelaySimulation

namespace IsWeakSimulation

/-- Equality weakly simulates a system by itself. -/
protected theorem refl (L : LTS Obs) : IsWeakSimulation L L Eq := by
  rintro s _ rfl label t hstep
  exact ⟨t, (LTS.Step.delay L hstep).weak, rfl⟩

/-- A weak simulation lifts a silent closure to a matching silent closure. -/
theorem silentSteps {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {rel : L₁.State → L₂.State → Prop}
    (h : IsWeakSimulation L₁ L₂ rel) {s₁ t₁ : L₁.State} {s₂ : L₂.State}
    (hrel : rel s₁ s₂) (hsteps : L₁.SilentSteps s₁ t₁) :
    ∃ t₂, L₂.SilentSteps s₂ t₂ ∧ rel t₁ t₂ := by
  induction hsteps with
  | refl => exact ⟨s₂, .refl, hrel⟩
  | tail hprefix hlast ih =>
      obtain ⟨middle₂, hprefix₂, hrelMiddle⟩ := ih
      obtain ⟨t₂, hlast₂, hrelTarget⟩ := h hrelMiddle hlast
      exact ⟨t₂, LTS.SilentSteps.trans L₂ hprefix₂ hlast₂, hrelTarget⟩

/-- A weak simulation lifts a weak transition to a weak transition. -/
theorem weakStep {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {rel : L₁.State → L₂.State → Prop}
    (h : IsWeakSimulation L₁ L₂ rel) {s₁ t₁ : L₁.State} {s₂ : L₂.State}
    {label : Option Obs} (hrel : rel s₁ s₂) (hstep : L₁.WeakStep s₁ label t₁) :
    ∃ t₂, L₂.WeakStep s₂ label t₂ ∧ rel t₁ t₂ := by
  cases label with
  | none => exact h.silentSteps hrel hstep
  | some obs =>
      obtain ⟨before₁, after₁, hpre₁, hvis₁, hpost₁⟩ := hstep
      obtain ⟨before₂, hpre₂, hrelBefore⟩ := h.silentSteps hrel hpre₁
      obtain ⟨afterMatch₂, hvisMatch₂, hrelAfter⟩ := h hrelBefore hvis₁
      obtain ⟨visibleAt₂, after₂, hpreMore₂, hvis₂, hpost₂⟩ := hvisMatch₂
      obtain ⟨t₂, hpostMore₂, hrelTarget⟩ := h.silentSteps hrelAfter hpost₁
      exact ⟨t₂, ⟨visibleAt₂, after₂,
        LTS.SilentSteps.trans L₂ hpre₂ hpreMore₂, hvis₂,
        LTS.SilentSteps.trans L₂ hpost₂ hpostMore₂⟩, hrelTarget⟩

/-- Weak simulations compose through their relational composite. -/
protected theorem comp {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs}
    {r₁₂ : L₁.State → L₂.State → Prop} {r₂₃ : L₂.State → L₃.State → Prop}
    (h₁₂ : IsWeakSimulation L₁ L₂ r₁₂)
    (h₂₃ : IsWeakSimulation L₂ L₃ r₂₃) :
    IsWeakSimulation L₁ L₃ (fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃) := by
  rintro s₁ s₃ ⟨s₂, hrel₁₂, hrel₂₃⟩ label t₁ hstep
  obtain ⟨t₂, hstep₂, hrelt₂⟩ := h₁₂ hrel₁₂ hstep
  obtain ⟨t₃, hstep₃, hrelt₃⟩ := h₂₃.weakStep hrel₂₃ hstep₂
  exact ⟨t₃, hstep₃, t₂, hrelt₂, hrelt₃⟩

end IsWeakSimulation

/-- Delay simulation is, in particular, weak simulation. -/
theorem IsDelaySimulation.toWeak {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {rel : L₁.State → L₂.State → Prop} (h : IsDelaySimulation L₁ L₂ rel) :
    IsWeakSimulation L₁ L₂ rel := by
  intro s₁ s₂ hrel label t₁ hstep
  obtain ⟨t₂, hmatch, hrelt⟩ := h hrel hstep
  exact ⟨t₂, hmatch.weak, hrelt⟩

/-! ## Relation-local bisimulations -/

/-- A relation that strongly simulates in both directions. -/
structure IsStrongBisimulation (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs)
    (rel : L₁.State → L₂.State → Prop) : Prop where
  forward : IsStrongSimulation L₁ L₂ rel
  backward : IsStrongSimulation L₂ L₁ (fun s₂ s₁ => rel s₁ s₂)

/-- A relation that delay-simulates in both directions. -/
structure IsDelayBisimulation (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs)
    (rel : L₁.State → L₂.State → Prop) : Prop where
  forward : IsDelaySimulation L₁ L₂ rel
  backward : IsDelaySimulation L₂ L₁ (fun s₂ s₁ => rel s₁ s₂)

/-- A relation that weakly simulates in both directions. -/
structure IsWeakBisimulation (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs)
    (rel : L₁.State → L₂.State → Prop) : Prop where
  forward : IsWeakSimulation L₁ L₂ rel
  backward : IsWeakSimulation L₂ L₁ (fun s₂ s₁ => rel s₁ s₂)

namespace IsStrongBisimulation

/-- Equality is a strong bisimulation on any labelled transition system. -/
protected theorem refl (L : LTS Obs) : IsStrongBisimulation L L Eq :=
  ⟨IsStrongSimulation.refl L, by
    rintro s _ rfl label t hstep
    exact ⟨t, hstep, rfl⟩⟩

/-- Reversing a strong bisimulation relation gives a strong bisimulation in
the opposite direction. -/
protected theorem symm {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {rel : L₁.State → L₂.State → Prop}
    (h : IsStrongBisimulation L₁ L₂ rel) :
    IsStrongBisimulation L₂ L₁ (fun s₂ s₁ => rel s₁ s₂) := ⟨h.backward, h.forward⟩

/-- Strong bisimulations compose by relational composition. -/
protected theorem comp {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs}
    {r₁₂ : L₁.State → L₂.State → Prop} {r₂₃ : L₂.State → L₃.State → Prop}
    (h₁₂ : IsStrongBisimulation L₁ L₂ r₁₂)
    (h₂₃ : IsStrongBisimulation L₂ L₃ r₂₃) :
    IsStrongBisimulation L₁ L₃ (fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃) := by
  refine ⟨IsStrongSimulation.comp h₁₂.forward h₂₃.forward, ?_⟩
  rintro s₃ s₁ ⟨s₂, hr₁₂, hr₂₃⟩ label t₃ hstep₃
  obtain ⟨t₂, hstep₂, hrt₂₃⟩ := h₂₃.backward hr₂₃ hstep₃
  obtain ⟨t₁, hstep₁, hrt₁₂⟩ := h₁₂.backward hr₁₂ hstep₂
  exact ⟨t₁, hstep₁, t₂, hrt₁₂, hrt₂₃⟩

/-- Every strong bisimulation is a delay bisimulation. -/
protected theorem toDelay {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {rel : L₁.State → L₂.State → Prop}
    (h : IsStrongBisimulation L₁ L₂ rel) : IsDelayBisimulation L₁ L₂ rel :=
  ⟨IsStrongSimulation.toDelay h.forward, IsStrongSimulation.toDelay h.backward⟩

end IsStrongBisimulation

namespace IsDelayBisimulation

/-- Equality is a delay bisimulation on any labelled transition system. -/
protected theorem refl (L : LTS Obs) : IsDelayBisimulation L L Eq :=
  ⟨IsDelaySimulation.refl L, by
    rintro s _ rfl label t hstep
    exact ⟨t, LTS.Step.delay L hstep, rfl⟩⟩

/-- Reversing a delay bisimulation relation gives a delay bisimulation in the
opposite direction. -/
protected theorem symm {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {rel : L₁.State → L₂.State → Prop}
    (h : IsDelayBisimulation L₁ L₂ rel) :
    IsDelayBisimulation L₂ L₁ (fun s₂ s₁ => rel s₁ s₂) := ⟨h.backward, h.forward⟩

/-- Delay bisimulations compose by relational composition. -/
protected theorem comp {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs}
    {r₁₂ : L₁.State → L₂.State → Prop} {r₂₃ : L₂.State → L₃.State → Prop}
    (h₁₂ : IsDelayBisimulation L₁ L₂ r₁₂)
    (h₂₃ : IsDelayBisimulation L₂ L₃ r₂₃) :
    IsDelayBisimulation L₁ L₃ (fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃) := by
  refine ⟨IsDelaySimulation.comp h₁₂.forward h₂₃.forward, ?_⟩
  rintro s₃ s₁ ⟨s₂, hr₁₂, hr₂₃⟩ label t₃ hstep₃
  obtain ⟨t₂, hstep₂, hrt₂₃⟩ := h₂₃.backward hr₂₃ hstep₃
  obtain ⟨t₁, hstep₁, hrt₁₂⟩ :=
    IsDelaySimulation.delayStep h₁₂.backward hr₁₂ hstep₂
  exact ⟨t₁, hstep₁, t₂, hrt₁₂, hrt₂₃⟩

/-- Every delay bisimulation is a weak bisimulation. -/
protected theorem toWeak {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {rel : L₁.State → L₂.State → Prop}
    (h : IsDelayBisimulation L₁ L₂ rel) : IsWeakBisimulation L₁ L₂ rel :=
  ⟨IsDelaySimulation.toWeak h.forward, IsDelaySimulation.toWeak h.backward⟩

end IsDelayBisimulation

namespace IsWeakBisimulation

/-- Equality is a weak bisimulation on any labelled transition system. -/
protected theorem refl (L : LTS Obs) : IsWeakBisimulation L L Eq :=
  ⟨IsWeakSimulation.refl L, by
    rintro s _ rfl label t hstep
    exact ⟨t, (LTS.Step.delay L hstep).weak, rfl⟩⟩

/-- Reversing a weak bisimulation relation gives a weak bisimulation in the
opposite direction. -/
protected theorem symm {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {rel : L₁.State → L₂.State → Prop}
    (h : IsWeakBisimulation L₁ L₂ rel) :
    IsWeakBisimulation L₂ L₁ (fun s₂ s₁ => rel s₁ s₂) := ⟨h.backward, h.forward⟩

/-- Weak bisimulations compose by relational composition. -/
protected theorem comp {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs}
    {r₁₂ : L₁.State → L₂.State → Prop} {r₂₃ : L₂.State → L₃.State → Prop}
    (h₁₂ : IsWeakBisimulation L₁ L₂ r₁₂)
    (h₂₃ : IsWeakBisimulation L₂ L₃ r₂₃) :
    IsWeakBisimulation L₁ L₃ (fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃) := by
  refine ⟨IsWeakSimulation.comp h₁₂.forward h₂₃.forward, ?_⟩
  rintro s₃ s₁ ⟨s₂, hr₁₂, hr₂₃⟩ label t₃ hstep₃
  obtain ⟨t₂, hstep₂, hrt₂₃⟩ := h₂₃.backward hr₂₃ hstep₃
  obtain ⟨t₁, hstep₁, hrt₁₂⟩ :=
    IsWeakSimulation.weakStep h₁₂.backward hr₁₂ hstep₂
  exact ⟨t₁, hstep₁, t₂, hrt₁₂, hrt₂₃⟩

end IsWeakBisimulation

/-! ## Bisimilarity of states -/

/-- Two states are strongly bisimilar when some strong bisimulation relates
them. This notion does not assert anything about unrelated states. -/
def StrongBisimilar (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs) (s₁ : L₁.State) (s₂ : L₂.State) : Prop :=
  ∃ rel, IsStrongBisimulation L₁ L₂ rel ∧ rel s₁ s₂

/-- Two states are delay bisimilar when some delay bisimulation relates them. -/
def DelayBisimilar (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs) (s₁ : L₁.State) (s₂ : L₂.State) : Prop :=
  ∃ rel, IsDelayBisimulation L₁ L₂ rel ∧ rel s₁ s₂

/-- Two states are weakly bisimilar when some weak bisimulation relates them. -/
def WeakBisimilar (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs) (s₁ : L₁.State) (s₂ : L₂.State) : Prop :=
  ∃ rel, IsWeakBisimulation L₁ L₂ rel ∧ rel s₁ s₂

namespace StrongBisimilar

/-- Every state is strongly bisimilar to itself. -/
@[refl] protected theorem refl (L : LTS Obs) (s : L.State) : StrongBisimilar L L s s :=
  ⟨Eq, IsStrongBisimulation.refl L, rfl⟩

/-- Strong bisimilarity of states is symmetric. -/
@[symm] protected theorem symm {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {s₁ : L₁.State} {s₂ : L₂.State}
    (h : StrongBisimilar L₁ L₂ s₁ s₂) : StrongBisimilar L₂ L₁ s₂ s₁ := by
  obtain ⟨rel, hb, hrel⟩ := h
  exact ⟨fun t₂ t₁ => rel t₁ t₂, hb.symm, hrel⟩

/-- Strong bisimilarity of states is transitive. -/
@[trans] protected theorem trans {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs} {s₁ : L₁.State}
    {s₂ : L₂.State} {s₃ : L₃.State}
    (h₁₂ : StrongBisimilar L₁ L₂ s₁ s₂) (h₂₃ : StrongBisimilar L₂ L₃ s₂ s₃) :
    StrongBisimilar L₁ L₃ s₁ s₃ := by
  obtain ⟨r₁₂, hb₁₂, hr₁₂⟩ := h₁₂
  obtain ⟨r₂₃, hb₂₃, hr₂₃⟩ := h₂₃
  exact ⟨fun t₁ t₃ => ∃ t₂, r₁₂ t₁ t₂ ∧ r₂₃ t₂ t₃,
    hb₁₂.comp hb₂₃, s₂, hr₁₂, hr₂₃⟩

/-- Strongly bisimilar states are delay bisimilar. -/
protected theorem toDelay {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {s₁ : L₁.State} {s₂ : L₂.State}
    (h : StrongBisimilar L₁ L₂ s₁ s₂) : DelayBisimilar L₁ L₂ s₁ s₂ := by
  obtain ⟨rel, hb, hrel⟩ := h
  exact ⟨rel, hb.toDelay, hrel⟩

end StrongBisimilar

namespace DelayBisimilar

/-- Every state is delay bisimilar to itself. -/
@[refl] protected theorem refl (L : LTS Obs) (s : L.State) : DelayBisimilar L L s s :=
  ⟨Eq, IsDelayBisimulation.refl L, rfl⟩

/-- Delay bisimilarity of states is symmetric. -/
@[symm] protected theorem symm {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {s₁ : L₁.State} {s₂ : L₂.State}
    (h : DelayBisimilar L₁ L₂ s₁ s₂) : DelayBisimilar L₂ L₁ s₂ s₁ := by
  obtain ⟨rel, hb, hrel⟩ := h
  exact ⟨fun t₂ t₁ => rel t₁ t₂, hb.symm, hrel⟩

/-- Delay bisimilarity of states is transitive. -/
@[trans] protected theorem trans {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs} {s₁ : L₁.State}
    {s₂ : L₂.State} {s₃ : L₃.State}
    (h₁₂ : DelayBisimilar L₁ L₂ s₁ s₂) (h₂₃ : DelayBisimilar L₂ L₃ s₂ s₃) :
    DelayBisimilar L₁ L₃ s₁ s₃ := by
  obtain ⟨r₁₂, hb₁₂, hr₁₂⟩ := h₁₂
  obtain ⟨r₂₃, hb₂₃, hr₂₃⟩ := h₂₃
  exact ⟨fun t₁ t₃ => ∃ t₂, r₁₂ t₁ t₂ ∧ r₂₃ t₂ t₃,
    hb₁₂.comp hb₂₃, s₂, hr₁₂, hr₂₃⟩

/-- Delay-bisimilar states are weakly bisimilar. -/
protected theorem toWeak {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {s₁ : L₁.State} {s₂ : L₂.State}
    (h : DelayBisimilar L₁ L₂ s₁ s₂) : WeakBisimilar L₁ L₂ s₁ s₂ := by
  obtain ⟨rel, hb, hrel⟩ := h
  exact ⟨rel, hb.toWeak, hrel⟩

end DelayBisimilar

namespace WeakBisimilar

/-- Every state is weakly bisimilar to itself. -/
@[refl] protected theorem refl (L : LTS Obs) (s : L.State) : WeakBisimilar L L s s :=
  ⟨Eq, IsWeakBisimulation.refl L, rfl⟩

/-- Weak bisimilarity of states is symmetric. -/
@[symm] protected theorem symm {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} {s₁ : L₁.State} {s₂ : L₂.State}
    (h : WeakBisimilar L₁ L₂ s₁ s₂) : WeakBisimilar L₂ L₁ s₂ s₁ := by
  obtain ⟨rel, hb, hrel⟩ := h
  exact ⟨fun t₂ t₁ => rel t₁ t₂, hb.symm, hrel⟩

/-- Weak bisimilarity of states is transitive. -/
@[trans] protected theorem trans {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs} {s₁ : L₁.State}
    {s₂ : L₂.State} {s₃ : L₃.State}
    (h₁₂ : WeakBisimilar L₁ L₂ s₁ s₂) (h₂₃ : WeakBisimilar L₂ L₃ s₂ s₃) :
    WeakBisimilar L₁ L₃ s₁ s₃ := by
  obtain ⟨r₁₂, hb₁₂, hr₁₂⟩ := h₁₂
  obtain ⟨r₂₃, hb₂₃, hr₂₃⟩ := h₂₃
  exact ⟨fun t₁ t₃ => ∃ t₂, r₁₂ t₁ t₂ ∧ r₂₃ t₂ t₃,
    hb₁₂.comp hb₂₃, s₂, hr₁₂, hr₂₃⟩

end WeakBisimilar

/-! ## Whole-system equivalence -/

/-- Whole-system strong bisimulation equivalence: a strong bisimulation whose
relation is total on both state spaces. -/
def StrongBisimulationEquivalent (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs) : Prop :=
  ∃ rel, IsStrongBisimulation L₁ L₂ rel ∧
    (∀ s₁, ∃ s₂, rel s₁ s₂) ∧ (∀ s₂, ∃ s₁, rel s₁ s₂)

/-- Whole-system delay bisimulation equivalence: a delay bisimulation whose
relation is total on both state spaces. -/
def DelayBisimulationEquivalent (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs) : Prop :=
  ∃ rel, IsDelayBisimulation L₁ L₂ rel ∧
    (∀ s₁, ∃ s₂, rel s₁ s₂) ∧ (∀ s₂, ∃ s₁, rel s₁ s₂)

/-- Whole-system weak bisimulation equivalence: a weak bisimulation whose
relation is total on both state spaces. -/
def WeakBisimulationEquivalent (L₁ : LTS.{uObs, uState₁, uMove₁} Obs)
    (L₂ : LTS.{uObs, uState₂, uMove₂} Obs) : Prop :=
  ∃ rel, IsWeakBisimulation L₁ L₂ rel ∧
    (∀ s₁, ∃ s₂, rel s₁ s₂) ∧ (∀ s₂, ∃ s₁, rel s₁ s₂)

namespace StrongBisimulationEquivalent

/-- Every labelled transition system is strongly bisimulation equivalent to
itself. -/
@[refl] protected theorem refl (L : LTS Obs) : StrongBisimulationEquivalent L L :=
  ⟨Eq, IsStrongBisimulation.refl L, fun s => ⟨s, rfl⟩, fun s => ⟨s, rfl⟩⟩

/-- Whole-system strong bisimulation equivalence is symmetric. -/
@[symm] protected theorem symm {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} (h : StrongBisimulationEquivalent L₁ L₂) :
    StrongBisimulationEquivalent L₂ L₁ := by
  obtain ⟨rel, hb, hleft, hright⟩ := h
  exact ⟨fun s₂ s₁ => rel s₁ s₂, hb.symm, hright, hleft⟩

/-- Whole-system strong bisimulation equivalence is transitive. -/
@[trans] protected theorem trans {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs}
    (h₁₂ : StrongBisimulationEquivalent L₁ L₂) (h₂₃ : StrongBisimulationEquivalent L₂ L₃) :
    StrongBisimulationEquivalent L₁ L₃ := by
  obtain ⟨r₁₂, hb₁₂, hl₁₂, hr₁₂⟩ := h₁₂
  obtain ⟨r₂₃, hb₂₃, hl₂₃, hr₂₃⟩ := h₂₃
  refine ⟨fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃,
    hb₁₂.comp hb₂₃, ?_, ?_⟩
  · intro s₁; obtain ⟨s₂, h₁₂⟩ := hl₁₂ s₁; obtain ⟨s₃, h₂₃⟩ := hl₂₃ s₂
    exact ⟨s₃, s₂, h₁₂, h₂₃⟩
  · intro s₃; obtain ⟨s₂, h₂₃⟩ := hr₂₃ s₃; obtain ⟨s₁, h₁₂⟩ := hr₁₂ s₂
    exact ⟨s₁, s₂, h₁₂, h₂₃⟩

/-- Whole-system strong equivalence implies whole-system delay equivalence. -/
protected theorem toDelay {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} (h : StrongBisimulationEquivalent L₁ L₂) :
    DelayBisimulationEquivalent L₁ L₂ := by
  obtain ⟨rel, hb, hleft, hright⟩ := h
  exact ⟨rel, hb.toDelay, hleft, hright⟩

end StrongBisimulationEquivalent

namespace DelayBisimulationEquivalent

/-- Every labelled transition system is delay bisimulation equivalent to
itself. -/
@[refl] protected theorem refl (L : LTS Obs) : DelayBisimulationEquivalent L L :=
  ⟨Eq, IsDelayBisimulation.refl L, fun s => ⟨s, rfl⟩, fun s => ⟨s, rfl⟩⟩

/-- Whole-system delay bisimulation equivalence is symmetric. -/
@[symm] protected theorem symm {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} (h : DelayBisimulationEquivalent L₁ L₂) :
    DelayBisimulationEquivalent L₂ L₁ := by
  obtain ⟨rel, hb, hleft, hright⟩ := h
  exact ⟨fun s₂ s₁ => rel s₁ s₂, hb.symm, hright, hleft⟩

/-- Whole-system delay bisimulation equivalence is transitive. -/
@[trans] protected theorem trans {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs}
    (h₁₂ : DelayBisimulationEquivalent L₁ L₂) (h₂₃ : DelayBisimulationEquivalent L₂ L₃) :
    DelayBisimulationEquivalent L₁ L₃ := by
  obtain ⟨r₁₂, hb₁₂, hl₁₂, hr₁₂⟩ := h₁₂
  obtain ⟨r₂₃, hb₂₃, hl₂₃, hr₂₃⟩ := h₂₃
  refine ⟨fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃,
    hb₁₂.comp hb₂₃, ?_, ?_⟩
  · intro s₁; obtain ⟨s₂, h₁₂⟩ := hl₁₂ s₁; obtain ⟨s₃, h₂₃⟩ := hl₂₃ s₂
    exact ⟨s₃, s₂, h₁₂, h₂₃⟩
  · intro s₃; obtain ⟨s₂, h₂₃⟩ := hr₂₃ s₃; obtain ⟨s₁, h₁₂⟩ := hr₁₂ s₂
    exact ⟨s₁, s₂, h₁₂, h₂₃⟩

/-- Whole-system delay equivalence implies whole-system weak equivalence. -/
protected theorem toWeak {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} (h : DelayBisimulationEquivalent L₁ L₂) :
    WeakBisimulationEquivalent L₁ L₂ := by
  obtain ⟨rel, hb, hleft, hright⟩ := h
  exact ⟨rel, hb.toWeak, hleft, hright⟩

end DelayBisimulationEquivalent

namespace WeakBisimulationEquivalent

/-- Every labelled transition system is weakly bisimulation equivalent to
itself. -/
@[refl] protected theorem refl (L : LTS Obs) : WeakBisimulationEquivalent L L :=
  ⟨Eq, IsWeakBisimulation.refl L, fun s => ⟨s, rfl⟩, fun s => ⟨s, rfl⟩⟩

/-- Whole-system weak bisimulation equivalence is symmetric. -/
@[symm] protected theorem symm {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs} (h : WeakBisimulationEquivalent L₁ L₂) :
    WeakBisimulationEquivalent L₂ L₁ := by
  obtain ⟨rel, hb, hleft, hright⟩ := h
  exact ⟨fun s₂ s₁ => rel s₁ s₂, hb.symm, hright, hleft⟩

/-- Whole-system weak bisimulation equivalence is transitive. -/
@[trans] protected theorem trans {L₁ : LTS.{uObs, uState₁, uMove₁} Obs}
    {L₂ : LTS.{uObs, uState₂, uMove₂} Obs}
    {L₃ : LTS.{uObs, uState₃, uMove₃} Obs}
    (h₁₂ : WeakBisimulationEquivalent L₁ L₂) (h₂₃ : WeakBisimulationEquivalent L₂ L₃) :
    WeakBisimulationEquivalent L₁ L₃ := by
  obtain ⟨r₁₂, hb₁₂, hl₁₂, hr₁₂⟩ := h₁₂
  obtain ⟨r₂₃, hb₂₃, hl₂₃, hr₂₃⟩ := h₂₃
  refine ⟨fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃,
    hb₁₂.comp hb₂₃, ?_, ?_⟩
  · intro s₁; obtain ⟨s₂, h₁₂⟩ := hl₁₂ s₁; obtain ⟨s₃, h₂₃⟩ := hl₂₃ s₂
    exact ⟨s₃, s₂, h₁₂, h₂₃⟩
  · intro s₃; obtain ⟨s₂, h₂₃⟩ := hr₂₃ s₃; obtain ⟨s₁, h₁₂⟩ := hr₁₂ s₂
    exact ⟨s₁, s₂, h₁₂, h₂₃⟩

end WeakBisimulationEquivalent

end Control
