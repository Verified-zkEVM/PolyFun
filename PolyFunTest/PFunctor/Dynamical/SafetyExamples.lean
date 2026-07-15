/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Safety

/-!
# Examples for safety metadata and concrete-step relations

Regression tests for the metadata deliberately kept outside `DynSystem`:
`SafetySpec`, `Labeled`, `Ticketed`, and the basic `StepRel` operations.
-/

@[expose] public section

namespace PFunctor
namespace DynSystem.Examples

/-- A two-state system over the terminal interface. -/
def toggle : DynSystem Bool X.{0, 0} :=
  (fun _ => PUnit.unit) ⇆ fun state _ => !state

/-- A safety problem with one initial state and default-true policy predicates. -/
def toggleSafety : DynSystem.SafetySpec X.{0, 0} where
  State := Bool
  toDynSystem := toggle
  init state := state = false

example : toggleSafety.init false := rfl
example (state : Bool) : toggleSafety.assumptions state := trivial
example (state : Bool) : toggleSafety.safe state := trivial
example (state : Bool) :
    toggleSafety.toDynSystem.expose state = toggle.expose state := rfl
example (state : Bool) : toggleSafety.toDynSystem.update state PUnit.unit = !state := rfl

/-- Event labels may expose stable information about the source transition. -/
def toggleLabeled : DynSystem.Labeled X.{0, 0} where
  State := Bool
  toDynSystem := toggle
  Event := Bool
  event state _ := state

example (state : Bool) : toggleLabeled.event state PUnit.unit = state := rfl

/-- Tickets may identify scheduling obligations independently of directions. -/
def toggleTicketed : DynSystem.Ticketed X.{0, 0} where
  State := Bool
  toDynSystem := toggle
  Ticket := Unit
  ticket _ _ := ()

example (state : Bool) : toggleTicketed.ticket state PUnit.unit = () := rfl

section StepRelations

variable {S₁ S₂ : Type} {p₁ p₂ : PFunctor.{0, 0}}
  {system₁ : DynSystem S₁ p₁} {system₂ : DynSystem S₂ p₂}

example (rel : DynSystem.StepRel system₁ system₂)
    (step₁ : system₁.Step) (step₂ : system₂.Step) :
    DynSystem.StepRel.reverse rel step₂ step₁ ↔ rel step₁ step₂ := Iff.rfl

example (first second : DynSystem.StepRel system₁ system₂)
    (step₁ : system₁.Step) (step₂ : system₂.Step) :
    DynSystem.StepRel.inter first second step₁ step₂ ↔
      first step₁ step₂ ∧ second step₁ step₂ := Iff.rfl

end StepRelations

/-- Synchronized matching relates a concrete step to itself. -/
example (state : Bool) :
    DynSystem.StepRel.sync toggle toggle ⟨state, PUnit.unit⟩ ⟨state, PUnit.unit⟩ :=
  ⟨rfl, HEq.rfl⟩

end DynSystem.Examples
end PFunctor
