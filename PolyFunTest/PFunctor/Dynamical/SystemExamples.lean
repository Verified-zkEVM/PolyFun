/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.System

/-!
# Examples for the verification bundles and step-matching relations

Regression tests for `PFunctor/Dynamical/System.lean`: the verification bundle
`DynSystem.System` (init / assumptions / safety / invariant, with `True`
defaults), the labelled and ticketed bundles `DynSystem.Labeled` /
`DynSystem.Ticketed`, and the step-matching relations `DynSystem.DirRel`
(`top` / `reverse` / `inter` / `sync`).
-/

@[expose] public section

namespace PFunctor
namespace DynSystem.Examples

/-- A two-state toggle over the terminal interface `X` (one position, one
direction): it flips its boolean state at every step. -/
def toggle : DynSystem Bool X.{0, 0} :=
  DynSystem.mk' (fun _ => PUnit.unit) (fun s _ => !s)

/-! ## The verification bundle `System` -/

/-- The `toggle` system with `false` as its only initial state and the trivial
ambient / safety / invariant predicates (the field defaults). -/
def toggleSystem : DynSystem.System X.{0, 0} where
  State := Bool
  toDynSystem := toggle
  init := fun s => s = false

/-- The bundle's `expose` face is the underlying system's. -/
example (s : Bool) : toggleSystem.expose s = toggle.expose s := rfl

/-- `false` is an initial state. -/
example : toggleSystem.init false := rfl

/-- The default ambient / safety / invariant predicates hold everywhere. -/
example (s : Bool) : toggleSystem.assumptions s := trivial
example (s : Bool) : toggleSystem.safe s := trivial
example (s : Bool) : toggleSystem.inv s := trivial

/-! ## Labelled and ticketed bundles -/

/-- A labelled toggle: every transition is labelled with the state it left. -/
def toggleLabeled : DynSystem.Labeled X.{0, 0} where
  State := Bool
  toDynSystem := toggle
  Event := Bool
  event := fun s _ => s

example (s : Bool) : toggleLabeled.event s PUnit.unit = s := rfl

/-- A ticketed toggle over `Unit` scheduling obligations. -/
def toggleTicketed : DynSystem.Ticketed X.{0, 0} where
  State := Bool
  toDynSystem := toggle
  Ticket := Unit
  ticket := fun _ _ => ()

example (s : Bool) : toggleTicketed.ticket s PUnit.unit = () := rfl

/-! ## Step-matching relations `DirRel` -/

section
variable {S₁ S₂ : Type} {p₁ p₂ : PFunctor.{0, 0}}
  {t₁ : DynSystem S₁ p₁} {t₂ : DynSystem S₂ p₂}

/-- `reverse` swaps the two arguments of a step-matching relation. -/
example (r : DynSystem.DirRel t₁ t₂) {a : S₁} {b : S₂}
    (d₁ : p₁.B (t₁.expose a)) (d₂ : p₂.B (t₂.expose b)) :
    DynSystem.DirRel.reverse r d₂ d₁ = r d₁ d₂ := rfl

/-- `inter` is the conjunction of two step-matching relations. -/
example (r₁ r₂ : DynSystem.DirRel t₁ t₂) {a : S₁} {b : S₂}
    (d₁ : p₁.B (t₁.expose a)) (d₂ : p₂.B (t₂.expose b)) :
    DynSystem.DirRel.inter r₁ r₂ d₁ d₂ = (r₁ d₁ d₂ ∧ r₂ d₁ d₂) := rfl

end

/-- `sync` on a system with itself relates each direction to itself: equal
exposed positions and `HEq`-equal directions. -/
example (s : Bool) (d : X.B (toggle.expose s)) :
    DynSystem.DirRel.sync toggle toggle (st₁ := s) (st₂ := s) d d :=
  ⟨rfl, HEq.rfl⟩

end DynSystem.Examples
end PFunctor
