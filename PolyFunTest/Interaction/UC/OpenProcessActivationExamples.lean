/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.UC.OpenProcess

/-!
# Activation-labelled open-process examples

Regression checks that the open-process coherence relation is the generic
delay-bisimulation notion, including across independent process-state
universes, and therefore inherits the standard delay-to-weak inclusion.
-/

universe u v₁ v₂ w w'

namespace Interaction.UC.OpenProcessActivationExamples

variable {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}
    {p₁ : OpenProcess.{u, v₁, w, w'} m Party Δ}
    {p₂ : OpenProcess.{u, v₂, w, w'} m Party Δ}

/-- Activation equivalence is definitionally the generic whole-system delay
bisimulation of the activation-labelled transition systems. -/
example : OpenProcessActivationEquiv p₁ p₂ ↔
    Control.DelayBisimulationEquivalent p₁.activationLTS p₂.activationLTS :=
  Iff.rfl

/-- The standard spectrum immediately supplies weak activation bisimulation. -/
example (h : OpenProcessActivationEquiv p₁ p₂) :
    Control.WeakBisimulationEquivalent p₁.activationLTS p₂.activationLTS :=
  Control.DelayBisimulationEquivalent.toWeak h

/-- The domain-specific abbreviation retains the generic relation ergonomics. -/
example : OpenProcessActivationEquiv p₁ p₁ := by rfl

example (h : OpenProcessActivationEquiv p₁ p₂) :
    OpenProcessActivationEquiv p₂ p₁ := by
  symm
  exact h

/-- A path proved silent receives the generic silent label. -/
example (s : p₁.Proc) (tr : (p₁.step s).tree.Path)
    (h : IsSilentStep p₁ s tr) : p₁.activationLTS.label s tr = none :=
  p₁.activationLTS_label_of_silent s tr h

end Interaction.UC.OpenProcessActivationExamples
