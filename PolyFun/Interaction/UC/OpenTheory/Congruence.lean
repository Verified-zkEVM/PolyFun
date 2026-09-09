/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.OpenTheory

/-!
# Congruences on open theories

A **congruence** on an open theory is a family of equivalence relations, one
on the objects of each boundary, preserved by boundary adaptation, parallel
composition, wiring, and plugging. It is the data needed to quotient a theory
(`OpenTheory.quotient`) so that coherence laws holding only up to the
congruence become equalities.

The free syntax models are quotients of raw syntax by such a congruence, and
a process model whose laws hold up to activation or sampler equivalence
carries the corresponding congruence once those equivalences are shown to be
preserved by the operations.
-/

public section

universe u

namespace Interaction
namespace UC
namespace OpenTheory

/-- A congruence on the open theory `T`: an equivalence relation on the
objects of every boundary, preserved by each operation of the theory. -/
structure Congruence (T : UC.OpenTheory.{u}) where
  /-- The equivalence relation on the objects of each boundary. -/
  setoid : ∀ Δ : PortBoundary, Setoid (T.Obj Δ)
  /-- Boundary adaptation preserves the relation. -/
  map_congr : ∀ {Δ₁ Δ₂ : PortBoundary} (φ : PortBoundary.Hom Δ₁ Δ₂) {W W' : T.Obj Δ₁},
    (setoid Δ₁).r W W' → (setoid Δ₂).r (T.map φ W) (T.map φ W')
  /-- Parallel composition preserves the relation in both arguments. -/
  par_congr : ∀ {Δ₁ Δ₂ : PortBoundary} {W₁ W₁' : T.Obj Δ₁} {W₂ W₂' : T.Obj Δ₂},
    (setoid Δ₁).r W₁ W₁' → (setoid Δ₂).r W₂ W₂' →
      (setoid _).r (T.par W₁ W₂) (T.par W₁' W₂')
  /-- Wiring preserves the relation in both arguments. -/
  wire_congr : ∀ {Δ₁ Γ Δ₂ : PortBoundary}
    {W₁ W₁' : T.Obj (PortBoundary.tensor Δ₁ Γ)}
    {W₂ W₂' : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)},
    (setoid _).r W₁ W₁' → (setoid _).r W₂ W₂' →
      (setoid _).r (T.wire W₁ W₂) (T.wire W₁' W₂')
  /-- Plugging preserves the relation in both arguments. -/
  plug_congr : ∀ {Δ : PortBoundary} {W W' : T.Obj Δ} {K K' : T.Obj (PortBoundary.swap Δ)},
    (setoid Δ).r W W' → (setoid _).r K K' →
      (setoid PortBoundary.empty).r (T.plug W K) (T.plug W' K')

namespace Congruence

variable {T : UC.OpenTheory.{u}} (E : Congruence T)

/-- The relation of the congruence at a boundary. -/
abbrev rel {Δ : PortBoundary} (W W' : T.Obj Δ) : Prop :=
  (E.setoid Δ).r W W'

theorem refl {Δ : PortBoundary} (W : T.Obj Δ) : E.rel W W :=
  (E.setoid Δ).iseqv.refl W

theorem symm {Δ : PortBoundary} {W W' : T.Obj Δ} (h : E.rel W W') : E.rel W' W :=
  (E.setoid Δ).iseqv.symm h

theorem trans {Δ : PortBoundary} {W W' W'' : T.Obj Δ} (h : E.rel W W') (h' : E.rel W' W'') :
    E.rel W W'' :=
  (E.setoid Δ).iseqv.trans h h'

theorem rel_of_eq {Δ : PortBoundary} {W W' : T.Obj Δ} (h : W = W') : E.rel W W' :=
  h ▸ E.refl W

/-- The congruence is an equivalence at every boundary. -/
theorem equivalence (Δ : PortBoundary) : Equivalence (E.rel (Δ := Δ)) :=
  (E.setoid Δ).iseqv

/-- The discrete congruence: only equal objects are related. Its quotient is
the theory itself up to the canonical bijection. -/
def eq (T : UC.OpenTheory.{u}) : Congruence T where
  setoid Δ := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  map_congr := by
    intro _ _ φ _ _ h
    exact congrArg _ h
  par_congr h₁ h₂ := h₁ ▸ h₂ ▸ rfl
  wire_congr h₁ h₂ := h₁ ▸ h₂ ▸ rfl
  plug_congr h₁ h₂ := h₁ ▸ h₂ ▸ rfl

@[simp]
theorem eq_rel {Δ : PortBoundary} {W W' : T.Obj Δ} : (Congruence.eq T).rel W W' ↔ W = W' :=
  Iff.rfl

end Congruence

end OpenTheory
end UC
end Interaction
