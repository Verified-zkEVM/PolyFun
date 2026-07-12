/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Simulation
public import PolyFun.Control.Bisimulation

/-!
# Dynamical systems as labeled transition systems

This file connects the generic `Control` LTS simulation spectrum
(`PolyFun/Control/Bisimulation.lean`) to the coalgebraic behaviour semantics of
`DynSystem` (`Dynamical/Trajectory.lean`). A `p`-system is exhibited as a
`Control.LTS` (`DynSystem.toLTS`), and the main result

* `DynSystem.obsEq_of_isStrongSimulation` — a generic **strong** simulation on the
  induced transition systems forces **equal behaviour trees**
  (`DynSystem.ObsEq`), proved through the terminal-coalgebra bisimulation
  principle `M.corec_eq_corec`

is the classical "simulation implies behavioural refinement" route,
instantiated so the generic framework's strong simulation lands on the
M-finality equality that `DynSystem.behavior` already provides. UC security
observations remain separate: a structural scheduler relation is not promoted
without packet/action and effect semantics.

## The observation encoding

`toLTS` observes, at each move, the current exposed position **and** the move
itself (`Σ a : p.A, Option (p.B a)`). The `none` move is a self-loop that
observes only the position (so position equality is forced even at
direction-free positions), and each `some d` move takes the transition `update`
while observing the direction `d` (so matching is forced to be pointwise). Both
are what a *strong* bisimulation must preserve to recover behaviour-tree
equality.
-/

@[expose] public section

universe u u₁ u₂ uA uB

namespace PFunctor
namespace DynSystem

variable {S : Type u} {S₁ : Type u₁} {S₂ : Type u₂} {p : PFunctor.{uA, uB}}

/-- A `p`-dynamical system as a labeled transition system. The moves out of a
state are `Option (p.B (expose s))`: the `none` self-loop observes the position,
and each `some d` takes the `update`-transition observing the direction. Every
move observes the current exposed position, so a strong bisimulation on `toLTS`
recovers behaviour-tree equality. -/
def toLTS (D : DynSystem S p) : Control.LTS (Σ a : p.A, Option (p.B a)) where
  State := S
  Move s := Option (p.B (D.expose s))
  next s mv := mv.elim s (D.update s)
  label s mv := some ⟨D.expose s, mv⟩

@[simp] theorem toLTS_label (D : DynSystem S p) (s : S)
    (mv : Option (p.B (D.expose s))) :
    (D.toLTS).label s mv = some ⟨D.expose s, mv⟩ := rfl

@[simp] theorem toLTS_next_none (D : DynSystem S p) (s : S) :
    (D.toLTS).next s none = s := rfl

@[simp] theorem toLTS_next_some (D : DynSystem S p) (s : S) (d : p.B (D.expose s)) :
    (D.toLTS).next s (some d) = D.update s d := rfl

/-- A move heterogeneously equal to `some d` at a different exposed position is,
after transporting `d` along the position equality, literally `some (hh ▸ d)`.
Universally quantifying the positions lets `cases hh` discharge the transport.
A small private helper for the dependent bookkeeping in
`isSimulation_of_isStrongSimulation`. -/
private theorem move_eq_of_heq {a b : p.A} (hh : a = b)
    {μ : Option (p.B b)} {d : p.B a} (hmv : HEq μ (some d)) :
    μ = some (hh ▸ d) := by
  cases hh; exact eq_of_heq hmv

private theorem option_none_heq {a b : p.A} (h : a = b) :
    HEq (none : Option (p.B b)) (none : Option (p.B a)) := by
  cases h
  rfl

private theorem option_some_cast_heq {a b : p.A} (h : a = b) (d : p.B a) :
    HEq (some (h ▸ d) : Option (p.B b)) (some d : Option (p.B a)) := by
  cases h
  rfl

/-- A strong LTS simulation between the encodings of two dynamical systems is
exactly enough to build the library's synchronized `DynSystem.IsSimulation`.
The artificial `none` self-loop forces equality of exposed positions; a
`some d` move then gives the matching update. -/
theorem isSimulation_of_isStrongSimulation
    {D₁ : DynSystem S₁ p} {D₂ : DynSystem S₂ p} {rel : S₁ → S₂ → Prop}
    (h : Control.IsStrongSimulation D₁.toLTS D₂.toLTS rel) :
    DynSystem.IsSimulation D₁ D₂ rel where
  expose_eq := by
    intro s₁ s₂ hrel
    have hstep : D₁.toLTS.Step s₁ (some ⟨D₁.expose s₁, none⟩) s₁ :=
      ⟨none, rfl, rfl⟩
    obtain ⟨t₂, ⟨move₂, hlabel, _⟩, _⟩ := h hrel hstep
    exact (Sigma.mk.inj_iff.mp (Option.some.inj hlabel)).1.symm
  update_rel := by
    intro s₁ s₂ hrel d
    have hstep : D₁.toLTS.Step s₁ (some ⟨D₁.expose s₁, some d⟩)
        (D₁.update s₁ d) := ⟨some d, rfl, rfl⟩
    obtain ⟨t₂, ⟨move₂, hlabel, hnext⟩, hrel'⟩ := h hrel hstep
    have expose_eq : D₁.expose s₁ = D₂.expose s₂ :=
      (Sigma.mk.inj_iff.mp (Option.some.inj hlabel)).1.symm
    have hmove : HEq move₂ (some d) :=
      (Sigma.mk.inj_iff.mp (Option.some.inj hlabel)).2
    have : move₂ = some (expose_eq ▸ d) := move_eq_of_heq expose_eq hmove
    subst this
    change D₂.update s₂ (expose_eq ▸ d) = t₂ at hnext
    exact hnext.symm ▸ hrel'

/-- Every synchronized dynamical-system simulation induces a strong
simulation of the labelled encodings. Thus `toLTS` neither loses nor adds
simulation obligations: its position self-loop and direction moves encode the
two fields of `DynSystem.IsSimulation` exactly. -/
theorem isStrongSimulation_of_isSimulation
    {D₁ : DynSystem S₁ p} {D₂ : DynSystem S₂ p} {rel : S₁ → S₂ → Prop}
    (h : DynSystem.IsSimulation D₁ D₂ rel) :
    Control.IsStrongSimulation D₁.toLTS D₂.toLTS rel := by
  rintro s₁ s₂ hrel label t₁ ⟨move₁, hlabel, hnext⟩
  have hexpose := h.expose_eq hrel
  subst label
  subst t₁
  cases move₁ with
  | none =>
      have hlabelNone :
          some (⟨D₂.expose s₂, none⟩ : Σ a : p.A, Option (p.B a)) =
            some (⟨D₁.expose s₁, none⟩ : Σ a : p.A, Option (p.B a)) := by
        exact congrArg some (Sigma.ext hexpose.symm (option_none_heq hexpose))
      exact ⟨s₂, ⟨none, hlabelNone, rfl⟩, hrel⟩
  | some d =>
      let d₂ := hexpose ▸ d
      have hlabelSome :
          some (⟨D₂.expose s₂, some d₂⟩ : Σ a : p.A, Option (p.B a)) =
            some (⟨D₁.expose s₁, some d⟩ : Σ a : p.A, Option (p.B a)) := by
        exact congrArg some
          (Sigma.ext hexpose.symm (option_some_cast_heq hexpose d))
      exact ⟨D₂.update s₂ d₂, ⟨some d₂, hlabelSome, rfl⟩, h.update_rel hrel d⟩

/-- The generic strong-simulation condition on `toLTS` is logically
equivalent to the native synchronized simulation condition. -/
theorem isStrongSimulation_toLTS_iff_isSimulation
    {D₁ : DynSystem S₁ p} {D₂ : DynSystem S₂ p} {rel : S₁ → S₂ → Prop} :
    Control.IsStrongSimulation D₁.toLTS D₂.toLTS rel ↔
      DynSystem.IsSimulation D₁ D₂ rel :=
  ⟨isSimulation_of_isStrongSimulation, isStrongSimulation_of_isSimulation⟩

/-- Strong simulation of the induced labelled transition systems preserves
the final behavior trees of related states. The coinductive proof is delegated
to the existing `behavior_eq_of_isSimulation` theorem. -/
theorem obsEq_of_isStrongSimulation
    {D₁ : DynSystem S₁ p} {D₂ : DynSystem S₂ p} {rel : S₁ → S₂ → Prop}
    (h : Control.IsStrongSimulation D₁.toLTS D₂.toLTS rel)
    {st₁ : S₁} {st₂ : S₂} (hr : rel st₁ st₂) :
    DynSystem.ObsEq D₁ D₂ st₁ st₂ :=
  behavior_eq_of_isSimulation (isSimulation_of_isStrongSimulation h) hr

end DynSystem
end PFunctor
