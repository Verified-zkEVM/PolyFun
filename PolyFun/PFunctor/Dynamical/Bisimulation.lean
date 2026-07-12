/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Refinement
public import PolyFun.Control.Bisimulation

/-!
# Dynamical systems as labeled transition systems

This file connects the generic `Control.WeakBisim`/`Control.StrongBisim` theory
(`PolyFun/Control/Bisimulation.lean`) to the coalgebraic behaviour semantics of
`DynSystem` (`Dynamical/Trajectory.lean`). A `p`-system is exhibited as a
`Control.LTS` (`DynSystem.toLTS`), and the main result

* `DynSystem.obsEq_of_isStrongBisim` — a generic **strong** bisimulation on the
  induced transition systems forces **equal behaviour trees**
  (`DynSystem.ObsEq`), proved through the terminal-coalgebra bisimulation
  principle `M.corec_eq_corec`

is the classical "bisimulation implies behavioural equivalence", instantiated so
the generic framework's strong bisimulation lands on the M-finality equality that
`DynSystem.behavior` already provides. This is the tie between the LTS
bisimulation framework and the project's terminal-coalgebra differentiator; the
UC `OpenProcessIso`/`Observation.bisim` layer (delay bisimulation) sits above it.

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

variable {S S₁ S₂ : Type u} {p : PFunctor.{uA, uB}}

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
`obsEq_of_isStrongBisim`. -/
private theorem move_eq_of_heq {a b : p.A} (hh : a = b)
    {μ : Option (p.B b)} {d : p.B a} (hmv : HEq μ (some d)) :
    μ = some (hh ▸ d) := by
  cases hh; exact eq_of_heq hmv

/-- **Bisimulation implies behavioural equivalence.** If `rel` is a generic
strong bisimulation between the transition systems of two `p`-systems and relates
`st₁` to `st₂`, then the two states have equal behaviour trees (`ObsEq`). Proved
by the terminal-coalgebra bisimulation principle `M.corec_eq_corec`: the `none`
self-loop forces the exposed positions to agree, and the `some d` moves force the
successors to stay related pointwise. -/
theorem obsEq_of_isStrongBisim {D₁ : DynSystem S₁ p} {D₂ : DynSystem S₂ p}
    {rel : S₁ → S₂ → Prop} (h : Control.IsStrongBisim D₁.toLTS D₂.toLTS rel)
    {st₁ : S₁} {st₂ : S₂} (hr : rel st₁ st₂) :
    DynSystem.ObsEq D₁ D₂ st₁ st₂ := by
  refine M.corec_eq_corec D₁.out D₂.out rel st₁ st₂ hr (fun x y hxy => ?_)
  -- Position agreement from the `none` self-loop.
  obtain ⟨μ₀, hlbl₀, -⟩ := h.forward hxy none
  simp only [toLTS_label] at hlbl₀
  have he : D₁.expose x = D₂.expose y :=
    (Sigma.mk.inj_iff.mp (Option.some.inj hlbl₀)).1.symm
  refine ⟨D₁.expose x, D₁.update x, fun d => D₂.update y (he ▸ d), rfl, ?_, ?_⟩
  · -- `D₂.out y = ⟨D₁.expose x, fun d => D₂.update y (he ▸ d)⟩`
    simp only [DynSystem.out]
    refine Sigma.ext he.symm (Function.hfunext (congrArg p.B he.symm) fun a a' hab => ?_)
    exact heq_of_eq (congrArg (D₂.update y) (eq_of_heq (hab.trans (eqRec_heq he a').symm)))
  · -- Successors stay related pointwise, from the `some d` moves.
    intro d
    obtain ⟨μ, hlbl, hrel⟩ := h.forward hxy (some d)
    simp only [toLTS_label] at hlbl
    -- `hlbl : some ⟨D₂.expose y, μ⟩ = some ⟨D₁.expose x, some d⟩`
    have hmv : HEq μ (some d) := (Sigma.mk.inj_iff.mp (Option.some.inj hlbl)).2
    have hμ : μ = some (he ▸ d) := move_eq_of_heq he hmv
    subst hμ
    simpa using hrel

end DynSystem
end PFunctor
