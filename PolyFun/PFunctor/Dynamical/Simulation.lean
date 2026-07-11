/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Trajectory

/-!
# Simulations between dynamical systems

A **simulation** of one `p`-dynamical system by another is a relation on their
states that is preserved by a single synchronized step and matches the exposed
positions. Because `M p` is the terminal `p.Obj`-coalgebra, a simulation forces
related states to have equal `behavior` trees — the coinductive
`implements_of_isSimulation`, proved via the bisimulation principle
`M.corec_eq_corec`. This is the interface-generic core of the step-synchronized
simulation method VCVio's oracle machines use to discharge `Implements`.

The relation is step-synchronized (one `D₁` step matches exactly one `D₂` step).
A stutter-budget variant (several `D₂` steps per `D₁` step) is a later addition,
needed once looping / sequential composition introduces silent steps.
-/

@[expose] public section

universe u uA uB

namespace PFunctor

namespace DynSystem

variable {p : PFunctor.{uA, uB}}

/-- `IsSimulation D₁ D₂ R`: the relation `R` on states is a **simulation** —
related states expose the same position, and the two systems' updates carry
related states to related states (with the `D₁`-direction transported along the
shared exposed position). -/
structure IsSimulation (D₁ D₂ : DynSystem.{u} p)
    (R : D₁.State → D₂.State → Prop) : Prop where
  /-- Related states expose the same `p`-position. -/
  expose_eq : ∀ {s₁ s₂}, R s₁ s₂ → D₁.expose s₁ = D₂.expose s₂
  /-- One synchronized step preserves the relation. -/
  update_rel : ∀ {s₁ s₂} (h : R s₁ s₂) (d : p.B (D₁.expose s₁)),
      R (D₁.update s₁ d) (D₂.update s₂ (expose_eq h ▸ d))

/-- **A simulation preserves behaviour.** If `R` is a simulation and `R s₁ s₂`,
the two states have the same behaviour tree; hence they are observationally
equivalent (`ObsEq`). Proved by the terminal-coalgebra bisimulation principle. -/
theorem implements_of_isSimulation {D₁ D₂ : DynSystem.{u} p}
    {R : D₁.State → D₂.State → Prop} (hsim : IsSimulation D₁ D₂ R)
    {s₁ : D₁.State} {s₂ : D₂.State} (h : R s₁ s₂) :
    D₁.behavior s₁ = D₂.behavior s₂ := by
  refine M.corec_eq_corec D₁.out D₂.out R s₁ s₂ h (fun x y hxy => ?_)
  have he : D₁.expose x = D₂.expose y := hsim.expose_eq hxy
  refine ⟨D₁.expose x, D₁.update x, fun d => D₂.update y (he ▸ d), rfl, ?_,
    fun d => hsim.update_rel hxy d⟩
  simp only [DynSystem.out]
  refine Sigma.ext he.symm (Function.hfunext (congrArg p.B he.symm) fun a a' hab => ?_)
  exact heq_of_eq (congrArg (D₂.update y) (eq_of_heq (hab.trans (eqRec_heq he a').symm)))

/-- Simulation-related states are observationally equivalent. -/
theorem obsEq_of_isSimulation {D₁ D₂ : DynSystem.{u} p}
    {R : D₁.State → D₂.State → Prop} (hsim : IsSimulation D₁ D₂ R)
    {s₁ : D₁.State} {s₂ : D₂.State} (h : R s₁ s₂) : ObsEq D₁ D₂ s₁ s₂ :=
  implements_of_isSimulation hsim h

end DynSystem

end PFunctor
