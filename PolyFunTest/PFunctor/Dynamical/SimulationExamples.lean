/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Refinement

/-!
# Examples for simulations between dynamical systems

Regression tests: equality is a simulation of a system by itself,
`behavior_eq_of_isSimulation` turns a simulation into behaviour equality, a
coalgebra-morphism graph is a simulation preserving behaviour, and a
step-synchronized simulation embeds into the forward-simulation layer at
`StepRel.sync`.
-/

@[expose] public section

universe u v

namespace PFunctor

variable {p : PFunctor.{u, u}}

/-- Equality is a simulation of any dynamical system by itself. -/
def idSim (D : DynSystem.{u} p) : DynSystem.IsSimulation D D (· = ·) where
  expose_eq h := congrArg D.expose h
  update_rel h _ := by subst h; rfl

/-- A simulation turns into behaviour equality. -/
example (D : DynSystem.{u} p) (s : D.State) : D.behavior s = D.behavior s :=
  DynSystem.behavior_eq_of_isSimulation (idSim D) rfl

/-- ...and hence observational equivalence. -/
example (D : DynSystem.{u} p) (s : D.State) : DynSystem.ObsEq D D s s :=
  DynSystem.obsEq_of_isSimulation (idSim D) rfl

/-- Simulations do not require the two state types to inhabit the same
universe. -/
example {D₁ : DynSystem.{u} p} {D₂ : DynSystem.{v} p}
    {R : D₁.State → D₂.State → Prop} (sim : DynSystem.IsSimulation D₁ D₂ R)
    {s₁ : D₁.State} {s₂ : D₂.State} (h : R s₁ s₂) :
    D₁.behavior s₁ = D₂.behavior s₂ :=
  DynSystem.behavior_eq_of_isSimulation sim h

/-- The graph of the identity coalgebra morphism is a simulation. -/
example (D : DynSystem.{u} p) :
    DynSystem.IsSimulation D D (fun s₁ s₂ => Coalg.Hom.id (F := p.Obj) s₁ = s₂) :=
  DynSystem.isSimulation_graph_coalgHom (Coalg.Hom.id)

/-- Coalgebra morphisms preserve behaviour trees. -/
example (D : DynSystem.{u} p) (s : D.State) :
    D.behavior (Coalg.Hom.id (F := p.Obj) (S₁ := D.State) s) = D.behavior s :=
  DynSystem.behavior_coalgHom Coalg.Hom.id s

/-- A step-synchronized simulation is an operational forward simulation at
`StepRel.sync`. -/
example (D : DynSystem.{u} p) :
    DynSystem.ForwardSimulation D D (DynSystem.StepRel.sync D D) :=
  DynSystem.ForwardSimulation.ofIsSimulation (idSim D)

/-- The same synchronized simulation lifts to safety refinement once the three
verification-policy obligations are supplied. -/
example (D : DynSystem.{u} p) :
    DynSystem.SafetyRefinement
      ⟨D, fun _ => True, fun _ => True, fun _ => True⟩
      ⟨D, fun _ => True, fun _ => True, fun _ => True⟩
      (DynSystem.StepRel.sync D D) :=
  DynSystem.SafetyRefinement.ofIsSimulation (idSim D)
    (fun st _ => ⟨st, trivial, rfl⟩) (fun _ _ => trivial) (fun _ _ => trivial)

/-- Safety refinements compose by composing their operational simulations and
their verification-policy obligations. -/
example (D : DynSystem.{u} p) :
    let system : DynSystem.SafetySpec.{u} p :=
      ⟨D, fun _ => True, fun _ => True, fun _ => True⟩
    DynSystem.SafetyRefinement system system
      (DynSystem.StepRel.comp
        (DynSystem.StepRel.top : DynSystem.StepRel system.toDynSystem system.toDynSystem)
        (DynSystem.StepRel.top : DynSystem.StepRel system.toDynSystem system.toDynSystem)) := by
  intro system
  exact (DynSystem.SafetyRefinement.reflTop system).comp
    (DynSystem.SafetyRefinement.reflTop system)

/-! Concrete-step relations expose the expected relational algebra. -/

example (D : DynSystem.{u} p) :
    DynSystem.StepRel.comp (DynSystem.StepRel.id D) DynSystem.StepRel.top =
      (DynSystem.StepRel.top : DynSystem.StepRel D D) := by simp

example (D : DynSystem.{u} p) :
    DynSystem.StepRel.reverse
        (DynSystem.StepRel.comp DynSystem.StepRel.top (DynSystem.StepRel.id D)) =
      (DynSystem.StepRel.top : DynSystem.StepRel D D) := by
  rw [DynSystem.StepRel.reverse_comp]
  simp

/-- Mutual refinements can weaken both endpoint matching relations together. -/
example (D : DynSystem.{u} p) :
    let system : DynSystem.SafetySpec.{u} p :=
      ⟨D, fun _ => True, fun _ => True, fun _ => True⟩
    DynSystem.MutualSafetyRefinement system system
      DynSystem.StepRel.top DynSystem.StepRel.top := by
  intro system
  exact (DynSystem.MutualSafetyRefinement.refl system
    DynSystem.StepRel.top DynSystem.StepRel.top (fun _ => trivial) (fun _ => trivial)).weakenMatch
      (fun _ _ h => h) (fun _ _ h => h)

end PFunctor
