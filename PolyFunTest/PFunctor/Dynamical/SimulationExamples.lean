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

variable {S : Type u} {p : PFunctor.{u, u}}

/-- Equality is a simulation of any dynamical system by itself. -/
def idSim (D : DynSystem S p) : DynSystem.IsSimulation D D (· = ·) where
  expose_eq h := congrArg D.expose h
  update_rel h _ := by subst h; rfl

/-- A simulation turns into behaviour equality. -/
example (D : DynSystem S p) (s : S) : D.behavior s = D.behavior s :=
  DynSystem.behavior_eq_of_isSimulation (idSim D) rfl

/-- ...and hence observational equivalence. -/
example (D : DynSystem S p) (s : S) : DynSystem.ObsEq D D s s :=
  DynSystem.obsEq_of_isSimulation (idSim D) rfl

/-- Simulations do not require the two state types to inhabit the same
universe. -/
example {S₁ : Type u} {S₂ : Type v} {D₁ : DynSystem S₁ p} {D₂ : DynSystem S₂ p}
    {R : S₁ → S₂ → Prop} (sim : DynSystem.IsSimulation D₁ D₂ R)
    {s₁ : S₁} {s₂ : S₂} (h : R s₁ s₂) :
    D₁.behavior s₁ = D₂.behavior s₂ :=
  DynSystem.behavior_eq_of_isSimulation sim h

/-- The graph of the identity coalgebra morphism is a simulation. The coalgebra
structure is the system's own, supplied locally via `letI := D.coalg`. -/
example (D : DynSystem S p) :
    letI := D.coalg
    DynSystem.IsSimulation D D (fun s₁ s₂ => Coalg.Hom.id (F := p.Obj) s₁ = s₂) :=
  letI := D.coalg
  DynSystem.isSimulation_graph_coalgHom (Coalg.Hom.id)

/-- Coalgebra morphisms preserve behaviour trees. -/
example (D : DynSystem S p) (s : S) :
    letI := D.coalg
    D.behavior (Coalg.Hom.id (F := p.Obj) (S₁ := S) s) = D.behavior s :=
  letI := D.coalg
  DynSystem.behavior_coalgHom Coalg.Hom.id s

/-- A step-synchronized simulation is an operational forward simulation at
`StepRel.sync`. -/
example (D : DynSystem S p) :
    DynSystem.ForwardSimulation D D (DynSystem.StepRel.sync D D) :=
  DynSystem.ForwardSimulation.ofIsSimulation (idSim D)

/-- Every dynamical system operationally simulates itself. -/
def selfSimulation (D : DynSystem S p) : DynSystem.ForwardSimulation D D :=
  DynSystem.ForwardSimulation.reflTop D

/-- Mapping a run preserves the simulation relation at every step. -/
example {SImpl SSpec : Type u} {impl : DynSystem SImpl p} {spec : DynSystem SSpec p}
    {matchStep : DynSystem.StepRel impl spec}
    (sim : DynSystem.ForwardSimulation impl spec matchStep)
    (run : DynSystem.Run impl) {initialSpec : SSpec}
    (hrel : sim.stateRel run.initial initialSpec) (n : ℕ) :
    sim.stateRel (run.state n) ((sim.mapRun run hrel).state n) :=
  sim.stateRel_mapRun run hrel n

/-- The mapped run also satisfies the requested concrete-step relation. -/
example {SImpl SSpec : Type u} {impl : DynSystem SImpl p} {spec : DynSystem SSpec p}
    {matchStep : DynSystem.StepRel impl spec}
    (sim : DynSystem.ForwardSimulation impl spec matchStep)
    (run : DynSystem.Run impl) {initialSpec : SSpec}
    (hrel : sim.stateRel run.initial initialSpec) (n : ℕ) :
    matchStep ⟨run.state n, run.dir n⟩
      ⟨(sim.mapRun run hrel).state n, (sim.mapRun run hrel).dir n⟩ :=
  sim.match_mapRun run hrel n

/-- The same synchronized simulation lifts to safety refinement once the three
verification-policy obligations are supplied. -/
example (D : DynSystem S p) :
    DynSystem.SafetyRefinement
      ⟨S, D, fun _ => True, fun _ => True, fun _ => True⟩
      ⟨S, D, fun _ => True, fun _ => True, fun _ => True⟩
      (DynSystem.StepRel.sync D D) :=
  DynSystem.SafetyRefinement.ofIsSimulation (idSim D)
    (fun st _ => ⟨st, trivial, rfl⟩) (fun _ _ => trivial) (fun _ _ => trivial)

/-- Safety refinements compose by composing their operational simulations and
their verification-policy obligations. -/
example (D : DynSystem S p) :
    let system : DynSystem.SafetySpec.{u} p :=
      ⟨S, D, fun _ => True, fun _ => True, fun _ => True⟩
    DynSystem.SafetyRefinement system system
      (DynSystem.StepRel.comp
        (DynSystem.StepRel.top : DynSystem.StepRel system.toDynSystem system.toDynSystem)
        (DynSystem.StepRel.top : DynSystem.StepRel system.toDynSystem system.toDynSystem)) := by
  intro system
  exact (DynSystem.SafetyRefinement.reflTop system).comp
    (DynSystem.SafetyRefinement.reflTop system)

/-! Concrete-step relations expose the expected relational algebra. -/

example (D : DynSystem S p) :
    DynSystem.StepRel.comp (DynSystem.StepRel.id D) DynSystem.StepRel.top =
      (DynSystem.StepRel.top : DynSystem.StepRel D D) := by simp

example (D : DynSystem S p) :
    DynSystem.StepRel.reverse
        (DynSystem.StepRel.comp DynSystem.StepRel.top (DynSystem.StepRel.id D)) =
      (DynSystem.StepRel.top : DynSystem.StepRel D D) := by
  rw [DynSystem.StepRel.reverse_comp]
  simp

/-- Mutual refinements can weaken both endpoint matching relations together. -/
example (D : DynSystem S p) :
    let system : DynSystem.SafetySpec.{u} p :=
      ⟨S, D, fun _ => True, fun _ => True, fun _ => True⟩
    DynSystem.MutualSafetyRefinement system system
      DynSystem.StepRel.top DynSystem.StepRel.top := by
  intro system
  exact (DynSystem.MutualSafetyRefinement.refl system
    DynSystem.StepRel.top DynSystem.StepRel.top (fun _ => trivial) (fun _ => trivial)).weakenMatch
      (fun _ _ h => h) (fun _ _ h => h)

end PFunctor
