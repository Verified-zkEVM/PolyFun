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

/-- The chosen matched state and mapped run expose their supplied initial
specification state to `simp`. -/
example {SImpl SSpec : Type u} {impl : DynSystem SImpl p} {spec : DynSystem SSpec p}
    {matchStep : DynSystem.StepRel impl spec}
    (sim : DynSystem.ForwardSimulation impl spec matchStep)
    (run : DynSystem.Run impl) {initialSpec : SSpec}
    (hrel : sim.stateRel run.initial initialSpec) :
    (sim.matchedState run hrel 0).1 = initialSpec ∧
      (sim.mapRun run hrel).initial = initialSpec := by
  simp

/-- The recursive state and mapped-run projections also reduce through their
named simp equations. -/
example {SImpl SSpec : Type u} {impl : DynSystem SImpl p} {spec : DynSystem SSpec p}
    {matchStep : DynSystem.StepRel impl spec}
    (sim : DynSystem.ForwardSimulation impl spec matchStep)
    (run : DynSystem.Run impl) {initialSpec : SSpec}
    (hrel : sim.stateRel run.initial initialSpec) (n : ℕ) :
    (sim.mapRun run hrel).state n = (sim.matchedState run hrel n).1 ∧
      (sim.matchedState run hrel (n + 1)).1 =
        spec.update (sim.matchedState run hrel n).1 (sim.matchedDir run hrel n) := by
  simp

/-- The zero- and successor-step equations for finite-prefix matching are simp
rules. -/
example {SImpl SSpec : Type u} {impl : DynSystem SImpl p} {spec : DynSystem SSpec p}
    (matchStep : DynSystem.StepRel impl spec)
    (left : DynSystem.Run impl) (right : DynSystem.Run spec) (n : ℕ) :
    DynSystem.Run.RelUpTo matchStep left right 0 ∧
      (DynSystem.Run.RelUpTo matchStep left right (n + 1) ↔
        matchStep ⟨left.state 0, left.dir 0⟩ ⟨right.state 0, right.dir 0⟩ ∧
          DynSystem.Run.RelUpTo matchStep left.tail right.tail n) := by
  simp

/-- Finite-prefix matching has a pointwise elimination form. -/
example {SImpl SSpec : Type u} {impl : DynSystem SImpl p} {spec : DynSystem SSpec p}
    (matchStep : DynSystem.StepRel impl spec)
    (left : DynSystem.Run impl) (right : DynSystem.Run spec) (n : ℕ) :
    DynSystem.Run.RelUpTo matchStep left right n ↔
      ∀ k, k < n →
        matchStep ⟨left.state k, left.dir k⟩ ⟨right.state k, right.dir k⟩ :=
  DynSystem.Run.relUpTo_iff_pointwise matchStep left right n

/-- Full run matching is pointwise matching at every time index. -/
example {SImpl SSpec : Type u} {impl : DynSystem SImpl p} {spec : DynSystem SSpec p}
    (matchStep : DynSystem.StepRel impl spec)
    (left : DynSystem.Run impl) (right : DynSystem.Run spec) :
    DynSystem.Run.Rel matchStep left right ↔
      ∀ n, matchStep ⟨left.state n, left.dir n⟩ ⟨right.state n, right.dir n⟩ :=
  DynSystem.Run.rel_iff_pointwise matchStep left right

/-- The safety-refinement forwarding API has the same initial-state simp
behavior as its underlying forward simulation. -/
example {impl spec : DynSystem.SafetySpec.{u} p}
    {matchStep : DynSystem.StepRel impl.toDynSystem spec.toDynSystem}
    (sim : DynSystem.SafetyRefinement impl spec matchStep)
    (run : DynSystem.Run impl.toDynSystem) {initialSpec : spec.State}
    (hrel : sim.stateRel run.initial initialSpec) :
    (sim.matchedState run hrel 0).1 = initialSpec ∧
      (sim.mapRun run hrel).initial = initialSpec := by
  simp

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
