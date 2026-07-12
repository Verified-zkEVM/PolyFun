/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Refinement

/-!
# Examples for simulations and refinement between dynamical systems

Regression tests for the tight and lax notions now living together in
`PFunctor/Dynamical/Refinement.lean`. Tight (`IsSimulation`): equality is a
self-simulation, `implements_of_isSimulation` turns a simulation into behaviour
equality, and a coalgebra-morphism graph is a behaviour-preserving simulation.
Lax (`ForwardSimulation` / `Bisimulation`): a step-synchronized simulation
embeds at `DirRel.sync`, systems refine and are bisimilar to themselves,
`BackwardSimulation` is the reversed forward simulation, `mapRun` transports
runs (with the `stateRel` and step-matching guarantees), and bisimulation is
symmetric.
-/

@[expose] public section

universe u

namespace PFunctor

variable {S : Type u} {p : PFunctor.{u, u}}

/-- Equality is a simulation of any dynamical system by itself. -/
def idSim (D : DynSystem S p) : DynSystem.IsSimulation D D (· = ·) where
  expose_eq h := congrArg D.expose h
  update_rel h _ := by subst h; rfl

/-- A simulation turns into behaviour equality. -/
example (D : DynSystem S p) (s : S) : D.behavior s = D.behavior s :=
  DynSystem.implements_of_isSimulation (idSim D) rfl

/-- ...and hence observational equivalence. -/
example (D : DynSystem S p) (s : S) : DynSystem.ObsEq D D s s :=
  DynSystem.obsEq_of_isSimulation (idSim D) rfl

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

/-- A step-synchronized simulation is a forward simulation at `DirRel.sync`:
the identity simulation on the trivial verification bundle. -/
noncomputable example (D : DynSystem S p) :
    DynSystem.ForwardSimulation
      ⟨S, D, fun _ => True, fun _ => True, fun _ => True, fun _ => True⟩
      ⟨S, D, fun _ => True, fun _ => True, fun _ => True, fun _ => True⟩
      (DynSystem.DirRel.sync D D) :=
  DynSystem.ForwardSimulation.ofIsSimulation (idSim D)
    (fun st _ => ⟨st, trivial, rfl⟩) (fun _ _ => trivial) (fun _ _ => trivial)

/-! ## Forward refinement, backward simulation, and bisimulation -/

/-- The trivial verification bundle on a dynamical system: every state is
initial and all ambient / safety / invariant predicates are `True`. -/
def trivSystem (D : DynSystem S p) : DynSystem.System p where
  State := S
  toDynSystem := D
  init := fun _ => True

/-- Every system refines itself: the identity forward simulation at `DirRel.top`. -/
def selfRefine (D : DynSystem S p) :
    DynSystem.ForwardSimulation (trivSystem D) (trivSystem D) :=
  DynSystem.ForwardSimulation.refl (trivSystem D) (hmatch := fun _ => trivial)

/-- `BackwardSimulation` is definitionally the reversed forward simulation. -/
example (impl spec : DynSystem.System.{u} p)
    (ms : DynSystem.DirRel impl.toDynSystem spec.toDynSystem) :
    DynSystem.BackwardSimulation impl spec ms =
      DynSystem.ForwardSimulation spec impl (DynSystem.DirRel.reverse ms) := rfl

/-- The mapped specification run stays related to the implementation run at
every step (the `stateRel` transport of `mapRun`). -/
example (impl spec : DynSystem.System.{u} p)
    {ms : DynSystem.DirRel impl.toDynSystem spec.toDynSystem}
    (sim : DynSystem.ForwardSimulation impl spec ms)
    (run : DynSystem.Run impl.toDynSystem) {t : spec.State}
    (hrel : sim.stateRel run.initial t) (n : ℕ) :
    sim.stateRel (run.state n) ((sim.mapRun run hrel).state n) :=
  sim.stateRel_mapRun run hrel n

/-- Every implementation step is matched by the mapped specification step. -/
example (impl spec : DynSystem.System.{u} p)
    {ms : DynSystem.DirRel impl.toDynSystem spec.toDynSystem}
    (sim : DynSystem.ForwardSimulation impl spec ms)
    (run : DynSystem.Run impl.toDynSystem) {t : spec.State}
    (hrel : sim.stateRel run.initial t) (n : ℕ) :
    ms (run.dir n) ((sim.mapRun run hrel).dir n) :=
  sim.match_mapRun run hrel n

/-- Every system is bisimilar to itself. -/
def selfBisim (D : DynSystem S p) :
    DynSystem.Bisimulation (trivSystem D) (trivSystem D) :=
  DynSystem.Bisimulation.refl (trivSystem D)
    (hForth := fun _ => trivial) (hBack := fun _ => trivial)

/-- Bisimulation is symmetric. -/
example (left right : DynSystem.System.{u} p)
    {mf : DynSystem.DirRel left.toDynSystem right.toDynSystem}
    {mb : DynSystem.DirRel right.toDynSystem left.toDynSystem}
    (b : DynSystem.Bisimulation left right mf mb) :
    DynSystem.Bisimulation right left mb mf := b.symm

end PFunctor
