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
`implements_of_isSimulation` turns a simulation into behaviour equality, a
coalgebra-morphism graph is a simulation preserving behaviour, and a
step-synchronized simulation embeds into the forward-simulation layer at
`DirRel.sync`.
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

end PFunctor
