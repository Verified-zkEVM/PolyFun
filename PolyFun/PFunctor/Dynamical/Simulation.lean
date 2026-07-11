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

Coalgebra morphisms (`Coalg.Hom`) are the functional instances of this notion:
`isSimulation_graph` shows the graph of a map commuting with the structure maps
is a simulation, so morphisms preserve behaviour (`behavior_coalgHom`). The
lax, existential counterpart between verification-oriented `System`s — matching
steps by a `DirRel` and transporting init / assumption / safety obligations —
is `DynSystem.ForwardSimulation` in `PolyFun/PFunctor/Dynamical/Refinement.lean`;
`ForwardSimulation.ofIsSimulation` embeds a step-synchronized simulation there
at the relation `DirRel.sync`.
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

/-! ## Coalgebra morphisms as simulations -/

/-- The graph of a map commuting with the coalgebra structure maps is a
simulation: coalgebra morphisms are the functional forward simulations. -/
theorem isSimulation_graph {D₁ D₂ : DynSystem.{u} p} (f : D₁.State → D₂.State)
    (hf : ∀ st, D₂.out (f st) = p.map f (D₁.out st)) :
    IsSimulation D₁ D₂ (fun st₁ st₂ => f st₁ = st₂) := by
  have hexpose : ∀ st, D₂.expose (f st) = D₁.expose st :=
    fun st => congrArg Sigma.fst (hf st)
  have hupdate : ∀ st, HEq (D₂.update (f st)) (f ∘ D₁.update st) :=
    fun st => congr_arg_heq Sigma.snd (hf st)
  refine ⟨fun {st₁ st₂} h => h ▸ (hexpose st₁).symm, fun {st₁ st₂} h d => ?_⟩
  subst h
  exact (congr_heq (hupdate st₁) (eqRec_heq _ d)).symm

/-- A coalgebra morphism between the state coalgebras of two `p`-systems is a
functional simulation: its graph is a simulation. -/
theorem isSimulation_graph_coalgHom {D₁ D₂ : DynSystem.{u} p}
    (f : Coalg.Hom p.Obj D₁.State D₂.State) :
    IsSimulation D₁ D₂ (fun st₁ st₂ => f st₁ = st₂) :=
  isSimulation_graph f fun st => (congrFun f.comm st).symm

/-- Coalgebra morphisms preserve behaviour trees. -/
theorem behavior_coalgHom {D₁ D₂ : DynSystem.{u} p}
    (f : Coalg.Hom p.Obj D₁.State D₂.State) (st : D₁.State) :
    D₂.behavior (f st) = D₁.behavior st :=
  (implements_of_isSimulation (isSimulation_graph_coalgHom f) rfl).symm

end DynSystem

end PFunctor
