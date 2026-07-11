/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Run
public import PolyFun.PFunctor.Dynamical.Simulation
import Batteries.Tactic.Lint

/-!
# Forward refinement between dynamical systems

The lax, existential refinement notion between two verification-oriented
`DynSystem.System`s, possibly over different interface polynomials:

* `DynSystem.ForwardSimulation impl spec matchStep` — a state relation such
  that every initial implementation state is matched by an initial
  specification state, assumptions transfer forward, every implementation
  direction is matched by *some* specification direction related by the
  `DirRel` `matchStep`, and safety transfers backward.
* `ForwardSimulation.mapRun` — the induced translation of implementation runs
  into matching specification runs, with `stateRel_mapRun` / `match_mapRun` /
  `safe_of_mapRun` / `assumptions_mapRun` and the prefix-matching forms
  `relUpTo_mapRun` / `rel_mapRun`.
* `BackwardSimulation` / `Bisimulation` — the reversed and two-way packagings,
  with `Bisimulation.symm` / `Bisimulation.refl`.
* `ForwardSimulation.ofIsSimulation` — a step-synchronized simulation
  (`DynSystem.IsSimulation`, the tight notion with the coinductive
  `behavior`-equality payoff) is a forward simulation at the synchronized step
  relation `DirRel.sync`.

Instantiating the interface polynomial recovers the refinement layers of the
concrete system notions built on `DynSystem`, such as concurrent processes.
-/

@[expose] public section

universe u u₁ u₂ uA uB uA₂ uB₂

namespace PFunctor

namespace DynSystem

variable {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}

/-- `ForwardSimulation impl spec matchStep` is a forward simulation from the
implementation system `impl` to the specification system `spec`:

* every initial implementation state is related to some initial specification
  state;
* assumptions are preserved from implementation to specification;
* every implementation direction can be matched by some specification
  direction satisfying `matchStep`;
* related safe specification states imply safe implementation states.

The parameter `matchStep` determines what behavioral information the
simulation preserves at each step: choosing different `DirRel`s recovers
event-preserving, ticket-preserving, or observation-preserving refinements. -/
-- The state universes (`u₁`, `u₂`) and the interface universes are independent.
@[nolint checkUnivs]
structure ForwardSimulation (impl : System.{u₁} p) (spec : System.{u₂} q)
    (matchStep : DirRel impl.toDynSystem spec.toDynSystem := DirRel.top) where
  /-- The relation linking implementation states to specification states. -/
  stateRel : impl.State → spec.State → Prop
  init :
    ∀ stImpl, impl.init stImpl →
      ∃ stSpec, spec.init stSpec ∧ stateRel stImpl stSpec
  assumptions :
    ∀ {stImpl stSpec}, stateRel stImpl stSpec →
      impl.assumptions stImpl → spec.assumptions stSpec
  step :
    ∀ {stImpl stSpec}, stateRel stImpl stSpec →
      ∀ dImpl : p.B (impl.expose stImpl),
        ∃ dSpec : q.B (spec.expose stSpec),
          matchStep dImpl dSpec ∧
            stateRel (impl.update stImpl dImpl) (spec.update stSpec dSpec)
  safe :
    ∀ {stImpl stSpec}, stateRel stImpl stSpec →
      spec.safe stSpec → impl.safe stImpl

namespace ForwardSimulation

variable {impl : System.{u₁} p} {spec : System.{u₂} q}
  {matchStep : DirRel impl.toDynSystem spec.toDynSystem}

/-- The identity simulation on `system`, provided that `matchStep` relates
each direction to itself. This is the canonical witness that every system
refines itself. -/
def refl (system : System.{u} p)
    (matchStep : DirRel system.toDynSystem system.toDynSystem := DirRel.top)
    (hmatch : ∀ {st : system.State} (d : p.B (system.expose st)), matchStep d d) :
    ForwardSimulation system system matchStep where
  stateRel st₁ st₂ := st₁ = st₂
  init st hst := ⟨st, hst, rfl⟩
  assumptions
    | rfl, h => h
  step
    | rfl, d => ⟨d, hmatch d, rfl⟩
  safe
    | rfl, h => h

/-- Choose the matching specification direction for one implementation
direction: the specification-side step selected by the simulation for the
given implementation step. -/
noncomputable def matchDir (sim : ForwardSimulation impl spec matchStep)
    {stImpl : impl.State} {stSpec : spec.State}
    (hrel : sim.stateRel stImpl stSpec)
    (dImpl : p.B (impl.expose stImpl)) : q.B (spec.expose stSpec) :=
  Classical.choose (sim.step hrel dImpl)

/-- The chosen matching direction satisfies `matchStep` and preserves the state
relation to the next states. -/
theorem matchDir_spec (sim : ForwardSimulation impl spec matchStep)
    {stImpl : impl.State} {stSpec : spec.State}
    (hrel : sim.stateRel stImpl stSpec)
    (dImpl : p.B (impl.expose stImpl)) :
    matchStep dImpl (sim.matchDir hrel dImpl) ∧
      sim.stateRel (impl.update stImpl dImpl)
        (spec.update stSpec (sim.matchDir hrel dImpl)) :=
  Classical.choose_spec (sim.step hrel dImpl)

/-- `matchedState sim run hrel n` is the specification-side state reached after
matching the first `n` steps of the implementation run `run`, starting from an
initial related specification state witnessed by `hrel`.

This is the fundamental state-transport construction behind run-level
refinement: it recursively follows the implementation run while using the
simulation to pick matching specification directions. -/
noncomputable def matchedState (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    (n : ℕ) → {tSpec : spec.State // sim.stateRel (run.state n) tSpec}
  | 0 => ⟨stSpec, by simpa [Run.initial] using hrel⟩
  | n + 1 =>
      let prev := sim.matchedState run hrel n
      let dSpec := sim.matchDir prev.2 (run.dir n)
      let hspec := sim.matchDir_spec prev.2 (run.dir n)
      ⟨spec.update prev.1 dSpec, by
        dsimp [dSpec]
        rw [run.next_state n]
        exact hspec.2⟩

/-- The specification direction chosen to match the `n`th implementation step
of the run `run`, relative to the initial related specification state
witnessed by `hrel`. This is the stepwise witness used to build the whole
matched specification run. -/
noncomputable def matchedDir (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) (n : ℕ) :
    q.B (spec.expose (sim.matchedState run hrel n).1) :=
  sim.matchDir (sim.matchedState run hrel n).2 (run.dir n)

/-- `mapRun sim run hrel` is the specification run obtained by recursively
matching every step of the implementation run `run`, starting from an initial
related specification state witnessed by `hrel`.

So `mapRun` turns a forward simulation into an execution-level translation
from implementation runs to matching specification runs. -/
noncomputable def mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) : Run spec.toDynSystem where
  state n := (sim.matchedState run hrel n).1
  dir n := sim.matchedDir run hrel n
  next_state _ := rfl

/-- At every step index `n`, the mapped specification run remains related to
the implementation run by `stateRel`. -/
theorem stateRel_mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, sim.stateRel (run.state n) ((sim.mapRun run hrel).state n)
  | n => (sim.matchedState run hrel n).2

/-- At every step index `n`, the mapped specification direction matches the
implementation direction by `matchStep`. This is the run-level form of the
step-matching guarantee. -/
theorem match_mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, matchStep (run.dir n) ((sim.mapRun run hrel).dir n)
  | n => (sim.matchDir_spec (sim.matchedState run hrel n).2 (run.dir n)).1

/-- If every state along the mapped specification run is safe, then every
state along the implementation run is safe. This is the basic safety-transport
principle of forward simulation. -/
theorem safe_of_mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec)
    (hsafe : ∀ n, spec.safe ((sim.mapRun run hrel).state n)) :
    ∀ n, impl.safe (run.state n)
  | n => sim.safe (sim.stateRel_mapRun run hrel n) (hsafe n)

/-- If ambient assumptions hold along an implementation run, they hold along
its mapped specification run: assumptions are preserved by the run translation
induced by the simulation. -/
theorem assumptions_mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec)
    (hassumptions : ∀ n, impl.assumptions (run.state n)) :
    ∀ n, spec.assumptions ((sim.mapRun run hrel).state n) :=
  fun n => sim.assumptions (sim.stateRel_mapRun run hrel n) (hassumptions n)

/-- The first `n` steps of the mapped specification run match the first `n`
implementation steps according to `matchStep`. -/
theorem relUpTo_mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, Run.RelUpTo matchStep run (sim.mapRun run hrel) n :=
  Run.relUpTo_of_pointwise matchStep run (sim.mapRun run hrel)
    (sim.match_mapRun run hrel)

/-- The mapped specification run matches the implementation run at every
finite prefix according to `matchStep`. -/
theorem rel_mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    Run.Rel matchStep run (sim.mapRun run hrel) :=
  Run.rel_of_pointwise matchStep run (sim.mapRun run hrel)
    (sim.match_mapRun run hrel)

end ForwardSimulation

/-! ## Backward simulation and bisimulation -/

/-- `BackwardSimulation impl spec matchStep` is a forward simulation from
`spec` to `impl`, with the step-matching relation reversed accordingly. So
"backward simulation" is only a change of viewpoint, not a second primitive
notion. -/
abbrev BackwardSimulation (impl : System.{u₁} p) (spec : System.{u₂} q)
    (matchStep : DirRel impl.toDynSystem spec.toDynSystem := DirRel.top) :=
  ForwardSimulation spec impl (DirRel.reverse matchStep)

/-- `Bisimulation left right matchForth matchBack` packages one forward
simulation in each direction between `left` and `right`. By default, the
backward step-matching relation is the reversal of the forward one.

This is the main system-level equivalence witness: each side can match the
other's executions while preserving the chosen step relation. -/
-- The state universes and the interface universes are independent.
@[nolint checkUnivs]
structure Bisimulation (left : System.{u₁} p) (right : System.{u₂} q)
    (matchForth : DirRel left.toDynSystem right.toDynSystem := DirRel.top)
    (matchBack : DirRel right.toDynSystem left.toDynSystem :=
      DirRel.reverse matchForth) where
  /-- The forward simulation: `left` refines `right` under `matchForth`. -/
  forth : ForwardSimulation left right matchForth
  /-- The backward simulation: `right` refines `left` under `matchBack`. -/
  back : ForwardSimulation right left matchBack

namespace Bisimulation

variable {left : System.{u₁} p} {right : System.{u₂} q}
  {matchForth : DirRel left.toDynSystem right.toDynSystem}
  {matchBack : DirRel right.toDynSystem left.toDynSystem}

/-- Swap the two sides of a bisimulation: the symmetry principle for the
packaged equivalence witness. -/
def symm (bisim : Bisimulation left right matchForth matchBack) :
    Bisimulation right left matchBack matchForth where
  forth := bisim.back
  back := bisim.forth

/-- The identity bisimulation on `system`, provided that both step relations
relate every direction to itself: the reflexivity principle for the packaged
equivalence witness. -/
def refl (system : System.{u} p)
    (matchForth : DirRel system.toDynSystem system.toDynSystem := DirRel.top)
    (matchBack : DirRel system.toDynSystem system.toDynSystem :=
      DirRel.reverse matchForth)
    (hForth : ∀ {st : system.State} (d : p.B (system.expose st)), matchForth d d)
    (hBack : ∀ {st : system.State} (d : p.B (system.expose st)), matchBack d d) :
    Bisimulation system system matchForth matchBack where
  forth := ForwardSimulation.refl system matchForth hForth
  back := ForwardSimulation.refl system matchBack hBack

end Bisimulation

/-! ## Step-synchronized simulations as forward simulations -/

/-- A step-synchronized simulation (`IsSimulation`) between the dynamics of two
systems over a shared interface is a forward simulation at the synchronized
step relation `DirRel.sync`, given transport of the initial-state, assumption,
and safety predicates along the relation. -/
def ForwardSimulation.ofIsSimulation {S₁ S₂ : System.{u} p}
    {R : S₁.State → S₂.State → Prop}
    (hsim : IsSimulation S₁.toDynSystem S₂.toDynSystem R)
    (hinit : ∀ st₁, S₁.init st₁ → ∃ st₂, S₂.init st₂ ∧ R st₁ st₂)
    (hassumptions : ∀ {st₁ st₂}, R st₁ st₂ →
      S₁.assumptions st₁ → S₂.assumptions st₂)
    (hsafe : ∀ {st₁ st₂}, R st₁ st₂ → S₂.safe st₂ → S₁.safe st₁) :
    ForwardSimulation S₁ S₂ (DirRel.sync S₁.toDynSystem S₂.toDynSystem) where
  stateRel := R
  init := hinit
  assumptions := hassumptions
  step h d₁ :=
    ⟨hsim.expose_eq h ▸ d₁, ⟨hsim.expose_eq h, (eqRec_heq _ _).symm⟩,
      hsim.update_rel h d₁⟩
  safe := hsafe

end DynSystem

end PFunctor
