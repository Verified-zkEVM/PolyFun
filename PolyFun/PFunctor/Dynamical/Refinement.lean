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
`DynSystem.SafetySpec`s, possibly over different interface polynomials:

* `DynSystem.SafetyRefinement impl spec matchStep` — a state relation such
  that every initial implementation state is matched by an initial
  specification state, assumptions transfer forward, every implementation
  direction is matched by *some* specification direction related by the
  `DirRel` `matchStep`, and safety transfers backward.
* `SafetyRefinement.mapRun` — the induced translation of implementation runs
  into matching specification runs, with `stateRel_mapRun` / `match_mapRun` /
  `safe_of_mapRun` / `assumptions_mapRun` and the prefix-matching forms
  `relUpTo_mapRun` / `rel_mapRun`.
* `ReverseSafetyRefinement` / `MutualSafetyRefinement` — the reversed and two-way packagings,
  with `MutualSafetyRefinement.symm` / `MutualSafetyRefinement.refl`.
* `SafetyRefinement.ofIsSimulation` — a step-synchronized simulation
  (`DynSystem.IsSimulation`, the tight notion with the coinductive
  `behavior`-equality payoff) is a forward simulation at the synchronized step
  relation `DirRel.sync`.

Instantiating the interface polynomial recovers the refinement layers of the
concrete system notions built on `DynSystem`, such as concurrent processes.
-/

@[expose] public section

universe u u₁ u₂ u₃ uA uB uA₂ uB₂ uA₃ uB₃

namespace PFunctor

namespace DynSystem

variable {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}

/-- `SafetyRefinement impl spec matchStep` is a forward simulation from the
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
structure SafetyRefinement (impl : SafetySpec.{u₁} p) (spec : SafetySpec.{u₂} q)
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

namespace SafetyRefinement

variable {impl : SafetySpec.{u₁} p} {spec : SafetySpec.{u₂} q}
  {matchStep : DirRel impl.toDynSystem spec.toDynSystem}

/-- The identity simulation on `system`, provided that `matchStep` relates
each direction to itself. This is the canonical witness that every system
refines itself. -/
def refl (system : SafetySpec.{u} p)
    (matchStep : DirRel system.toDynSystem system.toDynSystem := DirRel.top)
    (hmatch : ∀ {st : system.State} (d : p.B (system.expose st)), matchStep d d) :
    SafetyRefinement system system matchStep where
  stateRel st₁ st₂ := st₁ = st₂
  init st hst := ⟨st, hst, rfl⟩
  assumptions
    | rfl, h => h
  step
    | rfl, d => ⟨d, hmatch d, rfl⟩
  safe
    | rfl, h => h

/-- The identity simulation using the permissive direction relation. -/
def reflTop (system : SafetySpec.{u} p) : SafetyRefinement system system DirRel.top :=
  refl system DirRel.top fun _ => trivial

/-- Composition of forward simulations. The intermediate state retained by the
composite relation is the witness needed to compose the two step simulations. -/
def comp {r : PFunctor.{uA₃, uB₃}} {middle : SafetySpec.{u₂} q} {target : SafetySpec.{u₃} r}
    {matchFirst : DirRel impl.toDynSystem middle.toDynSystem}
    {matchSecond : DirRel middle.toDynSystem target.toDynSystem}
    (second : SafetyRefinement middle target matchSecond)
    (first : SafetyRefinement impl middle matchFirst) :
    SafetyRefinement impl target (DirRel.comp matchFirst matchSecond) where
  stateRel stImpl stTarget :=
    ∃ stMiddle, first.stateRel stImpl stMiddle ∧ second.stateRel stMiddle stTarget
  init stImpl hinit := by
    obtain ⟨stMiddle, hMiddleInit, hFirst⟩ := first.init stImpl hinit
    obtain ⟨stTarget, hTargetInit, hSecond⟩ := second.init stMiddle hMiddleInit
    exact ⟨stTarget, hTargetInit, stMiddle, hFirst, hSecond⟩
  assumptions := by
    rintro stImpl stTarget ⟨stMiddle, hFirst, hSecond⟩ hAssumptions
    exact second.assumptions hSecond (first.assumptions hFirst hAssumptions)
  step := by
    rintro stImpl stTarget ⟨stMiddle, hFirst, hSecond⟩ dImpl
    obtain ⟨dMiddle, hMatchFirst, hFirst'⟩ := first.step hFirst dImpl
    obtain ⟨dTarget, hMatchSecond, hSecond'⟩ := second.step hSecond dMiddle
    exact ⟨dTarget, ⟨stMiddle, dMiddle, hMatchFirst, hMatchSecond⟩,
      ⟨middle.update stMiddle dMiddle, hFirst', hSecond'⟩⟩
  safe := by
    rintro stImpl stTarget ⟨stMiddle, hFirst, hSecond⟩ hSafe
    exact first.safe hFirst (second.safe hSecond hSafe)

/-- Choose the matching specification direction for one implementation
direction: the specification-side step selected by the simulation for the
given implementation step. -/
noncomputable def matchDir (sim : SafetyRefinement impl spec matchStep)
    {stImpl : impl.State} {stSpec : spec.State}
    (hrel : sim.stateRel stImpl stSpec)
    (dImpl : p.B (impl.expose stImpl)) : q.B (spec.expose stSpec) :=
  Classical.choose (sim.step hrel dImpl)

/-- The chosen matching direction satisfies `matchStep` and preserves the state
relation to the next states. -/
theorem matchDir_spec (sim : SafetyRefinement impl spec matchStep)
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
noncomputable def matchedState (sim : SafetyRefinement impl spec matchStep)
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
noncomputable def matchedDir (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) (n : ℕ) :
    q.B (spec.expose (sim.matchedState run hrel n).1) :=
  sim.matchDir (sim.matchedState run hrel n).2 (run.dir n)

/-- `mapRun sim run hrel` is the specification run obtained by recursively
matching every step of the implementation run `run`, starting from an initial
related specification state witnessed by `hrel`.

So `mapRun` turns a forward simulation into an execution-level translation
from implementation runs to matching specification runs. -/
noncomputable def mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) : Run spec.toDynSystem where
  state n := (sim.matchedState run hrel n).1
  dir n := sim.matchedDir run hrel n
  next_state _ := rfl

/-- At every step index `n`, the mapped specification run remains related to
the implementation run by `stateRel`. -/
theorem stateRel_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, sim.stateRel (run.state n) ((sim.mapRun run hrel).state n)
  | n => (sim.matchedState run hrel n).2

/-- At every step index `n`, the mapped specification direction matches the
implementation direction by `matchStep`. This is the run-level form of the
step-matching guarantee. -/
theorem match_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, matchStep (run.dir n) ((sim.mapRun run hrel).dir n)
  | n => (sim.matchDir_spec (sim.matchedState run hrel n).2 (run.dir n)).1

/-- If every state along the mapped specification run is safe, then every
state along the implementation run is safe. This is the basic safety-transport
principle of forward simulation. -/
theorem safe_of_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec)
    (hsafe : ∀ n, spec.safe ((sim.mapRun run hrel).state n)) :
    ∀ n, impl.safe (run.state n)
  | n => sim.safe (sim.stateRel_mapRun run hrel n) (hsafe n)

/-- If ambient assumptions hold along an implementation run, they hold along
its mapped specification run: assumptions are preserved by the run translation
induced by the simulation. -/
theorem assumptions_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec)
    (hassumptions : ∀ n, impl.assumptions (run.state n)) :
    ∀ n, spec.assumptions ((sim.mapRun run hrel).state n) :=
  fun n => sim.assumptions (sim.stateRel_mapRun run hrel n) (hassumptions n)

/-- The first `n` steps of the mapped specification run match the first `n`
implementation steps according to `matchStep`. -/
theorem relUpTo_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, Run.RelUpTo matchStep run (sim.mapRun run hrel) n :=
  Run.relUpTo_of_pointwise matchStep run (sim.mapRun run hrel)
    (sim.match_mapRun run hrel)

/-- The mapped specification run matches the implementation run at every
finite prefix according to `matchStep`. -/
theorem rel_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    Run.Rel matchStep run (sim.mapRun run hrel) :=
  Run.rel_of_pointwise matchStep run (sim.mapRun run hrel)
    (sim.match_mapRun run hrel)

end SafetyRefinement

/-! ## Reverse and mutual safety refinement -/

/-- `ReverseSafetyRefinement impl spec matchStep` is the safety refinement from
`spec` to `impl`, with the step-matching relation reversed accordingly. It is
only a change of viewpoint, not a second primitive notion. -/
abbrev ReverseSafetyRefinement (impl : SafetySpec.{u₁} p) (spec : SafetySpec.{u₂} q)
    (matchStep : DirRel impl.toDynSystem spec.toDynSystem := DirRel.top) :=
  SafetyRefinement spec impl (DirRel.reverse matchStep)

/-- `MutualSafetyRefinement left right matchForth matchBack` packages one forward
simulation in each direction between `left` and `right`. By default, the
backward step-matching relation is the reversal of the forward one.

This is the symmetric closure of `SafetyRefinement`: each side can match the
other's executions, possibly using independent state relations. It is not a
coalgebraic bisimulation. -/
-- The state universes and the interface universes are independent.
@[nolint checkUnivs]
structure MutualSafetyRefinement (left : SafetySpec.{u₁} p) (right : SafetySpec.{u₂} q)
    (matchForth : DirRel left.toDynSystem right.toDynSystem := DirRel.top)
    (matchBack : DirRel right.toDynSystem left.toDynSystem :=
      DirRel.reverse matchForth) where
  /-- The forward refinement: `left` refines `right` under `matchForth`. -/
  forth : SafetyRefinement left right matchForth
  /-- The reverse refinement: `right` refines `left` under `matchBack`. -/
  back : SafetyRefinement right left matchBack

namespace MutualSafetyRefinement

variable {left : SafetySpec.{u₁} p} {right : SafetySpec.{u₂} q}
  {matchForth : DirRel left.toDynSystem right.toDynSystem}
  {matchBack : DirRel right.toDynSystem left.toDynSystem}

/-- Swap the two sides of a mutual safety refinement. -/
def symm (both : MutualSafetyRefinement left right matchForth matchBack) :
    MutualSafetyRefinement right left matchBack matchForth where
  forth := both.back
  back := both.forth

/-- The identity mutual safety refinement on `system`, provided that both step
relations relate every direction to itself. -/
def refl (system : SafetySpec.{u} p)
    (matchForth : DirRel system.toDynSystem system.toDynSystem := DirRel.top)
    (matchBack : DirRel system.toDynSystem system.toDynSystem :=
      DirRel.reverse matchForth)
    (hForth : ∀ {st : system.State} (d : p.B (system.expose st)), matchForth d d)
    (hBack : ∀ {st : system.State} (d : p.B (system.expose st)), matchBack d d) :
    MutualSafetyRefinement system system matchForth matchBack where
  forth := SafetyRefinement.refl system matchForth hForth
  back := SafetyRefinement.refl system matchBack hBack

end MutualSafetyRefinement

/-! ## Step-synchronized simulations as forward simulations -/

/-- A step-synchronized simulation (`IsSimulation`) between the dynamics of two
systems over a shared interface is a forward simulation at the synchronized
step relation `DirRel.sync`, given transport of the initial-state, assumption,
and safety predicates along the relation. -/
def SafetyRefinement.ofIsSimulation {S₁ S₂ : SafetySpec.{u} p}
    {R : S₁.State → S₂.State → Prop}
    (hsim : IsSimulation S₁.toDynSystem S₂.toDynSystem R)
    (hinit : ∀ st₁, S₁.init st₁ → ∃ st₂, S₂.init st₂ ∧ R st₁ st₂)
    (hassumptions : ∀ {st₁ st₂}, R st₁ st₂ →
      S₁.assumptions st₁ → S₂.assumptions st₂)
    (hsafe : ∀ {st₁ st₂}, R st₁ st₂ → S₂.safe st₂ → S₁.safe st₁) :
    SafetyRefinement S₁ S₂ (DirRel.sync S₁.toDynSystem S₂.toDynSystem) where
  stateRel := R
  init := hinit
  assumptions := hassumptions
  step h d₁ :=
    ⟨hsim.expose_eq h ▸ d₁, ⟨hsim.expose_eq h, (eqRec_heq _ _).symm⟩,
      hsim.update_rel h d₁⟩
  safe := hsafe

end DynSystem

end PFunctor
