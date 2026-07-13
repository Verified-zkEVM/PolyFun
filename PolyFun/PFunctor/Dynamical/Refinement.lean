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
# Forward simulation and safety refinement between dynamical systems

This file separates operational trace simulation from verification policy:

* `DynSystem.ForwardSimulation impl spec matchStep` contains only a state
  relation and step preservation between bare dynamical systems.
* `ForwardSimulation.mapRun` is the induced translation of implementation runs
  into matching specification runs, with `stateRel_mapRun` / `match_mapRun` /
  `relUpTo_mapRun` / `rel_mapRun`.
* `DynSystem.SafetyRefinement impl spec matchStep` extends that operational core
  with initial-state coverage, assumption preservation, and safety reflection.
* `ReverseSafetyRefinement` / `MutualSafetyRefinement` — the reversed and
  two-way packagings, with reflexivity, symmetry, and transitivity operations.
  `weakenMatch` changes only the required endpoint step relation.
* `ForwardSimulation.ofIsSimulation` — a step-synchronized simulation
  (`DynSystem.IsSimulation`, the tight notion with the coinductive
  `behavior`-equality payoff) is a forward simulation at the synchronized step
  relation `StepRel.sync`.

Instantiating the interface polynomial recovers the refinement layers of the
concrete system notions built on `DynSystem`, such as concurrent processes.
-/

@[expose] public section

universe u u₁ u₂ u₃ uA uB uA₂ uB₂ uA₃ uB₃

namespace PFunctor

namespace DynSystem

variable {SImpl : Type u₁} {SSpec : Type u₂}
  {p : PFunctor.{uA, uB}} {q : PFunctor.{uA₂, uB₂}}

/-! ## Operational forward simulation -/

set_option linter.checkUnivs false in
/-- A trace-theoretic forward simulation between bare dynamical systems.

Related implementation states can match every concrete implementation step by
some related specification step, preserving both `matchStep` and the state
relation. Initial states and semantic predicates are deliberately separate. -/
-- The state universes (`u₁`, `u₂`) and the interface universes are independent.
structure ForwardSimulation (impl : DynSystem SImpl p) (spec : DynSystem SSpec q)
    (matchStep : StepRel impl spec := StepRel.top) where
  /-- The relation linking implementation states to specification states. -/
  stateRel : SImpl → SSpec → Prop
  /-- Every implementation step has a matching specification step that
  preserves the state relation. -/
  step :
    ∀ {stImpl stSpec}, stateRel stImpl stSpec →
      ∀ dImpl : p.B (impl.expose stImpl),
        ∃ dSpec : q.B (spec.expose stSpec),
          matchStep ⟨stImpl, dImpl⟩ ⟨stSpec, dSpec⟩ ∧
            stateRel (impl.update stImpl dImpl) (spec.update stSpec dSpec)

namespace ForwardSimulation

variable {impl : DynSystem SImpl p} {spec : DynSystem SSpec q}
  {matchStep : StepRel impl spec}

/-- Initial-state coverage by a forward simulation: every implementation state
selected by `initialImpl` is related to a specification state selected by
`initialSpec`. -/
def RelatesInitial (sim : ForwardSimulation impl spec matchStep)
    (initialImpl : SImpl → Prop) (initialSpec : SSpec → Prop) : Prop :=
  ∀ stImpl, initialImpl stImpl →
    ∃ stSpec, initialSpec stSpec ∧ sim.stateRel stImpl stSpec

/-- Covariant preservation of state predicates along the simulation relation. -/
def PreservesStatePred (sim : ForwardSimulation impl spec matchStep)
    (predImpl : SImpl → Prop) (predSpec : SSpec → Prop) : Prop :=
  ∀ {stImpl stSpec}, sim.stateRel stImpl stSpec → predImpl stImpl → predSpec stSpec

/-- Contravariant reflection of state predicates along the simulation relation. -/
def ReflectsStatePred (sim : ForwardSimulation impl spec matchStep)
    (predImpl : SImpl → Prop) (predSpec : SSpec → Prop) : Prop :=
  ∀ {stImpl stSpec}, sim.stateRel stImpl stSpec → predSpec stSpec → predImpl stImpl

end ForwardSimulation

set_option linter.checkUnivs false in
/-- `SafetyRefinement impl spec matchStep` is a forward simulation from the
implementation system `impl` to the specification system `spec`:

* every initial implementation state is related to some initial specification
  state;
* assumptions are preserved from implementation to specification;
* every implementation direction can be matched by some specification
  direction satisfying `matchStep`;
* related safe specification states imply safe implementation states.

The parameter `matchStep` determines what behavioral information the
simulation preserves at each step: choosing different `StepRel`s recovers
event-preserving, ticket-preserving, or observation-preserving refinements. -/
-- The state universes (`u₁`, `u₂`) and the interface universes are independent.
structure SafetyRefinement (impl : SafetySpec.{u₁} p) (spec : SafetySpec.{u₂} q)
    (matchStep : StepRel impl.toDynSystem spec.toDynSystem := StepRel.top)
    extends ForwardSimulation impl.toDynSystem spec.toDynSystem matchStep where
  /-- Every initial implementation state is related to an initial
  specification state. -/
  init : toForwardSimulation.RelatesInitial impl.init spec.init
  /-- Ambient assumptions transfer from related implementation states to
  specification states. -/
  assumptions :
    toForwardSimulation.PreservesStatePred impl.assumptions spec.assumptions
  /-- Safety reflects from related specification states to implementation
  states. -/
  safe : toForwardSimulation.ReflectsStatePred impl.safe spec.safe

namespace ForwardSimulation

variable {impl : DynSystem SImpl p} {spec : DynSystem SSpec q}
  {matchStep : StepRel impl spec}

/-- The identity simulation on `system`, provided that `matchStep` relates
each concrete step to itself. This is the canonical witness that every system
refines itself. -/
def refl {S : Type u} (system : DynSystem S p)
    (matchStep : StepRel system system := StepRel.top)
    (hmatch : ∀ step : system.Step, matchStep step step) :
    ForwardSimulation system system matchStep where
  stateRel st₁ st₂ := st₁ = st₂
  step
    | rfl, d => ⟨d, hmatch ⟨_, d⟩, rfl⟩

/-- The identity simulation using the permissive step relation. -/
def reflTop {S : Type u} (system : DynSystem S p) : ForwardSimulation system system StepRel.top :=
  refl system StepRel.top fun _ => trivial

/-- Weaken the required step relation of a forward simulation. The state
relation and its preservation proof are unchanged. -/
def weakenMatch
    {matchStrong matchWeak : StepRel impl spec}
    (sim : ForwardSimulation impl spec matchStrong)
    (hmatch : ∀ stepImpl stepSpec, matchStrong stepImpl stepSpec →
      matchWeak stepImpl stepSpec) :
    ForwardSimulation impl spec matchWeak where
  stateRel := sim.stateRel
  step hrel dImpl := by
    obtain ⟨dSpec, hstep, hnext⟩ := sim.step hrel dImpl
    exact ⟨dSpec, hmatch _ _ hstep, hnext⟩

/-- Composition of forward simulations. The intermediate state retained by the
composite relation is the witness needed to compose the two step simulations. -/
def comp {STarget : Type u₃} {r : PFunctor.{uA₃, uB₃}}
    {middle : DynSystem SSpec q} {target : DynSystem STarget r}
    {matchFirst : StepRel impl middle}
    {matchSecond : StepRel middle target}
    (second : ForwardSimulation middle target matchSecond)
    (first : ForwardSimulation impl middle matchFirst) :
    ForwardSimulation impl target (StepRel.comp matchFirst matchSecond) where
  stateRel stImpl stTarget :=
    ∃ stMiddle, first.stateRel stImpl stMiddle ∧ second.stateRel stMiddle stTarget
  step := by
    rintro stImpl stTarget ⟨stMiddle, hFirst, hSecond⟩ dImpl
    obtain ⟨dMiddle, hMatchFirst, hFirst'⟩ := first.step hFirst dImpl
    obtain ⟨dTarget, hMatchSecond, hSecond'⟩ := second.step hSecond dMiddle
    exact ⟨dTarget, ⟨⟨stMiddle, dMiddle⟩, hMatchFirst, hMatchSecond⟩,
      ⟨middle.update stMiddle dMiddle, hFirst', hSecond'⟩⟩

/-- Choose the matching specification direction for one implementation
direction: the specification-side step selected by the simulation for the
given implementation step. -/
noncomputable def matchDir (sim : ForwardSimulation impl spec matchStep)
    {stImpl : SImpl} {stSpec : SSpec}
    (hrel : sim.stateRel stImpl stSpec)
    (dImpl : p.B (impl.expose stImpl)) : q.B (spec.expose stSpec) :=
  Classical.choose (sim.step hrel dImpl)

/-- The chosen matching direction satisfies `matchStep` and preserves the state
relation to the next states. -/
theorem matchDir_spec (sim : ForwardSimulation impl spec matchStep)
    {stImpl : SImpl} {stSpec : SSpec}
    (hrel : sim.stateRel stImpl stSpec)
    (dImpl : p.B (impl.expose stImpl)) :
    matchStep ⟨stImpl, dImpl⟩ ⟨stSpec, sim.matchDir hrel dImpl⟩ ∧
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
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) :
    (n : ℕ) → {tSpec : SSpec // sim.stateRel (run.state n) tSpec}
  | 0 => ⟨stSpec, by simpa [Run.initial] using hrel⟩
  | n + 1 =>
      let prev := sim.matchedState run hrel n
      let dSpec := sim.matchDir prev.2 (run.dir n)
      let hspec := sim.matchDir_spec prev.2 (run.dir n)
      ⟨spec.update prev.1 dSpec, by
        dsimp [dSpec]
        rw [run.next_state n]
        exact hspec.2⟩

/-- Before any steps are matched, the chosen specification state is the
initial state supplied by the caller. -/
@[simp] theorem matchedState_zero (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) :
    (sim.matchedState run hrel 0).1 = stSpec :=
  rfl

/-- The specification direction chosen to match the `n`th implementation step
of the run `run`, relative to the initial related specification state
witnessed by `hrel`. This is the stepwise witness used to build the whole
matched specification run. -/
noncomputable def matchedDir (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) (n : ℕ) :
    q.B (spec.expose (sim.matchedState run hrel n).1) :=
  sim.matchDir (sim.matchedState run hrel n).2 (run.dir n)

/-- The chosen specification state after one more matched step is obtained by
updating the previous chosen state along its matched direction. -/
@[simp] theorem matchedState_succ (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) (n : ℕ) :
    (sim.matchedState run hrel (n + 1)).1 =
      spec.update (sim.matchedState run hrel n).1 (sim.matchedDir run hrel n) :=
  rfl

/-- `mapRun sim run hrel` is the specification run obtained by recursively
matching every step of the implementation run `run`, starting from an initial
related specification state witnessed by `hrel`.

So `mapRun` turns a forward simulation into an execution-level translation
from implementation runs to matching specification runs. -/
noncomputable def mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) : Run spec where
  state n := (sim.matchedState run hrel n).1
  dir n := sim.matchedDir run hrel n
  next_state _ := rfl

/-- The state of a mapped run is the state recursively chosen by the forward
simulation. -/
@[simp] theorem mapRun_state (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) (n : ℕ) :
    (sim.mapRun run hrel).state n = (sim.matchedState run hrel n).1 :=
  rfl

/-- The direction of a mapped run is the direction recursively chosen by the
forward simulation. -/
@[simp] theorem mapRun_dir (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) (n : ℕ) :
    (sim.mapRun run hrel).dir n = sim.matchedDir run hrel n :=
  rfl

/-- A mapped run starts at the specification state supplied by the caller. -/
@[simp] theorem mapRun_initial (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) :
    (sim.mapRun run hrel).initial = stSpec :=
  rfl

/-- At every step index `n`, the mapped specification run remains related to
the implementation run by `stateRel`. -/
theorem stateRel_mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, sim.stateRel (run.state n) ((sim.mapRun run hrel).state n)
  | n => (sim.matchedState run hrel n).2

/-- At every step index `n`, the mapped specification direction matches the
implementation direction by `matchStep`. This is the run-level form of the
step-matching guarantee. -/
theorem match_mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, matchStep ⟨run.state n, run.dir n⟩
      ⟨(sim.mapRun run hrel).state n, (sim.mapRun run hrel).dir n⟩
  | n => (sim.matchDir_spec (sim.matchedState run hrel n).2 (run.dir n)).1

/-- The first `n` steps of the mapped specification run match the first `n`
implementation steps according to `matchStep`. -/
theorem relUpTo_mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, Run.RelUpTo matchStep run (sim.mapRun run hrel) n :=
  Run.relUpTo_of_pointwise matchStep run (sim.mapRun run hrel)
    (sim.match_mapRun run hrel)

/-- The mapped specification run matches the implementation run at every
finite prefix according to `matchStep`. -/
theorem rel_mapRun (sim : ForwardSimulation impl spec matchStep)
    (run : Run impl) {stSpec : SSpec}
    (hrel : sim.stateRel run.initial stSpec) :
    Run.Rel matchStep run (sim.mapRun run hrel) :=
  Run.rel_of_pointwise matchStep run (sim.mapRun run hrel)
    (sim.match_mapRun run hrel)

end ForwardSimulation

/-! ## Safety-specific refinement data -/

namespace SafetyRefinement

variable {impl : SafetySpec.{u₁} p} {spec : SafetySpec.{u₂} q}
  {matchStep : StepRel impl.toDynSystem spec.toDynSystem}

/-- The identity safety refinement, provided that `matchStep` relates each
concrete step to itself. -/
def refl (system : SafetySpec.{u} p)
    (matchStep : StepRel system.toDynSystem system.toDynSystem := StepRel.top)
    (hmatch : ∀ step : system.toDynSystem.Step, matchStep step step) :
    SafetyRefinement system system matchStep where
  toForwardSimulation := ForwardSimulation.refl system.toDynSystem matchStep hmatch
  init st hst := ⟨st, hst, rfl⟩
  assumptions
    | rfl, h => h
  safe
    | rfl, h => h

/-- The identity safety refinement using the permissive step relation. -/
def reflTop (system : SafetySpec.{u} p) : SafetyRefinement system system StepRel.top :=
  refl system StepRel.top fun _ => trivial

/-- Weaken the required step relation of a safety refinement while retaining
its operational state relation and all verification-policy obligations. -/
def weakenMatch
    {matchStrong matchWeak : StepRel impl.toDynSystem spec.toDynSystem}
    (sim : SafetyRefinement impl spec matchStrong)
    (hmatch : ∀ stepImpl stepSpec, matchStrong stepImpl stepSpec →
      matchWeak stepImpl stepSpec) :
    SafetyRefinement impl spec matchWeak where
  toForwardSimulation := sim.toForwardSimulation.weakenMatch hmatch
  init := sim.init
  assumptions := sim.assumptions
  safe := sim.safe

/-- Composition of safety refinements, using ordinary relational composition
on their concrete-step relations. -/
def comp {r : PFunctor.{uA₃, uB₃}} {middle : SafetySpec.{u₂} q}
    {target : SafetySpec.{u₃} r}
    {matchFirst : StepRel impl.toDynSystem middle.toDynSystem}
    {matchSecond : StepRel middle.toDynSystem target.toDynSystem}
    (second : SafetyRefinement middle target matchSecond)
    (first : SafetyRefinement impl middle matchFirst) :
    SafetyRefinement impl target (StepRel.comp matchFirst matchSecond) where
  toForwardSimulation := second.toForwardSimulation.comp first.toForwardSimulation
  init stImpl hinit := by
    obtain ⟨stMiddle, hMiddleInit, hFirst⟩ := first.init stImpl hinit
    obtain ⟨stTarget, hTargetInit, hSecond⟩ := second.init stMiddle hMiddleInit
    exact ⟨stTarget, hTargetInit, stMiddle, hFirst, hSecond⟩
  assumptions := by
    rintro stImpl stTarget ⟨stMiddle, hFirst, hSecond⟩ hAssumptions
    exact second.assumptions hSecond (first.assumptions hFirst hAssumptions)
  safe := by
    rintro stImpl stTarget ⟨stMiddle, hFirst, hSecond⟩ hSafe
    exact first.safe hFirst (second.safe hSecond hSafe)

/-! Forwarding abbreviations preserve the existing dot-notation while making
the operational ownership of the run-translation API explicit. -/

/-- The specification direction chosen by the underlying forward simulation.
This forwarding abbreviation preserves the `sim.matchDir` API for safety
refinements. -/
noncomputable abbrev matchDir (sim : SafetyRefinement impl spec matchStep)
    {stImpl : impl.State} {stSpec : spec.State}
    (hrel : sim.stateRel stImpl stSpec)
    (dImpl : p.B (impl.expose stImpl)) : q.B (spec.expose stSpec) :=
  sim.toForwardSimulation.matchDir hrel dImpl

/-- The direction chosen through a safety refinement satisfies its requested
step relation and preserves the underlying simulation relation. -/
theorem matchDir_spec (sim : SafetyRefinement impl spec matchStep)
    {stImpl : impl.State} {stSpec : spec.State}
    (hrel : sim.stateRel stImpl stSpec)
    (dImpl : p.B (impl.expose stImpl)) :
    matchStep ⟨stImpl, dImpl⟩ ⟨stSpec, sim.matchDir hrel dImpl⟩ ∧
      sim.stateRel (impl.update stImpl dImpl)
        (spec.update stSpec (sim.matchDir hrel dImpl)) :=
  sim.toForwardSimulation.matchDir_spec hrel dImpl

/-- The related specification state constructed by the underlying forward
simulation after `n` implementation steps. -/
noncomputable abbrev matchedState (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :=
  sim.toForwardSimulation.matchedState run hrel

/-- Before any steps are matched, a safety refinement retains the
specification state supplied by the caller. -/
@[simp] theorem matchedState_zero (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    (sim.matchedState run hrel 0).1 = stSpec :=
  sim.toForwardSimulation.matchedState_zero run hrel

/-- The direction selected by the underlying forward simulation for the `n`th
implementation step. -/
noncomputable abbrev matchedDir (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) (n : ℕ) :=
  sim.toForwardSimulation.matchedDir run hrel n

/-- The chosen specification state after one more matched step is obtained by
updating the previous chosen state along its matched direction. -/
theorem matchedState_succ (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) (n : ℕ) :
    (sim.matchedState run hrel (n + 1)).1 =
      spec.update (sim.matchedState run hrel n).1 (sim.matchedDir run hrel n) :=
  sim.toForwardSimulation.matchedState_succ run hrel n

/-- Translate an implementation run using the underlying forward simulation.
This forwarding abbreviation preserves the `sim.mapRun` API for safety
refinements. -/
noncomputable abbrev mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :=
  sim.toForwardSimulation.mapRun run hrel

/-- The state of a run mapped through a safety refinement is the state chosen
by its underlying forward simulation. -/
@[simp] theorem mapRun_state (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) (n : ℕ) :
    (sim.mapRun run hrel).state n = (sim.matchedState run hrel n).1 :=
  sim.toForwardSimulation.mapRun_state run hrel n

/-- The direction of a run mapped through a safety refinement is the direction
chosen by its underlying forward simulation. -/
theorem mapRun_dir (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) (n : ℕ) :
    (sim.mapRun run hrel).dir n = sim.matchedDir run hrel n :=
  sim.toForwardSimulation.mapRun_dir run hrel n

/-- A mapped safety-specification run remains related to the implementation
run at every state index. -/
theorem stateRel_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, sim.stateRel (run.state n) ((sim.mapRun run hrel).state n) :=
  sim.toForwardSimulation.stateRel_mapRun run hrel

/-- Every step of a mapped safety-specification run satisfies the requested
step-matching relation. -/
theorem match_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, matchStep ⟨run.state n, run.dir n⟩
      ⟨(sim.mapRun run hrel).state n, (sim.mapRun run hrel).dir n⟩ :=
  sim.toForwardSimulation.match_mapRun run hrel

/-- Every finite prefix of the mapped run matches the corresponding
implementation prefix. -/
theorem relUpTo_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    ∀ n, Run.RelUpTo matchStep run (sim.mapRun run hrel) n :=
  sim.toForwardSimulation.relUpTo_mapRun run hrel

/-- The mapped run matches the implementation run at every finite prefix. -/
theorem rel_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    Run.Rel matchStep run (sim.mapRun run hrel) :=
  sim.toForwardSimulation.rel_mapRun run hrel

/-- A run mapped through a safety refinement starts at the specification state
supplied by the caller. -/
@[simp] theorem mapRun_initial (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec) :
    (sim.mapRun run hrel).initial = stSpec :=
  sim.toForwardSimulation.mapRun_initial run hrel

/-- If every state along the mapped specification run is safe, then every
state along the implementation run is safe. -/
theorem safe_of_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec)
    (hsafe : ∀ n, spec.safe ((sim.mapRun run hrel).state n)) :
    ∀ n, impl.safe (run.state n)
  | n => sim.safe (sim.stateRel_mapRun run hrel n) (hsafe n)

/-- If ambient assumptions hold along an implementation run, they hold along
its mapped specification run. -/
theorem assumptions_mapRun (sim : SafetyRefinement impl spec matchStep)
    (run : Run impl.toDynSystem) {stSpec : spec.State}
    (hrel : sim.stateRel run.initial stSpec)
    (hassumptions : ∀ n, impl.assumptions (run.state n)) :
    ∀ n, spec.assumptions ((sim.mapRun run hrel).state n) :=
  fun n => sim.assumptions (sim.stateRel_mapRun run hrel n) (hassumptions n)

end SafetyRefinement

/-! ## Reverse and mutual safety refinement -/

/-- `ReverseSafetyRefinement impl spec matchStep` is the safety refinement from
`spec` to `impl`, with the step-matching relation reversed accordingly. It is
only a change of viewpoint, not a second primitive notion. -/
abbrev ReverseSafetyRefinement (impl : SafetySpec.{u₁} p) (spec : SafetySpec.{u₂} q)
    (matchStep : StepRel impl.toDynSystem spec.toDynSystem := StepRel.top) :=
  SafetyRefinement spec impl (StepRel.reverse matchStep)

set_option linter.checkUnivs false in
/-- `MutualSafetyRefinement left right matchForth matchBack` packages one forward
simulation in each direction between `left` and `right`. By default, the
backward step-matching relation is the reversal of the forward one.

This is the symmetric closure of `SafetyRefinement`: each side can match the
other's executions, possibly using independent state relations. It is not a
coalgebraic bisimulation. -/
-- The state universes and the interface universes are independent.
structure MutualSafetyRefinement (left : SafetySpec.{u₁} p) (right : SafetySpec.{u₂} q)
    (matchForth : StepRel left.toDynSystem right.toDynSystem := StepRel.top)
    (matchBack : StepRel right.toDynSystem left.toDynSystem :=
      StepRel.reverse matchForth) where
  /-- The forward refinement: `left` refines `right` under `matchForth`. -/
  forth : SafetyRefinement left right matchForth
  /-- The reverse refinement: `right` refines `left` under `matchBack`. -/
  back : SafetyRefinement right left matchBack

namespace MutualSafetyRefinement

variable {left : SafetySpec.{u₁} p} {right : SafetySpec.{u₂} q}
  {matchForth : StepRel left.toDynSystem right.toDynSystem}
  {matchBack : StepRel right.toDynSystem left.toDynSystem}

/-- Swap the two sides of a mutual safety refinement. -/
def symm (both : MutualSafetyRefinement left right matchForth matchBack) :
    MutualSafetyRefinement right left matchBack matchForth where
  forth := both.back
  back := both.forth

/-- Weaken the required forward and backward step relations without changing
either operational simulation or its verification-policy obligations. -/
def weakenMatch
    {matchForthWeak : StepRel left.toDynSystem right.toDynSystem}
    {matchBackWeak : StepRel right.toDynSystem left.toDynSystem}
    (both : MutualSafetyRefinement left right matchForth matchBack)
    (hForth : ∀ stepLeft stepRight, matchForth stepLeft stepRight →
      matchForthWeak stepLeft stepRight)
    (hBack : ∀ stepRight stepLeft, matchBack stepRight stepLeft →
      matchBackWeak stepRight stepLeft) :
    MutualSafetyRefinement left right matchForthWeak matchBackWeak where
  forth := both.forth.weakenMatch hForth
  back := both.back.weakenMatch hBack

/-- The identity mutual safety refinement on `system`, provided that both step
relations relate every direction to itself. -/
def refl (system : SafetySpec.{u} p)
    (matchForth : StepRel system.toDynSystem system.toDynSystem := StepRel.top)
    (matchBack : StepRel system.toDynSystem system.toDynSystem :=
      StepRel.reverse matchForth)
    (hForth : ∀ step : system.toDynSystem.Step, matchForth step step)
    (hBack : ∀ step : system.toDynSystem.Step, matchBack step step) :
    MutualSafetyRefinement system system matchForth matchBack where
  forth := SafetyRefinement.refl system matchForth hForth
  back := SafetyRefinement.refl system matchBack hBack

/-- Compose mutual safety refinements when the composed forward and backward
step relations imply the relations required by the endpoints. -/
def trans {r : PFunctor.{uA₃, uB₃}}
    {middle : SafetySpec.{u₂} q} {target : SafetySpec.{u₃} r}
    {matchLeftMiddle : StepRel left.toDynSystem middle.toDynSystem}
    {matchMiddleLeft : StepRel middle.toDynSystem left.toDynSystem}
    {matchMiddleTarget : StepRel middle.toDynSystem target.toDynSystem}
    {matchTargetMiddle : StepRel target.toDynSystem middle.toDynSystem}
    {matchLeftTarget : StepRel left.toDynSystem target.toDynSystem}
    {matchTargetLeft : StepRel target.toDynSystem left.toDynSystem}
    (first : MutualSafetyRefinement left middle matchLeftMiddle matchMiddleLeft)
    (second : MutualSafetyRefinement middle target matchMiddleTarget matchTargetMiddle)
    (hForth : ∀ stepLeft stepTarget,
      StepRel.comp matchLeftMiddle matchMiddleTarget stepLeft stepTarget →
        matchLeftTarget stepLeft stepTarget)
    (hBack : ∀ stepTarget stepLeft,
      StepRel.comp matchTargetMiddle matchMiddleLeft stepTarget stepLeft →
        matchTargetLeft stepTarget stepLeft) :
    MutualSafetyRefinement left target matchLeftTarget matchTargetLeft := by
  let composed : MutualSafetyRefinement left target
      (StepRel.comp matchLeftMiddle matchMiddleTarget)
      (StepRel.comp matchTargetMiddle matchMiddleLeft) :=
    { forth := second.forth.comp first.forth
      back := first.back.comp second.back }
  exact composed.weakenMatch hForth hBack

end MutualSafetyRefinement

/-! ## Step-synchronized simulations as forward simulations -/

/-- A synchronized same-interface simulation induces an operational forward
simulation at `StepRel.sync`. -/
def ForwardSimulation.ofIsSimulation
    {D₁ : DynSystem SImpl p} {D₂ : DynSystem SSpec p}
    {R : SImpl → SSpec → Prop}
    (hsim : IsSimulation D₁ D₂ R) :
    ForwardSimulation D₁ D₂ (StepRel.sync D₁ D₂) where
  stateRel := R
  step h d₁ :=
    ⟨hsim.expose_eq h ▸ d₁, ⟨hsim.expose_eq h, (eqRec_heq _ _).symm⟩,
      hsim.update_rel h d₁⟩

/-- Lift a synchronized simulation to a safety refinement by supplying the
three verification-policy preservation properties separately. -/
def SafetyRefinement.ofIsSimulation
    {S₁ : SafetySpec.{u₁} p} {S₂ : SafetySpec.{u₂} p}
    {R : S₁.State → S₂.State → Prop}
    (hsim : IsSimulation S₁.toDynSystem S₂.toDynSystem R)
    (hinit : ∀ st₁, S₁.init st₁ → ∃ st₂, S₂.init st₂ ∧ R st₁ st₂)
    (hassumptions : ∀ {st₁ st₂}, R st₁ st₂ →
      S₁.assumptions st₁ → S₂.assumptions st₂)
    (hsafe : ∀ {st₁ st₂}, R st₁ st₂ → S₂.safe st₂ → S₁.safe st₁) :
    SafetyRefinement S₁ S₂ (StepRel.sync S₁.toDynSystem S₂.toDynSystem) where
  toForwardSimulation := ForwardSimulation.ofIsSimulation hsim
  init := hinit
  assumptions := hassumptions
  safe := hsafe

end DynSystem

end PFunctor
