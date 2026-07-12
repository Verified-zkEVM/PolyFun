# Interaction Framework

General-purpose protocol interaction theory: sequential specs, two-party
roles, multiparty local views, and concurrent process semantics. PolyFun's
[`PolyFun/Interaction/`](../../PolyFun/Interaction/) is intentionally
*generic*. It carries no probability, no security predicates, and no
concrete cryptographic algebra. Cryptographic content of any kind belongs
in [`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io)
downstream.

This page is descriptive. The Lean source under
[`PolyFun/Interaction/`](../../PolyFun/Interaction/) is the canonical
reference. Cite Lean source by file path plus declaration when accuracy
matters.

## Design philosophy

The framework is organized around a few stable principles:

- **Continuation-first semantics.** `Spec` is a `PUnit`-leaved free tree on
  `Spec.basePFunctor` (`PFunctor.FreeM Spec.basePFunctor PUnit`): each
  round's continuation type depends on the move chosen. All composition,
  decoration, and strategy types respect this structure. See
  [`pfunctor.md`](pfunctor.md) for the substrate.
- **Control vs observation are orthogonal.** Who *chooses* a move (per-node:
  `NodeAuthority`; per-spec-tree: `Concurrent.Control`) and who *sees* a
  move (per-node: `NodeView`; per-party-per-node: `Multiparty.ViewMode`;
  per-spec-tree: `Concurrent.Profile`) are independent axes. A party can
  control a node but see only a quotient of its own move, or observe a node
  fully without controlling it.
- **Boundary vs composition.** *Boundaries* adapt the interface of a fixed
  protocol (same transcript shape, same round structure). *Composition*
  (`append`, `replicate`, `stateChain`) extends the protocol with new
  rounds. Never conflate the two.
- **Concurrency is layered.** The kernel is `par` + `Front` (frontier) +
  `residual` (one-step reduction). Interleaving is the basic semantics;
  independence and true concurrency are refinements on top. Dynamic
  `Process` wraps sequential `Spec` episodes into a coinductive stream.
- **UC as a frontend, not the foundation.** The open-systems layer
  (`Interface`, `PortBoundary`, `OpenTheory`) provides compositional
  operations (`map`, `par`, `wire`, `plug`). Computational equivalence,
  asymptotic security, and other security-flavored UC layers are *not*
  part of PolyFun: those live in
  [`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io).

## Quick orientation

| Layer | Directory | What it models |
|-------|-----------|----------------|
| Sequential core | `Basic/` | Specs, transcripts, decorations, strategies, composition |
| Two-party | `TwoParty/` | Sender/receiver roles, counterparts, public-coin replay |
| Multiparty | `Multiparty/` | Per-party local view modes (pick / observe / hidden / react) and observation kernels |
| Concurrent | `Concurrent/` | Parallel composition, frontiers, processes, refinement |
| UC frontend | `UC/` | Open-system interfaces, port boundaries, structural composition algebra (`map` / `par` / `wire` / `plug`), corruption surfaces |

Dependencies flow downward: `Concurrent/` may import `Multiparty/` and
`Basic/`; `TwoParty/` and `Multiparty/` import only `Basic/`; `UC/` is
above all of them.

## Core concepts: Spec, Node, Party, Profile

Before reading any one file, it helps to fix four words. They are the
load-bearing vocabulary of the entire `Interaction/` layer.

### Node, a structural location in the protocol tree

A `Spec` is an interaction tree
([`PolyFun/Interaction/Basic/Spec.lean`](../../PolyFun/Interaction/Basic/Spec.lean)).
A **node** is one branching point of that tree: a pair
`(Moves : Type, rest : Moves → Spec)`. It is *not* an actor; it is a
location where some next move gets chosen. At the level of `Spec` alone, a
node knows its move space and its continuation family, and nothing else:
not who chooses, not who watches, not what monad runs, not what data is
attached. Those concerns are deferred to companion layers (`Decoration`,
`NodeProfile`, `StepOver`, `SyntaxOver`, `InteractionOver`).

The namespace `Spec.Node.*` (`Context`, `Schema`, `ContextHom` in
[`PolyFun/Interaction/Basic/Node.lean`](../../PolyFun/Interaction/Basic/Node.lean))
is *generic node-context infrastructure*: for any type family
`Γ : Type → Type`, a `Γ`-decoration attaches one `Γ X` value at every node
with move space `X`.

### Party, an actor that plays across many nodes

A `Party` is a free type parameter introduced by the *content* layers
(`Multiparty/`, `Concurrent/`, `UC/`). A party is an actor that may control
or observe moves at *various* nodes throughout the same protocol tree. A
party is whole-tree (it has a strategy across the entire `Spec`); a node
is local (it lives at one location in the tree). Typically there are *many
more* nodes than parties: a long protocol may have unboundedly many nodes
(or a continuation-based infinite stream of them via `ProcessOver`), but
always the same finite party set.

### ViewMode, what a single party sees at a single node

`Multiparty.ViewMode X`
([`PolyFun/Interaction/Multiparty/Core.lean`](../../PolyFun/Interaction/Multiparty/Core.lean))
records how *one* party locally experiences a node whose move space is
`X`. The four constructors `pick` / `observe` / `hidden` / `react ⟨Obs, toObs⟩`
are the canonical observation modes. A `ViewMode` is the smallest atomic
node × party × observation triple in the framework.

The information content of a `ViewMode` is captured by
`Multiparty.Observation X`
([`PolyFun/Interaction/Multiparty/Observation.lean`](../../PolyFun/Interaction/Multiparty/Observation.lean)),
a `Σ Obs : Type, X → Obs` realized as
`PFunctor.Idx (Observation.basePFunctor X)`. `Observation X` carries
Mathlib's order typeclasses (`⊤`, `⊥`, `≤`, `⊔`) so refinement and join
in the information lattice use standard notation.

### NodeProfile, per-node attribution of who-authors-what and who-sees-what

`NodeProfile Party X`
([`PolyFun/Interaction/Concurrent/Process.lean`](../../PolyFun/Interaction/Concurrent/Process.lean))
is the bridge between a single node and the whole party set. It bundles
two orthogonal factor structures:

- `NodeAuthority Party X`: `controllers : X → List Party`. For each
  possible move, which parties are credited as having authored it
  (move-dependent and possibly multi-controller).
- `NodeView Party X`: `views : Party → Multiparty.ViewMode X`. For each
  party, what local view they have at this node.

The structure `extends` both factors, so dot-notation field access
(`node.controllers x`, `node.views me`) and the structure-literal
constructor `{ controllers := ..., views := ... }` work transparently.
Code that depends only on authorship can take a `NodeAuthority Party X`
parameter; code that depends only on observation can take a
`NodeView Party X` parameter.

The naming `NodeView` (rather than `NodeObservation`) deliberately avoids
collision with `Multiparty.Observation X`, the kernel-level *information
content* of a single party's view.

`OpenNodeProfile Party Δ X`
([`PolyFun/Interaction/UC/OpenProcess.lean`](../../PolyFun/Interaction/UC/OpenProcess.lean))
is the open-system extension that adds one `BoundaryAction Δ X` field for
external traffic. `OpenNodeContext.boundaryTrace` extracts the finite
outbound-packet trace emitted along a completed decorated step transcript;
routing and probabilistic execution remain downstream runtime concerns.

### Mental picture

The protocol tree is the stage; **nodes** are scenes on the stage;
**parties** are actors who appear in many scenes; a **`NodeProfile`** is
one scene's cast list and sightlines. `ViewMode` is a single actor's
vantage on a single scene.

| Concept | Scope | Role |
|---|---|---|
| `Spec` | whole protocol tree | branching shape of all possible plays |
| Node | one location in the tree | one scene: move space + continuation |
| Party | spans the whole tree | actor; may control or observe at various nodes |
| `Multiparty.ViewMode X` | one node × one party | that party's vantage on that one scene |
| `Multiparty.Observation X` | one node × one party | information content (kernel) of that vantage |
| `NodeProfile Party X` | one node × all parties | full cast list + sightlines for that scene |

## Core types

### `Spec` and `Transcript` (`Basic/Spec.lean`)

`Spec` is `PFunctor.FreeM Spec.basePFunctor PUnit` exposed via
`@[match_pattern, reducible]` wrappers `Spec.done` and `Spec.node`:
`done` (no more moves) or `node Moves rest` (one round of type `Moves`,
with dependent continuation `rest : Moves → Spec`). `Transcript spec` is
one full play through a `Spec`.

### `Decoration` (`Basic/Decoration.lean`)

`Decoration Γ spec` attaches node-local metadata from a `Node.Context Γ`
to every node of a `Spec`. `Decoration.Over` adds a dependent second
layer. Used for role labels, monad annotations, party assignments, etc.
The substrate is `PFunctor.FreeM.Displayed` /
`PFunctor.FreeM.Decoration`. See [`pfunctor.md`](pfunctor.md).

### `Strategy` (`Basic/Strategy.lean`)

`Strategy m spec Output` is a one-player strategy with monadic effects in
`m`. `Strategy.run` executes it against a counterpart to produce a
`Transcript`. `Strategy.mapOutput` is functorial over the output family.

## Sequential composition

Three ways to compose specs sequentially, each suited to a different
pattern:

| Combinator | When to use |
|------------|-------------|
| `Spec.append s₁ s₂` | Two-phase protocol where phase 2 depends on phase 1's transcript |
| `Spec.replicate spec n` | Fixed `n`-fold repetition of an identical spec |
| `Spec.stateChain Stage step n` | `n` stages with explicit state threading |
| `Spec.Chain n` | Continuation-style telescope (no external state type needed) |

`Transcript.liftAppend` lifts a type family on the first transcript to
the combined transcript, avoiding `cast` / `Eq.rec` pollution.
`Strategy.comp` composes strategies along `append`.

## Two-party protocols (`TwoParty/`)

Label each node with `Role` (`.sender` or `.receiver`) via
`RoleDecoration`. Then:

- **`Strategy.withRoles m spec roles Output`**: the focal party's strategy,
  seeing sender nodes as "produce a move" and receiver nodes as "observe a
  move".
- **`Counterpart m spec roles Output`**: the environment (verifier if
  focal is prover).
- **`Strategy.runWithRoles`**: executes focal + counterpart to get a
  transcript.

For public-coin protocols, `PublicCoinCounterpart` and `replay` support
public-coin transcript replay (Fiat-Shamir-style).

### Composition

`Strategy.compWithRoles` and `Counterpart.append` compose along
`Spec.append`. The flat variants (`compWithRolesFlat`,
`Counterpart.appendFlat`) take a single output family on the combined
transcript. Factorization theorems (e.g.
`runWithRoles_compWithRoles_append`) show that executing a composed
protocol equals sequential execution of its parts. These require
`LawfulCommMonad` (independent effects may be swapped).

## Multiparty local views (`Multiparty/`)

`ViewMode X` characterizes what a participant sees at a node with move
type `X`:

| Constructor | Meaning |
|-------------|---------|
| `.pick` | Participant locally selects the move (effectful Σ-of-X) |
| `.observe` | Participant sees the full move (function-from-X) |
| `.hidden` | Participant sees nothing |
| `.react ⟨Obs, toObs⟩` | Participant sees `toObs x : Obs` (partial information) |

Three packaged resolver patterns:

- **`Broadcast.Strategy`**: one acting party per node, all others observe.
- **`Directed.Strategy`**: sender / receiver pair per node.
- **`Profile.Strategy`**: full per-party `ViewProfile` decoration.

### Information kernel vs operational shape

`ViewMode` carries information along **two orthogonal axes**:

- **Information**: what observation does the participant make? Fully
  captured by a single projection `toObs : X → Obs` packaged with its
  codomain `Obs`. This polynomial-element form is
  `Multiparty.Observation X`, defined as
  `PFunctor.Idx (Observation.basePFunctor X)` where
  `Observation.basePFunctor X := ⟨Type, (X → ·)⟩`. Concretely it
  unfolds to `Σ Obs : Type, X → Obs`. Every `ViewMode X` collapses to
  an `Observation X` via `ViewMode.toObservation`.
- **Operational**: what continuation-passing shape does the participant
  use for `Action`? `.pick` (effectful Σ-of-X), `.observe`
  (function-from-X), `.hidden` (function-into-Cont, prepared in
  advance), `.react` (function on the observation, prepared in advance).

The four-constructor `ViewMode` is the *ergonomically convenient* form;
it specializes `Action` to a definitionally simpler shape per pattern,
which keeps protocol examples short. `Observation` is the *semantically
universal* form; protocols whose participants make arbitrary observations
not captured by `.pick` / `.observe` / `.hidden` should build observations
directly. The two are related by `ViewMode.toObservation` (collapse) and
`Observation.toViewMode` (lift into the universal `.react` constructor);
on the operational side,
`ViewMode.Action (.react ⟨..⟩) = Observation.Action ⟨..⟩` definitionally.

The information lattice on `Observation X` is exposed via Mathlib's order
typeclasses, so `⊤`, `⊥`, `≤`, `⊔` work directly:

- `⊤ : Observation X` is `Observation.top X = ⟨X, id⟩`. Full information.
  This is exactly the kernel of `ViewMode.observe`.
- `⊥ : Observation X` is `Observation.bot X = ⟨PUnit, fun _ => .unit⟩`.
  No information. This is exactly the kernel of `ViewMode.hidden`.
- `k₁ ≤ k₂` denotes `Observation.Refines k₁ k₂`. `k₁` is no more
  revealing than `k₂`.
- `k₁ ⊔ k₂` denotes `Observation.combine k₁ k₂`. The join (Σ-product) of
  two observations.

`Refines` is only a *preorder* (mutual refinement permits codomain
bijections), so `Observation X` carries `Preorder`, `OrderTop`,
`OrderBot`, and `Max` instances but not `PartialOrder` / `SemilatticeSup`.
Profile-level order theory comes through Mathlib's `Pi` instances on
`ObservationProfile Party X = Party → Observation X` for free.

The operational distinction `.pick` vs `.observe` is **not** the
canonical authorship attribution. Authorship-of-move is recorded by
`Concurrent.NodeAuthority.controllers : X → List Party` (move-dependent,
possibly multi-controller). `ViewMode.pick` indicates only that the
participant chooses *locally* in its endpoint; the protocol-level
controllers of a given move are recorded separately.

### Literature

Three independent traditions converge on the kernel form
`Σ Obs, X → Obs`:

- *Epistemic logic* (Halpern-Vardi *Reasoning About Knowledge*): agent
  observation as a projection from global state to local
  indistinguishability classes.
- *Noninterference / information-flow* (Goguen-Meseguer; Sabelfeld-Myers
  *Language-Based Information-Flow Security*): per-security-level
  projection of observable outputs.
- *Session types and endpoint projection* (Honda-Yoshida-Carbone
  *Multiparty Asynchronous Session Types*; Cruz-Filipe-Montesi *A Core
  Model for Choreographic Programming*): projection of a global type /
  global play to a single role's local view.

Closest type-theoretic ancestor: Hancock-Setzer *Interactive Programs in
Dependent Type Theory*. Command/Response interfaces with embedded
observation modes mirror the four-constructor operational shape.

## Concurrent processes (`Concurrent/`)

### Structural layer

`Concurrent.Spec` extends `Spec` with `par left right`. `Front S` is the
type of currently enabled frontier events. `residual event` gives the
spec after one event fires. The `diamond` theorem proves independent
events commute. `Trace.Equiv` identifies different linearizations of
independent events.

### Dynamic processes

`Process Party` is a coinductive-style stream: each step is a sequential
`Interaction.Spec` episode, producing a residual process. `Process.Run`
and `Process.Prefix` model infinite and finite executions. `Machine`
provides a state-indexed transition-system frontend that compiles to
`Process` via `Machine.toProcess`.

### Coalgebraic structure

Both `ProcessOver` and `Machine` are dynamical systems, i.e. bundled
coalgebras of polynomial functors
([`PolyFun/PFunctor/Dynamical/Basic.lean`](../../PolyFun/PFunctor/Dynamical/Basic.lean)):

- `ProcessOver Γ` *is* `PFunctor.DynSystem (StepOver.toPFunctor Γ)` — a
  state space together with a coalgebra of the step polynomial whose
  positions are `Γ`-decorated specs and whose directions are complete
  transcripts. `ProcessOver.step` / `ProcessOver.ofStep` are the
  `StepOver`-shaped views of the coalgebra structure map.
- `Machine` *is* `PFunctor.DynSystem PFunctor.univ` — the exposed
  position at each state is the type of currently enabled events.
  `Machine.Enabled` / `Machine.step` / `Machine.mk'` keep the classical
  vocabulary.
- `StepOver Γ` remains a `Functor` (post-compose on `next`) and
  `LawfulFunctor`; `StepOver.equivObj` identifies it with the extension
  of `StepOver.toPFunctor Γ`.
- The generic instance `Coalg p.Obj s.State` (from `DynSystem.out`, in
  [`PolyFun/Control/Coalgebra.lean`](../../PolyFun/Control/Coalgebra.lean))
  therefore covers both; a `Coalg F S` is a type `S` together with
  `out : S → F S`, the categorical dual of `MonadAlgebra`.

Consequently the whole dynamical-system toolkit applies to processes and
machines directly: terminal-coalgebra behavior and observational
equivalence (`DynSystem.behavior`, `DynSystem.ObsEq`), orbits
(`DynSystem.Run` / `DynSystem.Prefix`, of which `ProcessOver.Run` /
`ProcessOver.Prefix` are the transcript-vocabulary views), transition
metadata (`DynSystem.EventMap`, `DynSystem.Labeled`, `DynSystem.SafetySpec`,
`DynSystem.StepRel`), and the combinators (`ProcessOver.interleave` is the
`wrap` of `DynSystem.choiceProd` along the scheduler wiring lens,
`interleave_eq_wrap_choiceProd`).

This reflects the Poly / ACT perspective: a process is a coalgebra for a
polynomial endofunctor, with the step functor playing the role of the
"interface polynomial."

### Interleaving combinator

`ProcessOver.interleave` factors out the binary-choice interleaving
pattern shared by `par`, `wire`, and `plug` in `OpenProcessModel`. Given
two processes `p₁ : ProcessOver Γ₁`, `p₂ : ProcessOver Γ₂`, context
morphisms into a target context `Δ`, and a scheduler decoration, it
produces a `ProcessOver Δ` with product state space `p₁.Proc × p₂.Proc`.

### Control and observation

`Control Party S` assigns ownership of payload moves and scheduling
decisions. `Profile Party S` assigns `ViewMode`s to each party at
frontier nodes. `Current.view` combines both to give a party's
current-step interface.

### Fairness, safety, liveness

`Fairness.lean` defines weak and strong fairness over stable ticket
systems. `Liveness.lean` provides temporal predicates (`AlwaysState`,
`EventuallyState`, `InfinitelyOftenState`) and safety / admissibility
under fairness.

### Safety refinement and mutual refinement

`Refinement.lean` lifts implementation runs to specification runs,
preserving safety and event / ticket / controller traces; its
`SafetyRefinement` is the generic `PFunctor.DynSystem.SafetyRefinement`
at the step polynomial, with `mapRun` and the transport lemmas supplied by
`PolyFun/PFunctor/Dynamical/Refinement.lean`. `MutualSafetyRefinement.lean` and
`ReverseSafetyRefinement` (likewise the `DynSystem` notions) package the reverse
and two-way forms. These use independent relations in each direction and are
not coalgebraic bisimulations. Named two-way comparisons in `Equivalence.lean`
specialize to controller, trace, and observational matching.

### Open systems (UC frontend)

`Interface` (= `PFunctor`) and `PortBoundary` define typed I/O
boundaries. The choice of `PFunctor` for interfaces keeps the kernel
minimal while supporting `Packet`, `Query`, `Hom`, `comp` (Poly's
composition product), `compUnit` (composition unit), and boundary
equivalences.

`OpenTheory` provides the compositional algebra: `map`, `par`, `wire`,
`plug`. Lawfulness is stratified into a granular Mathlib-style class
hierarchy. Carriers:

- `HasUnit`: distinguished monoidal unit object for `par`.
- `HasIdWire`: distinguished identity-wire builder for `wire`.

Naturality:

- `IsLawfulMap` / `IsLawfulPar` / `IsLawfulWire` / `IsLawfulPlug`:
  functoriality of `map` and naturality of each combinator.
- `IsLawful`: bundles all naturality laws.

Coherence (each subsequent class adds laws on top of the previous):

- `IsMonoidal`: symmetric monoidal coherence for `par` (associativity,
  commutativity, left / right unit laws via the `HasUnit` object).
- `IsTraced`: Joyal-Street-Verity traced symmetric monoidal structure
  (`wire`-trace yanking, sliding, vanishing).
- `IsCompactClosed`: compact closed structure (a `(Poly, ⊗)`-friendly
  weakening; the strict snake equations are *not* asserted, since
  `(Poly, ⊗)` is monoidal closed but not strictly compact closed; see
  Spivak arXiv:2202.00534 §4.3).
- `HasPlugWireFactor`: closure-factorization identities relating `plug`
  to `wire` (`plug_eq_wire`, `plug_par_left`, `plug_wire_left`).

`OpenProcessIso` (in `OpenProcess.lean`) provides a bisimulation-based
equivalence for `OpenProcess`, used to state monoidal and compact-closed
laws for the concrete `openTheory` model up to isomorphism (see
`OpenProcessModel.lean`).

`OpenSyntax/` provides three layers for free open-system expressions:

- `Raw` is an inductive syntax tree whose constructors mirror the
  `OpenTheory` operations. It is pattern-matchable and suitable for
  inspection, transformation, and visualization.
- `Expr` is the quotient of `Raw` by the `OpenTheory` equations,
  yielding a lawful `OpenTheory` instance by construction.
- `Interp` is a tagless-final (Church-encoded) structure (final model)
  that stores a universal interpretation function and carries a lawful
  `OpenTheory` instance.

`Expr.toInterp` embeds quotiented expressions into the lawful `Interp`
model.

### Monad-parametric open processes and intrinsic samplers

`OpenProcess m Party Δ`
([`PolyFun/Interaction/UC/OpenProcess.lean`](../../PolyFun/Interaction/UC/OpenProcess.lean))
is the runtime-facing analogue of `Concurrent.ProcessOver`: an
`m`-parametric structure that bundles, at every step, a `Spec.Sampler m`
for resolving that step's nondeterminism. Samplers are carried as data,
not threaded through as an external argument. Three concrete
consequences:

1. **Samplers are a decoration, not a side argument.**
   `Spec.Sampler m spec` is definitionally
   `Decoration (fun X => m X) spec`
   ([`PolyFun/Interaction/Basic/Sampler.lean`](../../PolyFun/Interaction/Basic/Sampler.lean)).
   Every move type `X` in the spec receives an `m X` computation;
   `sampleTranscript` folds a sampler into an `m (Transcript spec)`.
   Universe-polymorphic at `(w, w')` so that `m : Type w → Type w'` and
   `spec : Spec.{w}`.
2. **`OpenProcess` carries `stepSampler` as a field.**
   For each reachable step, `OpenProcess.stepSampler` supplies the
   `Spec.Sampler m` that resolves that step's move choices. The
   underlying pure structure is still a `Concurrent.ProcessOver`,
   recoverable via `OpenProcess.toProcess`. The structural layer
   (`StepOver`, `ProcessOver`) is left untouched.
3. **`openTheory m Party schedulerSampler` threads samplers
   compositionally.**
   The monad `m` and a scheduler sampler (resolving binary-choice
   scheduler nodes introduced by `par` / `wire` / `plug`) become
   parameters of the concrete model. Each combinator builds the new
   step's sampler via `Spec.Sampler.interleave` from its inputs'
   samplers, so any law about `map` / `par` / `wire` / `plug` that holds
   in the pure structural theory lifts to the monad-parametric one once
   `schedulerSampler` is fixed.

`Spec.Fintype` in
[`PolyFun/Interaction/Basic/SpecFintype.lean`](../../PolyFun/Interaction/Basic/SpecFintype.lean)
is the per-spec ornament (recursive `Fintype` + `Nonempty` for every
move type) that lets users recover canonical uniform samplers
(`Sampler.uniformI`) without writing one by hand.

PolyFun deliberately stops here: anything that requires a probability
monad (e.g. `processSemanticsProbComp`), an oracle simulation
(`processSemanticsOracle`), or a UC security predicate
(`UCSecure`, `CompEmulates`) lives downstream in
[`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io). The
relevant runtime / async / security files live there, not here.

## Import guide

Choose the minimal set for your task:

```lean
-- Sequential protocol
import PolyFun.Interaction.Basic.Spec
import PolyFun.Interaction.Basic.Strategy
import PolyFun.Interaction.Basic.Append      -- if composing

-- Two-party
import PolyFun.Interaction.TwoParty.Strategy -- includes Role, Decoration
import PolyFun.Interaction.TwoParty.Compose  -- if composing

-- Multiparty
import PolyFun.Interaction.Multiparty.Core
import PolyFun.Interaction.Multiparty.Broadcast  -- or Directed / Profile

-- Concurrent
import PolyFun.Interaction.Concurrent.Spec
import PolyFun.Interaction.Concurrent.Process

-- UC / open systems
import PolyFun.Interaction.UC.OpenTheory
import PolyFun.Interaction.UC.OpenProcess
import PolyFun.Interaction.UC.OpenProcessModel
```

## File index

### `Basic/`

| File | Purpose |
|------|---------|
| `Spec.lean` | `Spec`, `Transcript`, `ofList` |
| `Node.lean` | `Node.Context`, `Node.Schema`, `Prefix` |
| `Decoration.lean` | `Decoration`, `Decoration.Over`, `telescope`, `pack` / `unpack` |
| `Syntax.lean` | `SyntaxOver`, `SyntaxOver.Family` |
| `Shape.lean` | `ShapeOver` (functorial `SyntaxOver` with continuation map) |
| `Interaction.lean` | `InteractionOver`, `Interaction`, `run` |
| `Strategy.lean` | `Strategy`, `Strategy.run`, `mapOutput` |
| `Append.lean` | `Spec.append`, transcript ops, `Strategy.comp` / `compFlat` |
| `Replicate.lean` | `Spec.replicate`, `Strategy.iterate` |
| `StateChain.lean` | `Spec.stateChain`, `Strategy.stateChainComp` |
| `Chain.lean` | `Spec.Chain`, `Chain.toSpec`, `Chain.ofStateMachine` |
| `Telescope.lean` | telescope helpers shared across composition |
| `Ownership.lean` | `LocalView` / `LocalRunner` builders for `SyntaxOver` |
| `MonadDecoration.lean` | `MonadDecoration`, `Strategy.withMonads`, `runWithMonads` |
| `BundledMonad.lean` | `BundledMonad` (monad packaged for inductive data) |
| `Sampler.lean` | `Spec.Sampler m spec := Decoration (fun X => m X) spec`, `sampleTranscript`, `Sampler.interleave`, `Sampler.uniformI` |
| `SpecFintype.lean` | `Spec.Fintype` per-spec ornament; enables canonical `Sampler.uniformI` |

### `TwoParty/`

| File | Purpose |
|------|---------|
| `Role.lean` | `Role`, `swap`, `Action`, `Dual`, `interact` |
| `Decoration.lean` | `RoleDecoration`, `RoleContext`, `RoleSchema`, monad contexts |
| `Strategy.lean` | `withRoles`, `Counterpart`, `PublicCoinCounterpart`, `replay` |
| `Syntax.lean` | role-aware syntax helpers |
| `Compose.lean` | `compWithRoles`, `Counterpart.append`, factorization theorems |
| `Refine.lean` | `Role.Refine`, equivalence with `Decoration.Over` |
| `Swap.lean` | role swap involutivity and append compatibility |
| `Examples.lean` | definitional `rfl` checks on small specs |

### `Multiparty/`

| File | Purpose |
|------|---------|
| `Core.lean` | `ViewMode`, `ObsType`, `Action`, `ViewMode.toObservation` / `Observation.toViewMode` (kernel bridges), `Multiparty.Strategy` |
| `Observation.lean` | `Multiparty.Observation`, `top` / `bot` / `Refines` / `combine` / `postcomp` / `Action`, Mathlib order typeclasses |
| `ObservationProfile.lean` | `Multiparty.ObservationProfile Party X := Party → Observation X` (with pointwise `Pi` order instances), `toViewProfile` |
| `Broadcast.lean` | `PartyDecoration`, `Broadcast.Strategy` |
| `Directed.lean` | `EdgeDecoration`, `Directed.Strategy` |
| `Profile.lean` | `ViewProfile`, `Profile.Decoration`, `Profile.Strategy` |
| `Examples.lean` | broadcast, directed, profile, adversarial leakage examples |

### `Concurrent/`

| File | Purpose |
|------|---------|
| `Spec.lean` | `Concurrent.Spec` (`done` / `node` / `par`), `isLive` |
| `Frontier.lean` | `Front`, `residual`, liveness lemmas |
| `Trace.lean` | `Trace` (finite linearization), `length` |
| `Independence.lean` | `Independent`, `diamond` |
| `Interleaving.lean` | `Trace.Equiv`, `cast` |
| `Control.lean` | `Control`, `scheduler?`, `current?`, `controllers` |
| `Profile.lean` | `Profile`, `observe`, `residual`, `frontierView` |
| `Current.lean` | `view`, `observe`, `residualView` |
| `Process.lean` | `NodeAuthority`, `NodeView`, `NodeProfile`, `StepOver`, `ProcessOver` (= `DynSystem` of the step polynomial; views `step` / `ofStep`), `Process`, `Functor (StepOver Γ)`, `interleave` / `interleaveLens` / `interleave_eq_wrap_choiceProd`, `Behavior`, metadata bundles as `DynSystem` instantiations |
| `Tree.lean` | structural concurrent syntax → `Process` |
| `Machine.lean` | `Machine` (= `DynSystem PFunctor.univ`), `Machine.{Enabled, step, mk', SafetySpec}`, `Machine.toProcess` |
| `Execution.lean` | `Trace`, `ObservedTrace` for processes |
| `Run.lean` | `Prefix`, `Run` (infinite), controller / event extraction |
| `Policy.lean` | `StepPolicy`, `respects`, combinators |
| `Observation.lean` | `PackedObs`, transcript relations, observation preservation |
| `Refinement.lean` | `SafetyRefinement` (= `DynSystem.SafetyRefinement` at the step polynomial), `matchTranscript`, observation preservation, `safe_of_satisfies` |
| `MutualSafetyRefinement.lean` | `MutualSafetyRefinement`, `ReverseSafetyRefinement` (= the `DynSystem` notions), `Satisfies`-based safety transport |
| `Equivalence.lean` | controller, trace, observational equivalences |
| `Fairness.lean` | `WeakFair`, `StrongFair`, temporal predicates |
| `Liveness.lean` | `Safe`, `Satisfies`, `Admissible`, state predicates |
| `Examples.lean` | worked examples: profiles, control, execution, policies |

### `UC/`

| File | Purpose |
|------|---------|
| `Interface.lean` | `Interface`, `PortBoundary`, `Hom`, `Equiv`, `comp` / `compUnit`, tensor / swap |
| `OpenTheory.lean` | `OpenTheory` algebra, `IsLawful`, `HasUnit`, `HasIdWire`, `IsMonoidal`, `IsTraced`, `IsCompactClosed`, `HasPlugWireFactor` |
| `OpenSyntax/Raw.lean` | `Raw` syntax tree, `Raw.interpret`, `Raw.Equiv` (incl. monoidal / traced / CC equations) |
| `OpenSyntax/Interp.lean` | `Interp` (tagless-final), granular `HasUnit` / `HasIdWire` / `IsMonoidal` / `IsTraced` / `IsCompactClosed` / `HasPlugWireFactor` instances |
| `OpenSyntax/Expr.lean` | `Expr` (quotient of `Raw`), granular `OpenTheory` lawfulness instances, `Expr.toInterp` |
| `OpenProcess.lean` | `BoundaryAction`, `OpenNodeProfile`, `OpenNodeContext` (with polynomial-product bridge `productView` and structural `boundaryTrace`), `OpenProcess m Party Δ` (monad-parametric, with intrinsic `stepSampler`), `toProcess`, `OpenProcessIso` |
| `OpenProcessModel.lean` | `openTheory m Party schedulerSampler` (concrete model threading `Spec.Sampler` through `map` / `par` / `wire` / `plug`), `IsLawful`, monoidal / CC laws up to `OpenProcessIso` |
| `Emulates.lean` | `Observation`, `Emulates`, `UCSecure`. Contextual emulation and UC security stated abstractly over an `Observation` (an equivalence relation on closed systems), with no probability monad and no concrete security predicate. |
| `Notation.lean` | UC notation helpers (`∥`, `⊞`, `⊠`, `⊗ᵇ`, `ᵛ`); see [`notation.md`](notation.md) |
| `MachineId.lean` | machine identifiers |
| `EnvAction.lean` | environment actions, parametric over an arbitrary monad `m` (no probability dependency) |
| `EnvOpenProcess.lean` | open-process wrappers around `EnvAction`, also monad-parametric |
| `CorruptionModel.lean` | corruption-model surface, parametric over `m` |
| `MomentaryCorruption.lean` | momentary corruption surface, parametric over `m` |
| `Leakage.lean` | leakage-oriented UC observation helpers |

UC files that depended on a probability monad in VCV-io (`Computational.lean`,
`Runtime.lean`, `AsyncRuntime.lean`, `AsyncSecurity.lean`, `Standard.lean`,
`StdDoBridge.lean`) deliberately do **not** appear in PolyFun. They live in
[`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io) and
re-import the generic primitives from PolyFun.

## In-tree examples

- [`PolyFunTest/Interaction/TwoParty/Examples.lean`](../../PolyFunTest/Interaction/TwoParty/Examples.lean):
  `rfl` checks that `withRoles` / `Counterpart` types unfold correctly on
  a two-step spec.
- [`PolyFunTest/Interaction/Multiparty/Examples.lean`](../../PolyFunTest/Interaction/Multiparty/Examples.lean):
  pattern-matching resolvers for broadcast, directed, and profile-based
  models; adversarial leakage and adaptive corruption.
- [`PolyFunTest/Interaction/Concurrent/Examples.lean`](../../PolyFunTest/Interaction/Concurrent/Examples.lean):
  small concurrent specs with profiles, control, process execution,
  policies, and interleaving.

End-to-end UC examples that involve probability monads or concrete
cryptographic content (one-time pad, oracle protocols, etc.) live in
VCV-io rather than PolyFun, by design.
