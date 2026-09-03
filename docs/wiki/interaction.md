# Interaction Framework

For the UC paper-to-code ledger, observation boundary, and precise
PolyFun/VCVio ownership split, see [`uc.md`](uc.md).

General-purpose protocol interaction theory: sequential type trees, two-party
roles, multiparty local views, and concurrent process semantics. PolyFun's
[`PolyFun/Interaction/`](../../PolyFun/Interaction/) is intentionally
*generic*. It carries no probability, no security predicates, and no
concrete cryptographic algebra. Cryptographic content of any kind belongs
in [`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio)
downstream.

This page is descriptive. The Lean source under
[`PolyFun/Interaction/`](../../PolyFun/Interaction/) is the canonical
reference. Cite Lean source by file path plus declaration when accuracy
matters.

## Design philosophy

The framework is organized around a few stable principles:

- **Continuation-first semantics.** `TypeTree` is a `PUnit`-leaved free tree on
  `TypeTree.basePFunctor` (`PFunctor.FreeM TypeTree.basePFunctor PUnit`): each
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
  protocol (same path shape, same round structure). *Composition*
  (`append`, `replicate`, `stateChain`, `Chain.then`) extends the protocol
  with new rounds. Never conflate the two.
- **Concurrency is layered.** The kernel is `par` + `Front` (frontier) +
  `residual` (one-step reduction). Interleaving is the basic semantics;
  independence and true concurrency are refinements on top. Dynamic
  `Process` wraps sequential `TypeTree` episodes into a coinductive stream.
- **UC as a frontend, not the foundation.** The open-systems layer
  (`Interface`, `PortBoundary`, `OpenTheory`) provides compositional
  operations (`map`, `par`, `wire`, `plug`). Computational equivalence,
  asymptotic security, and other security-flavored UC layers are *not*
  part of PolyFun: those live in
  [`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio).

## Quick orientation

| Layer | Directory | What it models |
|-------|-----------|----------------|
| Sequential core | `Basic/` | Type trees, paths, decorations, strategies, composition |
| Two-party | `TwoParty/` | Sender/receiver roles, counterparts, public-coin replay |
| Multiparty | `Multiparty/` | Per-party local view modes (pick / observe / hidden / react) and observation kernels |
| Concurrent | `Concurrent/` | Parallel composition, frontiers, processes, refinement |
| UC frontend | `UC/` | Open-system interfaces, port boundaries, structural composition algebra (`map` / `par` / `wire` / `plug`), corruption surfaces |

Dependencies flow downward: `Concurrent/` may import `Multiparty/` and
`Basic/`; `TwoParty/` and `Multiparty/` import only `Basic/`; `UC/` is
above all of them.

The source modules make this boundary machine-checkable. Public declarations
are grouped in `public section`; dependencies appearing in their signatures
use `public import`, while implementation-only dependencies remain private.
Definitions are `@[expose]` only when downstream computation or definitional
equality is an intentional part of the API. Proof modules use `import all`
when they need opaque bodies without widening the exported reducer surface.

## Core concepts: TypeTree, Node, Party, Profile

Before reading any one file, it helps to fix four words. They are the
load-bearing vocabulary of the entire `Interaction/` layer.

### Node, a structural location in the protocol tree

A `TypeTree` is an interaction tree
([`PolyFun/Interaction/Basic/TypeTree.lean`](../../PolyFun/Interaction/Basic/TypeTree.lean)).
A **node** is one branching point of that tree: a pair
`(Moves : Type, rest : Moves → TypeTree)`. It is *not* an actor; it is a
location where some next move gets chosen. At the level of `TypeTree` alone, a
node knows its move space and its continuation family, and nothing else:
not who chooses, not who watches, not what monad runs, not what data is
attached. Those concerns are deferred to companion layers (`Decoration`,
`NodeProfile`, `StepOver`, `SyntaxOver`, `InteractionOver`).

The namespace `TypeTree.Node.*` (`Context`, `Schema`, `ContextHom` in
[`PolyFun/Interaction/Basic/Node.lean`](../../PolyFun/Interaction/Basic/Node.lean))
is *generic node-context infrastructure*: for any type family
`Γ : Type → Type`, a `Γ`-decoration attaches one `Γ X` value at every node
with move space `X`.

### Party, an actor that plays across many nodes

A `Party` is a free type parameter introduced by the *content* layers
(`Multiparty/`, `Concurrent/`, `UC/`). A party is an actor that may control
or observe moves at *various* nodes throughout the same protocol tree. A
party is whole-tree (it has a strategy across the entire `TypeTree`); a node
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
outbound-packet trace emitted along a completed decorated step path;
routing and probabilistic execution remain downstream runtime concerns.

### Mental picture

The protocol tree is the stage; **nodes** are scenes on the stage;
**parties** are actors who appear in many scenes; a **`NodeProfile`** is
one scene's cast list and sightlines. `ViewMode` is a single actor's
vantage on a single scene.

| Concept | Scope | Role |
|---|---|---|
| `TypeTree` | whole protocol tree | branching shape of all possible plays |
| Node | one location in the tree | one scene: move space + continuation |
| Party | spans the whole tree | actor; may control or observe at various nodes |
| `Multiparty.ViewMode X` | one node × one party | that party's vantage on that one scene |
| `Multiparty.Observation X` | one node × one party | information content (kernel) of that vantage |
| `NodeProfile Party X` | one node × all parties | full cast list + sightlines for that scene |

## Core types

### `TypeTree` and `Path` (`Basic/TypeTree.lean`)

`TypeTree` is `PFunctor.FreeM TypeTree.basePFunctor PUnit` exposed via
`@[match_pattern, reducible]` wrappers `TypeTree.done` and `TypeTree.node`:
`done` (no more moves) or `node Moves rest` (one round of type `Moves`,
with dependent continuation `rest : Moves → TypeTree`). `Path spec` is
one full play through a `TypeTree`.

### `Decoration` (`Basic/Decoration.lean`)

`Decoration Γ spec` attaches node-local metadata from a `Node.Context Γ`
to every node of a `TypeTree`. `Decoration.Over` adds a dependent second
layer. Used for role labels, monad annotations, party assignments, etc.
The substrate is `PFunctor.FreeM.Displayed` /
`PFunctor.FreeM.Decoration`. See [`pfunctor.md`](pfunctor.md).

### `Strategy` (`Basic/Strategy.lean`)

`Strategy m spec Output` is a one-player strategy with monadic effects in
`m`. `Strategy.run` executes it against a counterpart to produce a
`Path`. `Strategy.mapOutput` is functorial over the output family.

## Sequential composition

Three ways to compose type trees sequentially, each suited to a different
pattern:

| Combinator | When to use |
|------------|-------------|
| `TypeTree.append s₁ s₂` | Two-phase protocol where phase 2 depends on phase 1's path |
| `TypeTree.replicate tree n` | Fixed `n`-fold repetition of an identical type tree |
| `TypeTree.stateChain Stage step n` | Clocked finite unfold with explicit stage-indexed state |
| `TypeTree.Chain n` | Sigma-friendly presentation of `(TypeTree.stepPoly.Obj)^[n] PUnit` |
| `TypeTree.Chain.then c k` | Path-dependent concatenation preserving explicit round counts |
| `TypeTree.Telescope round step s` | Well-founded, possibly unbounded stopping tree from state `s` |

These constructions share one polynomial substrate. `TypeTree.stepPoly` is
definitionally `PFunctor.FreeP TypeTree.basePFunctor`, and `TypeTree.append` is the
forward map of its substitution-monoid multiplication (the backward map is
path splitting). `Chain.ofStateChain` unfolds a stage-indexed coalgebra
into `Chain`; `Chain.toTypeTree_ofStateChain` shows that flattening it recovers
`TypeTree.stateChain`.

`TypeTree.Telescope` serves a different role: it is the indexed W-type generated
by `done` and `extend`, with a formal initial-algebra fold. It is not by itself
a termination certificate, because `done` is available at every state.

`Path.liftAppend` lifts a type family on the first path to
the combined path, avoiding `cast` / `Eq.rec` pollution.
`Strategy.comp` composes strategies along `append`.
At the explicit-round `Chain.then` boundary, `Chain.thenPathEquiv` and its
split/join operations recover the two path pieces, `Chain.liftThen` transports
dependent output families, and `Chain.strategyCompThen` composes strategies.
Units hold at both the round-indexed and flattened levels. Three-stage
associativity is stated after `Chain.toTypeTree`, the stable operational
interpretation; raw equality of intensional `Chain` presentations is not part
of the API contract.

## Two-party protocols (`TwoParty/`)

Label each node with `Role` (`.sender` or `.receiver`) via
`RoleDecoration`. Then:

- **`Strategy.withRoles m spec roles Output`**: the focal party's strategy,
  seeing sender nodes as "produce a move" and receiver nodes as "observe a
  move".
- **`Counterpart m spec roles Output`**: the environment (verifier if
  focal is prover).
- **`Strategy.runWithRoles`**: executes focal + counterpart to get a
  path.

For public-coin protocols, `PublicCoinCounterpart` and `replay` support
public-coin path replay (Fiat-Shamir-style).

### Composition

`Strategy.compWithRoles` and `Counterpart.append` compose along
`TypeTree.append`. The flat variants (`compWithRolesFlat`,
`Counterpart.appendFlat`) take a single output family on the combined
path. Factorization theorems (e.g.
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
The factorization predicate itself is exposed so an ordinary-import consumer
can prove `k₁ ≤ k₂` directly as `⟨factor, proof⟩`; the named `refines_iff`
remains available when an explicit rewrite boundary is preferable.
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

`Concurrent.Spec` extends `TypeTree` with `par left right`. `Front S` is the
type of currently enabled frontier events. `residual event` gives the
spec after one event fires. The `diamond` theorem proves independent
events commute. `Trace.Equiv` identifies different linearizations of
independent events.

### Dynamic processes

`Process P Party` is a coinductive-style stream on states `P`: each step is a sequential
`Interaction.TypeTree` episode, producing a residual process. `Process.Run`
and `Process.Prefix` model infinite and finite executions. `Machine`
provides a state-indexed transition-system frontend that compiles to
`Process` via `Machine.toProcess`.

### Coalgebraic structure

Both `ProcessOver` and `Machine` are dynamical systems, i.e.
coalgebras of polynomial functors
([`PolyFun/PFunctor/Dynamical/Basic.lean`](../../PolyFun/PFunctor/Dynamical/Basic.lean)):

- `ProcessOver P Γ` *is* `PFunctor.DynSystem P (StepOver.toPFunctor Γ)`
  — a coalgebra on the state space `P` of the step polynomial whose
  positions are `Γ`-decorated type trees and whose directions are complete
  paths. `ProcessOver.step` / `ProcessOver.ofStep` are the
  `StepOver`-shaped views of the coalgebra structure map.
- `Machine S` *is* `PFunctor.DynSystem S PFunctor.univ` — the exposed
  position at each state is the type of currently enabled events.
  `Machine.Enabled` / `Machine.step` / `Machine.mk'` keep the classical
  vocabulary.
- `StepOver Γ` remains a `Functor` (post-compose on `next`) and
  `LawfulFunctor`; `StepOver.equivObj` identifies it with the extension
  of `StepOver.toPFunctor Γ`.
- The coalgebra packaging `DynSystem.coalg : Coalg p.Obj S` (built from
  `DynSystem.out`, against
  [`PolyFun/Control/Coalgebra.lean`](../../PolyFun/Control/Coalgebra.lean))
  therefore covers both; a `Coalg F S` is a type `S` together with
  `out : S → F S`, the categorical dual of `MonadAlgebra`.

Consequently the whole dynamical-system toolkit applies to processes and
machines directly: terminal-coalgebra behavior and observational
equivalence (`DynSystem.behavior`, `DynSystem.ObsEq`), orbits
(`DynSystem.Run` / `DynSystem.Prefix`, of which `ProcessOver.Run` /
`ProcessOver.Prefix` are the path-vocabulary views), transition
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
two processes `p₁ : ProcessOver P₁ Γ₁`, `p₂ : ProcessOver P₂ Γ₂`,
context morphisms into a target context `Δ`, and a scheduler decoration,
it produces a `ProcessOver (P₁ × P₂) Δ` on the product state space.

`ProcessOver.interleaveRouted` (`Concurrent/RoutedInterleave.lean`) keeps
that shape and adds a routing hook: once the scheduled side completes a step
path, a `Route` may update the other side's state from that path. With the
trivial routes it is `interleave` definitionally, and the `mapContext`
distribution laws hold verbatim because routes never see the decoration. The
open-process lift with samplers is `OpenProcess.interleaveRouted`
(`UC/OpenProcessInterleave.lean`); a communicating composition supplies routes
that deliver the packets emitted along the path, which the structural
`openTheory` composition erases.

### Control and observation

`Control Party S` assigns ownership of payload moves and scheduling
decisions. `Profile Party S` assigns `ViewMode`s to each party at
frontier nodes. `Current.view` combines both to give a party's
current-step interface.

### Fairness, safety, liveness

`Fairness.lean` defines weak and strong fairness over stable ticket
systems, including the generic implication from strong to weak fairness and
the temporal fact that eventual persistence implies infinite recurrence.
`Liveness.lean` provides temporal predicates (`AlwaysState`,
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
  Spivak, *A reference for categorical structures on Poly*,
  arXiv:2202.00534 §4.3).
- `HasPlugWireFactor`: closure-factorization identities relating `plug`
  to `wire` (`plug_eq_wire`, `plug_par_left`, `plug_wire_left`).

`OpenProcess.activationLTS` (in `OpenProcess.lean`) exposes only whether a
complete path is silent or activated. `OpenProcessActivationEquiv` is
the standard generic whole-system delay bisimulation of those labelled
transition systems and is used to state structural laws for the concrete
`openTheory` model (see `OpenProcessModel.lean`). The activation observation
does not retain packet/action identity or sampler effects, so it is not a
security observation.

`OpenProcessFactorization.lean` proves the four left/right `par` and `wire`
plug reassociations only at this structural layer. The reassociations change
the nesting and number of scheduler choices along a path. A sampler-aware or
probabilistic consumer must additionally transport those scheduler effects and
prove that its concrete observation is invariant under the transport; the
activation-equivalence theorems alone do not supply that semantic bridge.

Implementation follow-up: the four proofs repeat the same nested-interleave
decoration transport. The reusable abstraction belongs at the
`OpenProcess.interleave` owner layer as a reassociation/permutation theorem;
the factorization module records the finite scheduler truth tables until that
owner-level lemma is available.

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
`m`-parametric structure that bundles, at every step, a `TypeTree.Sampler m`
for resolving that step's nondeterminism. Samplers are carried as data,
not threaded through as an external argument. Three concrete
consequences:

1. **Samplers are a decoration, not a side argument.**
   `TypeTree.Sampler m spec` is definitionally
   `Decoration (fun X => m X) spec`
   ([`PolyFun/Interaction/Basic/Sampler.lean`](../../PolyFun/Interaction/Basic/Sampler.lean)).
   Every move type `X` in the tree receives an `m X` computation;
   `samplePath` folds a sampler into an `m (Path spec)`.
   Universe-polymorphic at `(w, w')` so that `m : Type w → Type w'` and
   `spec : TypeTree.{w}`.
2. **`OpenProcess` carries `stepSampler` as a field.**
   For each reachable step, `OpenProcess.stepSampler` supplies the
   `TypeTree.Sampler m` that resolves that step's move choices. The
   underlying pure structure is still a `Concurrent.ProcessOver`,
   recoverable via `OpenProcess.toProcess`. The structural layer
   (`StepOver`, `ProcessOver`) is left untouched.
3. **`openTheory m Party schedulerSampler` threads samplers
   compositionally.**
   The monad `m` and a scheduler sampler (resolving binary-choice
   scheduler nodes introduced by `par` / `wire` / `plug`) become
   parameters of the concrete model. Each combinator builds the new
   step's sampler via `TypeTree.Sampler.interleave` from its inputs'
   samplers. This construction is compositional, but a structural law does not
   automatically lift to sampler semantics: reassociation can change the order
   or number of scheduler samples even when `schedulerSampler` is fixed.

`TypeTree.Fintype` in
[`PolyFun/Interaction/Basic/TypeTreeFintype.lean`](../../PolyFun/Interaction/Basic/TypeTreeFintype.lean)
is the recursive finiteness ornament for every move type;
`TypeTree.Nonempty` independently records that every move type is nonempty.
Downstream uniform samplers require both properties. Keeping them separate
matches `PFunctor.Fintype` and does not treat finite branching as evidence that
a move is available.

PolyFun deliberately stops here: anything that requires a probability
monad (e.g. `processSemanticsProbComp`), an oracle simulation
(`processSemanticsOracle`), or a UC security predicate
(`UCSecure`, `CompEmulates`) lives downstream in
[`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio). The
relevant runtime / async / security files live there, not here.

## Import guide

Choose the minimal set for your task:

```lean
-- Sequential protocol
import PolyFun.Interaction.Basic.TypeTree
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
| `TypeTree.lean` | `TypeTree`, `Path`, canonical `stepPoly` / `substMonoid`, `ofList` |
| `Node.lean` | `Node.Context`, `Node.Schema`, `Prefix` |
| `Decoration.lean` | `Decoration`, `Decoration.Over`, `telescope`, `pack` / `unpack` |
| `Syntax.lean` | `SyntaxOver`, `SyntaxOver.Family` |
| `Shape.lean` | `ShapeOver` (functorial `SyntaxOver` with continuation map) |
| `Interaction.lean` | `InteractionOver`, `Interaction`, `run` |
| `Strategy.lean` | `Strategy`, `Strategy.run`, `mapOutput`, equality transport via `castSpec` |
| `Append.lean` | `TypeTree.append`, path ops, `Strategy.comp` / `compFlat` |
| `Replicate.lean` | `TypeTree.replicate`, `Strategy.iterate` |
| `StateChain.lean` | `TypeTree.stateChain`, `Strategy.stateChainComp` |
| `Chain.lean` | finite final-sequence `TypeTree.Chain`, `toTypeTree`, `ofStateChain`, `ofStateMachine` |
| `Chain/Append.lean` | dependent `Chain.then`, units, boundary path/output/strategy composition, and three-stage coherence |
| `Telescope.lean` | indexed stopping trees and their initial-algebra fold to `TypeTree` |
| `Ownership.lean` | `LocalView` / `LocalRunner` builders for `SyntaxOver` |
| `MonadDecoration.lean` | `MonadDecoration`, `Strategy.withMonads`, `runWithMonads` |
| `BundledMonad.lean` | `BundledMonad` (monad packaged for inductive data) |
| `Sampler.lean` | `TypeTree.Sampler m tree := Decoration (fun X => m X) tree`, `samplePath`, `Sampler.interleave` |
| `TypeTreeFintype.lean` | Universe-polymorphic `TypeTree.Fintype` and `TypeTree.Nonempty` branching ornaments |

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
| `Examples.lean` | definitional `rfl` checks on small type trees |

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
| `Process.lean` | `NodeAuthority`, `NodeView`, `NodeProfile`, `StepOver`, `ProcessOver` (= `DynSystem` of the step polynomial, state space as parameter; views `step` / `ofStep`), `Process`, `Functor (StepOver Γ)`, `interleave` / `interleaveLens` / `interleave_eq_wrap_choiceProd`, `Behavior`, metadata bundles as `DynSystem` instantiations |
| `RoutedInterleave.lean` | `ProcessOver.Route`, `interleaveRouted` (interleaving with routing hooks), `interleave_eq_interleaveRouted`, and the `mapContext` distribution laws for the routed form |
| `Tree.lean` | structural concurrent syntax → `Process` |
| `Machine.lean` | `Machine` (= `DynSystem` at `PFunctor.univ`, state space as parameter), `Machine.{Enabled, step, mk', SafetySpec}`, `Machine.toProcess` |
| `Execution.lean` | `Trace`, `ObservedTrace` for processes |
| `Run.lean` | `Prefix`, `Run` (infinite), controller / event extraction |
| `Policy.lean` | `StepPolicy`, `respects`, combinators |
| `Observation.lean` | `PackedObs`, path relations, observation preservation |
| `Refinement.lean` | `SafetyRefinement` (= `DynSystem.SafetyRefinement` at the step polynomial), `matchPath`, observation preservation, `safe_of_satisfies` |
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
| `OpenTheory/PlugFactorization.lean` | `parContextLeft` / `parContextRight` / `wireContextLeft` / `wireContextRight` (residual contexts, plain `map`/`wire` composites) and `HasPlugFactorization`: `plug_comm` plus the four `close_*` factorization equalities on top of `IsLawful`, strictly weaker than `HasPlugWireFactor` (every strict compact-closed theory is an instance). This is all the composition theorems consume, and the honest strict target for process models, which cannot reach unit or snake laws at strong sampler equivalence. |
| `OpenTheory/Congruence.lean` | `OpenTheory.Congruence` (a setoid on every boundary's objects preserved by `map`/`par`/`wire`/`plug`), its `rel`/`refl`/`symm`/`trans`/`rel_of_eq`, and the discrete congruence `Congruence.eq` |
| `OpenTheory/Quotient.lean` | `OpenTheory.quotient T E` (objects are classes, operations lifted along `Quotient.map'`/`map₂'`; `Congruence.cls` with its computation rules and `quotient_ind`), the laws-modulo-a-congruence classes `IsLawfulMod` / `IsMonoidalMod` / `IsTracedMod` / `IsCompactClosedMod` / `HasPlugWireFactorMod` / `HasPlugFactorizationMod`, the instances showing strict laws hold modulo any congruence, and the lifting instances making the quotient strictly lawful at each level |
| `OpenSyntax/Raw.lean` | `Raw` syntax tree, `Raw.interpret`, `Raw.Equiv` (incl. monoidal / traced / CC equations), the raw theory `Raw.theory` with `Raw.congruence` and its `HasPlugWireFactorMod` instance (every law is a constructor of `Raw.Equiv`) |
| `OpenSyntax/Interp.lean` | `Interp` (tagless-final), granular `HasUnit` / `HasIdWire` / `IsMonoidal` / `IsTraced` / `IsCompactClosed` / `HasPlugWireFactor` instances |
| `OpenSyntax/Expr.lean` | `Expr` (quotient of `Raw`), `Expr.theory` as `(Raw.theory Atom).quotient (Raw.congruence Atom)` with every lawfulness class by the generic lifting, the `theory_{map,par,wire,plug,unit,idWire}` computation lemmas, `Expr.toInterp` |
| `OpenProcess.lean` | `BoundaryAction`, `OpenNodeProfile`, `OpenNodeContext` (with polynomial-product bridge `productView` and structural `boundaryTrace`), `OpenProcess m Party Δ` (monad-parametric, with intrinsic `stepSampler`), `toProcess`, `OpenProcessActivationEquiv` |
| `OpenProcessInterleave.lean` | `OpenProcess.mapHom` (re-decoration along any node-context hom; `mapBoundary` is the boundary-morphism case), `OpenNodeContext.PreservesActivation` with instances for every injection of the theory, `OpenNodeContext.IsInternalNode` (silent and emitting nothing) and `OpenNodeContext.EmitsAlong` (the hom relabels traces by a partial index map) with `boundaryTrace_map_of_emitsAlong`, the routed interleaving `OpenProcess.interleaveRouted` with its samplers, the normalization equalities `mapBoundary_interleave` / `interleave_mapHom_{left,right}` pushing re-decoration into the injections, and the public extensionality helpers |
| `OpenProcessCoherence.lean` | `isSilentStep_interleave_{left,right}_iff`, the silence and boundary-trace unfoldings of each branch of a composite step, the generic shapes `interleave_assoc_activationEquiv` / `interleave_comm_activationEquiv` / `interleave_rehome_activationEquiv` / `interleave_unit_{left,right}_activationEquiv` for arbitrary activation-preserving injections and silent scheduler nodes, and the congruences `interleave_congr_{left,right}` / `mapHom_congr` (activation equivalence is preserved by interleaving and re-decoration). Structural coherence only; nothing here sees packets or samplers. |
| `OpenProcessModel.lean` | `openTheory m Party schedulerSampler` (concrete model threading `TypeTree.Sampler` through `map` / `par` / `wire` / `plug`), `IsLawful` with `HasUnit` / `HasIdWire` (`openTheoryUnit`, `openTheoryIdWire`), and every monoidal, traced, and compact-closed law up to `OpenProcessActivationEquiv` (`openTheory_{par_assoc,par_comm,plug_comm,wire_assoc,wire_par_superpose,wire_comm,par_left_unit,par_right_unit,wire_id_wire,wire_id_wire_right,plug_eq_wire,unit_eq}_activation_equiv`), each one instance of the `OpenProcessCoherence` shapes after normalization |
| `Scheduler.lean` | Positive-natural (`PNat`) frontier masses, mass-aware `BinaryScheduler`, hierarchical source/left/right draws, and `BinaryScheduler.IsFlat` / `IsCoherent`. `IsFlat` requires every binary encoding of a three-component choice to agree with one direct flat choice relative to a downstream `MonadRelFamily`. |
| `ScheduledOpenProcessModel.lean` | `ScheduledOpenProcess` and `scheduledOpenTheory`, the additive migration model that preserves positive frontier mass through `map` and adds it through `par` / `wire` / `plug`; each binary scheduler node receives the two subtree masses. The theory is `IsLawful`: each naturality law is the `openTheory` law at the draw for the component masses. |
| `ScheduledSamplerFactorization.lean` | `BinaryScheduler.{source,left,right}Draw` as the nested draws at the scheduler calls of a composition, `IsCoherent` restated in the form the shapes consume (`flip_rel`, `nestedDrawLeft_rel_factor{Left,Right}`), the public bind equations, `samplePath_interleave_assoc_{left,right}`, the five plug laws `scheduledOpenTheory_plug_{comm,par_left,par_right,wire_left,wire_right}_sampler_equiv` of the mass-aware theory with scheduler coherence as the whole obligation, and `Observation.scheduledSampler` with `respectsFactorization_scheduledSampler`. |
| `SubTheory.lean` | `SubTheory` (a boundary-indexed membership predicate on `T.Obj` closed under `map` / `par` / `wire`), the `IsPlugClosed` and `IsStructural` mixins, standard `PartialOrder` / `OrderTop` / `SemilatticeInf` instances, ordinary `generated`, and the separately named least plug-closed construction `plugGenerated`. This is structural membership only: resource, efficiency, realizability, protocol-class, and corruption readings require explicit bridges. |
| `Emulates.lean` | `Observation`, `Emulates`, `UCSecure`. Contextual emulation and UC security stated abstractly over an `Observation` (an equivalence relation on closed systems), with no probability monad and no concrete security predicate. Composition takes its exact structural input from the observation via `Observation.RespectsPlugComm` / `Observation.RespectsFactorization`; theories with `HasPlugFactorization` (in particular every strict `HasPlugWireFactor` theory) satisfy both automatically. Process-backed security observations must prove these laws without erasing security-visible packet, action, or sampler data. |
| `EmulatesQuotient.lean` | `Observation.comap` / `Observation.descend` / `Observation.ofCongruence` moving observations across a quotient, `comap_eq_rel` (equality of classes pulls back to the congruence), `Emulates.quotient_iff` / `Emulates.ofCongruence_iff`, and the instances pulling `RespectsPlugComm` / `RespectsFactorization` back along `comap`, so a theory whose laws hold modulo a congruence gets the composition suite at any observation factoring through its quotient |
| `EmulatesWithin.lean` | `EmulatesWithin` (emulation quantified only over `SubTheory`-allowed closing contexts) and its relativized composition suite, plus `UCSecureWithin` and `SubTheory.PreservesAllowedness`. The latter says only that the chosen simulator maps allowed contexts to allowed contexts; it does not prove simulator realizability or efficiency. Real/ideal protocol membership is also separate. Each composition theorem requests the precise component membership needed to build its residual context. `emulatesWithin_top_iff` shows the layer is a conservative extension. |
| `OpenSyntax/AtomSubTheory.lean` | `AllowedGen` / `atomSubTheory` (the least map/par/wire-closed sub-theory of quotiented `Expr.theory` generated by an allowed set of atoms plus identity wires), the pullback `interpretSubTheory`, and `mem_interpret_of_atoms`: if every allowed atom interprets into a target sub-theory, so does every generated expression. Quotient equality preserves membership; membership is not generally decidable. |
| `OpenProcessFactorization.lean` | the four structural `plug` factorization laws for `openTheory` up to `OpenProcessActivationEquiv` (`openTheory_plug_{par,wire}_{left,right}_activation_equiv`), each a reassociation and a commutation under the `OpenProcessCoherence` congruences, and their executable scheduler truth tables; packet/sampler-aware promotion requires a separate scheduler-transport theorem |
| `ActivationObservation.lean` | `Observation.activation`, the structural observation packaging `OpenProcessActivationEquiv` over `openTheory`, with `RespectsFactorization` supplied by the named activation-equivalence theorems. Judges coarse activation structure only — not a security observation; it makes the full `Emulates` composition suite available over the process model at the activation level. |
| `GlobalSubroutine.lean` | `OpenTheory.withGlobal` (wire a shared global resource onto a protocol's subroutine face), directional `SecurelyEmulatesWithGlobal`, and the stronger symmetric `EmulatesWithGlobal` / `EmulatesWithGlobalWithin`. `wire_outer` / `wire_compose_outer` compose only the symmetric relation; secure UCGS still needs structural simulators. |
| `SecureEmulation.lean` | `SecurelyEmulates` / `SecurelyEmulatesWithin`, the existential context-transformer judgment, its reconciliation with `Emulates` and `UCSecure`, and its local preorder. This is not yet FKKKT26's resource preorder: no resource-category translation or structural simulator morphism is present, and consequently no `par`/`wire` monotonicity is claimed. |
| `OpenProcessSamplerEquiv.lean` | `MonadRelFamily` (the abstract relation family on `m`-computations a downstream semantics supplies; `.top` forgets sampler effects), `IsSamplerBisimulation` (strong one-to-one path matching preserving silence, boundary traces, successor relatedness, and `R`-related sampled paths), and `OpenProcessSamplerEquiv` with refl/symm/trans and `toActivationEquiv`. Scheduler-transport facts are deliberately hypotheses of the sampler-aware factorization theorems, not theorems here — a shared scheduler does not preserve per-step scheduling distributions across reassociation. |
| `OpenProcessSamplerCoherence.lean` | `MonadRelFamily.IsBindCongr` (right-continuation congruence; instances for `eq` and `top`), `OpenProcessFactorization.Leaf`, the nested scheduler draws `nestedDrawLeft` / `nestedDrawFactorLeft` / `nestedDrawFactorRight` with their bind equations, the path re-encodings `flipInterleavePathEquiv` / `parLeftPathEquiv` / `parRightPathEquiv` / `{left,right}BranchPathEquiv`, the sampled-path flattening lemmas, the shapes `interleave_factor{Left,Right}_samplerEquiv` / `interleave_comm_samplerEquiv` / `interleave_rehome_samplerEquiv` / `interleave_assoc_samplerEquiv` (identically decorated leaves, internal scheduler nodes, related nested draws), and the congruences `OpenProcess.interleave_congr_{left,right}_samplerEquiv` / `mapHom_congr_samplerEquiv`. No unit absorption: a silent unit adds a path to every step. |
| `OpenProcessSamplerFactorization.lean` | The five sampler-aware plug laws `openTheory_plug_{comm,par_left,par_right,wire_left,wire_right}_sampler_equiv`, each conditional on its named scheduler-transport fact (`schedulerFlip`-fairness, `sourceDraw`/`leftDraw`/`rightDraw` relatedness) and each one instance of a sampler-level shape after normalization; the monoidal laws `openTheory_{par_comm,wire_comm}_sampler_equiv` (fairness) and `openTheory_par_assoc_sampler_equiv` (fairness, the left transport fact, and `IsBindCongr`); the closed composites and tensor reindexings of the theory's injections; and the congruence laws `openTheory_{map,par,wire,plug}_congr_*_sampler_equiv` under `MonadRelFamily.IsBindCongr`. The activation-equivalence laws keep their direct monad-free proofs; these strengthen them for lawful monads. |
| `SamplerObservation.lean` | `Observation.respectsFactorization_of_samplerInvariant` — any observation invariant under sampler equivalence respects plug commutation and factorization, given the transport facts — and the canonical sampled-path observation `Observation.sampler`. This exposes rather than solves the distributional scheduler obstruction: exact equality generally cannot prove the transport premises, and packet/action adequacy remains downstream. |
| `OpenProcessQuotient.lean` | `openTheory.activationCongruence` (activation equivalence as a congruence; the laws modulo it are the `openTheory_*_activation_equiv` theorems, so the activation quotient is strictly `HasPlugWireFactor`), `openTheory.samplerCongruence R` with `hasPlugFactorization_quotient_samplerCongruence` under the transport facts, `scheduledOpenTheory.samplerCongruence R` (equal mass and sampler-equivalent processes) with `hasPlugFactorization_quotient_samplerCongruence` under scheduler coherence, and `Observation.activation` / `Observation.sampler` as pull-backs of equality on the quotients |
| `Notation.lean` | UC notation helpers (`∥`, `⊞`, `⊠`, `⊗ᵇ`, `ᵛ`); see [`notation.md`](notation.md) |
| `MachineId.lean` | machine identifiers |
| `EnvAction.lean` | environment actions, parametric over an arbitrary monad `m` (no probability dependency) |
| `EnvOpenProcess.lean` | open-process wrappers around `EnvAction`, also monad-parametric |
| `CorruptionModel.lean` | corruption-model surface, parametric over `m` |
| `MomentaryCorruption.lean` | momentary corruption surface, parametric over `m` |
| `Leakage.lean` | leakage-oriented UC observation helpers |

UC files that depended on a probability monad in VCVio (`Computational.lean`,
`Runtime.lean`, `AsyncRuntime.lean`, `AsyncSecurity.lean`, `Standard.lean`,
`StdDoBridge.lean`) deliberately do **not** appear in PolyFun. They live in
[`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio) and
re-import the generic primitives from PolyFun.

## In-tree examples

- [`PolyFunTest/Interaction/TwoParty/Examples.lean`](../../PolyFunTest/Interaction/TwoParty/Examples.lean):
  `rfl` checks that `withRoles` / `Counterpart` types unfold correctly on
  a two-step type tree.
- [`PolyFunTest/Interaction/Multiparty/Examples.lean`](../../PolyFunTest/Interaction/Multiparty/Examples.lean):
  pattern-matching resolvers for broadcast, directed, and profile-based
  models; adversarial leakage and adaptive corruption.
- [`PolyFunTest/Interaction/Concurrent/Examples.lean`](../../PolyFunTest/Interaction/Concurrent/Examples.lean):
  small concurrent source terms with profiles, control, process execution,
  policies, and interleaving.

End-to-end UC examples that involve probability monads or concrete
cryptographic content (one-time pad, oracle protocols, etc.) live in
VCVio rather than PolyFun, by design.
