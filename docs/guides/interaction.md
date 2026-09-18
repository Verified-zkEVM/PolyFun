# Interaction Framework

For open-system composition and its observation boundary, see
[open systems](open-systems.md). The [PolyFun/VCVio guide](polyfun-and-vcvio.md)
explains how cryptographic applications consume this layer.

General-purpose protocol interaction theory: sequential type trees, two-party
roles, multiparty local views, and concurrent process semantics. PolyFun's
[`PolyFun/Interaction/`](../../PolyFun/Interaction) is intentionally
*generic*. It carries abstract observational judgments, with no probability
semantics or concrete cryptographic algebra. Cryptographic content of any kind belongs
in [`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio)
downstream.

This page is descriptive. The Lean source under
[`PolyFun/Interaction/`](../../PolyFun/Interaction) is the canonical
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
- **Observer-relative open composition.** The open-systems layer
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
| Typed boundaries | `Interface.lean` | Request/reply interfaces and directed ports |
| Execution | `Execution/` | Reactive processes, request networks, routing and assemblies |
| Open systems | `Open/` | Composition algebra, observations, contextual emulation and corruption vocabularies |

`Concurrent/` builds on the sequential and multiparty layers. Interfaces
are shared by execution and open-system modules; execution assemblies consume
the open syntax. See the [dependency map](../reference/repo-map.md#conceptual-layering)
for the allowed import direction.

The source modules make this boundary machine-checkable. Public declarations
are grouped in `public section`; dependencies appearing in their signatures
use `public import`, while implementation-only dependencies remain private.
Definitions are `@[expose]` only when downstream computation or definitional
equality is an intentional part of the API. Proof modules use `import all`
when they need opaque bodies without widening the exported reducer surface.

Downstream packet runtimes can observe `Interface.RoutedPacket.mapSender` through
`sender_mapSender`, `packet_mapSender`, and `mapSender_mk`. These public equations retain
the dependent payload and expose the renamed sender without unfolding the implementation.

## Core concepts: TypeTree, Node, Party, Profile

Before reading any one file, it helps to fix four words. They are the
load-bearing vocabulary of the entire `Interaction/` layer.

### Node, a structural location in the protocol tree

A `TypeTree` is a well-founded protocol shape
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
(`Multiparty/`, `Concurrent/`, `Open/`). A party is an actor that may control
or observe moves at *various* nodes throughout the same protocol tree. A
party is whole-tree (it has a strategy across the entire `TypeTree`); a node
is local (it lives at one location in the tree). Typically there are *many
more* nodes than parties: a long protocol may have unboundedly many nodes
(or a continuation-based infinite stream of them via `ProcessOver`), but
always the same party type.

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
([`PolyFun/Interaction/Open/OpenProcess.lean`](../../PolyFun/Interaction/Open/OpenProcess.lean))
is the open-system extension that adds one `BoundaryAction Δ X` field for
external traffic. `OpenNodeContext.boundaryTrace` extracts the finite
outbound-packet trace emitted along a completed decorated step path;
Generic routing and exact behavior are provided by `Interaction.Execution`;
probabilistic interpretations remain downstream.

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

`TwoParty/PublicCoin.lean` provides ordinary-import constructor equations for
both `replay` and `toCounterpart`. At receiver nodes replay follows a prescribed
challenge, whereas the ordinary counterpart samples a challenge and follows its
indexed continuation. These equations do not assert Fiat-Shamir security or
that the prescribed path was produced by a particular prover.

At the free-program layer, typed replay trees retain a fixed prefix while
branching over chosen responses. The
[heterogeneous replay regression](../../PolyFunTest/PFunctor/ReplayTree.lean)
uses different response types and continuation-dependent branch counts,
checking every selected leaf's output and ordered trace. These are structural
replay guarantees; probability and security bounds require downstream semantics.

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
(`Open/OpenProcessInterleave.lean`); a communicating composition supplies routes
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

## Interfaces, execution, and open systems

`Interaction.Interface` and `PortBoundary` describe typed requests, responses,
and directed boundaries. [Execution](execution.md) explains explicit reactive
and request networks under `Interaction.Execution`.

[Open systems](open-systems.md) explains `Interaction.Open`: the algebra of
`map`, `par`, `wire`, and `plug`; free syntax; monad-parametric open processes;
and the observations needed for contextual emulation. The lawfulness classes
separate strict equations from equations that hold only at a chosen observation.
Coarse activation equivalence forgets sampler effects and packet identity.

`TypeTree.Sampler m` is a decoration supplying an `m X` choice at each move
node. `OpenProcess m Party Δ` carries a sampler for each step, and its
composition also needs scheduler choices. Reassociating a structural composite
does not by itself preserve an effectful scheduler's semantics.

Probability, distinguishing advantage, and computational security belong to
VCVio. See [PolyFun and VCVio](polyfun-and-vcvio.md) for the ownership boundary;
generic declarations named `UCSecure` in PolyFun are parameterized judgments,
not instantiated cryptographic security claims.

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

-- Open systems
import PolyFun.Interaction.Open.OpenTheory
import PolyFun.Interaction.Open.OpenProcess
import PolyFun.Interaction.Open.OpenProcessModel
```

## Finding definitions

The [repository map](../reference/repo-map.md) gives task-oriented entry points.
Within each subtree, start with the module docstring and the imports it uses.
This guide explains the concepts; the source is the declaration index.

## Worked regressions

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
