# Repo Map

This repo is easiest to navigate by subtree, not by individual file name.
Most developments cluster by layer: `PFunctor` substrate, `ITree`,
`Interaction` framework. Cross-layer notes belong here; per-layer details
live in the dedicated pages [`pfunctor.md`](pfunctor.md),
[`itree.md`](itree.md), and [`interaction.md`](interaction.md).

## Main Surfaces

```text
PolyFun/
  PFunctor/          polynomial functors, charts, lenses, displays,
                     equivalences, M-type / cofree, free monad and displayed-free
  IPFunctor/         state-indexed polynomial functors and their free monads
                     (single-index FreeM, two-index FreeM₂ + IndexedMonad)
  ITree/             coinductive interaction trees, bisim/sim, handlers,
                     event signatures, relational trees, finite traces
  Interaction/       generic interaction framework
    Basic/           TypeTree, Node, Decoration, Strategy, Append, ...
    TwoParty/        sender/receiver roles, paired strategies
    Multiparty/      per-party local view modes, observation kernels
    Concurrent/      structural and dynamic concurrent semantics
    UC/              open-process / open-theory layer (no security content)
  Realizability/     step classes and realizability of dynamical systems and
                     free programs by admissible first-order machines;
                     executable quantitative realizers and syntactic run costs
  Complexity/        generic resource-bound syntax (not a concrete complexity class)
  Control/           monad/comonad and LTS infrastructure (Coalgebra,
                     Comonad, Lawful, Free, Iter, Bisimulation, LTS/Trace),
                     including the program-logic kernel
                     (Monad/{Algebra, Support}), its bridges to core's
                     lattice-generic WP stack (Monad/{Algebra, Support, Hom}/WP)
                     and the core-Std.Do quarantine root (Do/Basic)
  Logic/             small logic helpers (HEq)

ToCslib/             lowest production layer, staging what PolyFun upstreams:
                     cslib machine-API extensions (Computability/), free-monad
                     additions (Data/PFunctor/Free/), loop transport and
                     effect-free loop instances (Control/), and the Mathlib →
                     core order bridge (Order/); imports core, cslib and
                     Mathlib, never PolyFun or Std.Do

docs/wiki/           agent-facing notes (this directory)
scripts/             repo utilities (validate, lint, update-lib, port helpers)
.github/workflows/   CI workflows
```

## Conceptual Layering

Imports flow strictly downward, cycles are a build error. The DAG is also
recorded in [`AGENTS.md`](../../AGENTS.md):

`ToCslib` is the lowest layer of this DAG:

```text
Cslib + Mathlib + core Std.Internal -> ToCslib -> PolyFun
```

`PolyFun/PFunctor/Free/Basic.lean` imports `ToCslib.Data.PFunctor.Free.Basic`
and backend adapters import the machine modules; `ToCslib.Order.LeanOrder`
is where the program-logic kernel picks up core's order hierarchy. `ToCslib` contains staged upstream
material only: no realizability, oracle, probability, or cryptographic policy,
and no `Std.Do` / `Std.Internal.Do` imports.

```text
PFunctor/{Basic, Bound, M, Equiv, Chart, Lens}
  -> PFunctor/{Cofree, Trace}
  -> PFunctor/Resumption
Logic/HEq + PFunctor/{M, Lens/Basic} -> PFunctor/M/Vertex
PFunctor/M/Vertex -> PFunctor/M/WellFounded
IPFunctor/Basic + PFunctor/M/Vertex -> IPFunctor/M
IPFunctor/Free/{Basic, Indexed} + IPFunctor/Notation/Common
  -> IPFunctor/Notation + IPFunctor/Notation/{Indexed, Deterministic}
PFunctor/Display/Basic
  -> PFunctor/Display/{Chart, Coalgebra, Indexed, Free}
IPFunctor/M + PFunctor/Display/Indexed -> PFunctor/Display/M
PFunctor/Handler -> PFunctor/Handler/Instrumentation
PFunctor/{Handler, Free/Basic} -> PFunctor/Handler/Free
  -> PFunctor/Handler/Stateful -> PFunctor/Handler/Normalization/Attr
  -> PFunctor/Handler/Normalization
PFunctor/{Display/Free, Handler/Free}
  -> PFunctor/Display/Handler -> PFunctor/Display/Handler/Sigma
  -> PFunctor/Wiring
PFunctor/Display/{Chart, Handler} -> PFunctor/Display/Lens
PFunctor/Equiv/Basic -> PFunctor/Parallel -> PFunctor/Display/Parallel
PFunctor/{Handler/Free, Parallel} -> PFunctor/Free/Parallel
PFunctor/{Display/Lens, Display/Parallel, Free/Parallel}
  -> PFunctor/Display/Parallel/Lens
PFunctor/{Display/Handler, Display/Parallel, Free/Parallel}
  -> PFunctor/Display/Parallel/Free
PFunctor/{Display/Parallel/Free, Wiring} -> PFunctor/Wiring/Parallel
PFunctor/{Display/Handler, Free/Universal} -> PFunctor/Display/Category
PFunctor/Free/Basic -> PFunctor/Free/Fold
PFunctor/Free/Basic
  -> PFunctor/Free/Displayed
  -> PFunctor/Free/{Path, Displayed/Decoration}
  -> PFunctor/Free/Path/Execution
  -> PFunctor/Free/Cursor
  -> PFunctor/Free/Displayed/Cursor
  -> PFunctor/Free/Cursor/Append
  -> PFunctor/Free/Cursor/Occurrence
  -> PFunctor/Free/Cursor/Fork
PFunctor/{Bound, Free/Path/Execution} -> PFunctor/Free/Path/Bounded
PFunctor/{Free/Basic, Lens/Cartesian} -> PFunctor/Free/Sigma
PFunctor/{Resumption, Free/Basic} -> PFunctor/Free/Resumption
PFunctor/{Free/Resumption, M/WellFounded} -> PFunctor/Resumption/WellFounded
PFunctor/{Resumption, M/Vertex} -> PFunctor/Resumption/Empty
PFunctor/{Bound, Free/Resumption} -> PFunctor/Resumption/Truncate
PFunctor/Dynamical/DynComputation + PFunctor/{Bound, Handler, Resumption/Truncate}
  -> PFunctor/Dynamical/DynComputation/Bounded
PFunctor/{Free/Fold, Dynamical/DynComputation/Bounded}
  -> PFunctor/Dynamical/DynComputation/BoundedFold
PFunctor/Dynamical/DynComputation/Bounded
  -> PFunctor/Dynamical/DynComputation/Termination

Logic/HEq, Control/{Coalgebra, Comonad, Lawful, Monad, Bisimulation, LTS/Trace}
  (free-standing helpers, depended on by both PFunctor and ITree)
  Control/Bisimulation additionally imports cslib
  (Cslib.Foundations.Semantics.LTS.Bisimulation): the transition-system theory
  is cslib's, reached through `Control.LTS.toLts`.

Control/Monad/Algebra -> Control/Monad/Algebra/Relational
Control/Monad/{Algebra/Relational, Support}
  -> Control/Monad/Algebra/Relational/Support
Control/Monad/Hom + Mathlib.Control.Monad.Writer -> Control/Monad/Hom/Writer
Control/Monad/Support -> Control/Do/Basic  (also imports Std.Tactic.Do; see
  the quarantine rule in program-logic.md)

PFunctor/Lens/{Basic, Cartesian, State}
  -> PFunctor/Lens/{Composite, Distributivity, Factorization, Duoidal}
  -> PFunctor/{InternalHom, CartesianClosed, Adjunctions, Comonoid}

PFunctor/Lens/Basic -> PFunctor/SubstMonoid
PFunctor/{Free/Path, SubstMonoid} -> PFunctor/Free/Polynomial
PFunctor/Free/Path + Control/Monad/Support -> PFunctor/Free/Support
PFunctor/{Free/Support, Handler} -> PFunctor/Free/WP
  (demonic/angelic and admitted-response leaf contracts, including free-handler closure)
Control/Do/Basic + PFunctor/Free/WP -> PFunctor/Free/Do
PFunctor/Comonoid -> PFunctor/Comonoid/Category
PFunctor/{Comonoid, Lens/Duoidal} -> PFunctor/Comonoid/Tensor
PFunctor/{SubstMonoid, Comonoid, InternalHom, Lens/Duoidal}
  -> PFunctor/SubstMonoid/Convolution

PFunctor/{Cofree, Comonoid, M/Vertex}
  -> PFunctor/Cofree/Polynomial

PFunctor/{Cofree/Polynomial, Comonoid/Category}
  -> PFunctor/Cofree/Universal
  -> PFunctor/Cofree/FiniteProjection
PFunctor/{Cofree/Universal, Comonoid/Tensor}
  -> PFunctor/Cofree/LaxMonoidal
PFunctor/{Basic, Equiv/Basic, Lens/Basic, Chart/Basic, InternalHom,
  Adjunctions, Cofree/FiniteProjection}
  -> PFunctor/Deprecated  (aggregate import for module-owned transitional
     X-spelling compatibility)
PFunctor/{Free/Polynomial, Cofree/Polynomial}
  -> PFunctor/PatternRunsOnMatter/Basic
PFunctor/{PatternRunsOnMatter/Basic, Free/Universal,
  Cofree/Universal, SubstMonoid/Convolution}
  -> PFunctor/PatternRunsOnMatter/Universal
PFunctor/{PatternRunsOnMatter/Universal, Cofree/LaxMonoidal}
  -> PFunctor/PatternRunsOnMatter/Module
PFunctor/PatternRunsOnMatter/Universal + PFunctor/Handler
  -> PFunctor/PatternRunsOnMatter/Operational
PFunctor/PatternRunsOnMatter/Basic + PFunctor/Dynamical/{CofreeMate, Simulation, Game}
  -> PFunctor/PatternRunsOnMatter/Dynamical
PFunctor/PatternRunsOnMatter/{Module, Dynamical} + PFunctor/Dynamical/Bisimulation
  -> PFunctor/PatternRunsOnMatter/Applications

PFunctor/{Lens, Cofree, M} + Control/Coalgebra
  -> PFunctor/Dynamical/{Basic, Safety, Combinators, Run, Speedup, Trajectory}
  -> PFunctor/Dynamical/{Behavior, Simulation, RunN, DynComputation}
  -> PFunctor/Dynamical/{Refinement, Responder, Game}
PFunctor/{Cofree/Universal, Dynamical/Trajectory}
  -> PFunctor/Dynamical/CofreeMate
PFunctor/{Cofree/FiniteProjection, Dynamical/CofreeMate, Dynamical/RunN}
  -> PFunctor/Dynamical/CofreeMate/FiniteProjection
PFunctor/Display/Coalgebra + PFunctor/Dynamical/Responder
  -> PFunctor/Dynamical/Responder/Display
  -> PFunctor/Dynamical/Responder/Reindex
  -> PFunctor/Dynamical/Responder/Behavior
PFunctor/Dynamical/Simulation
  -> PFunctor/Dynamical/Responder/Behavior
  -> PFunctor/Dynamical/Responder/Presentation
PFunctor/{Display/Lens, Dynamical/Responder/Presentation}
  -> PFunctor/Dynamical/Responder/Lens
PFunctor/{Parallel, Dynamical/Responder}
  -> PFunctor/Dynamical/Responder/Parallel
PFunctor/{Display/Parallel, Dynamical/Responder/Display,
  Dynamical/Responder/Parallel}
  -> PFunctor/Dynamical/Responder/Parallel/Display
PFunctor/{Dynamical/Responder/Behavior,
  Dynamical/Responder/Parallel/Display}
  -> PFunctor/Dynamical/Responder/Parallel/Behavior
PFunctor/{Dynamical/Responder/Parallel/Behavior, Free/Parallel}
  -> PFunctor/Dynamical/Responder/Parallel/Compatibility
PFunctor/Dynamical/Responder/{Presentation, Parallel/Behavior}
  -> PFunctor/Dynamical/Responder/Parallel/Presentation
PFunctor/{Free/Parallel, Dynamical/Responder/Lens,
  Dynamical/Responder/Parallel/Behavior}
  -> PFunctor/Dynamical/Responder/Parallel/Coherence
PFunctor/{Display/Parallel/Lens,
  Dynamical/Responder/Parallel/Coherence,
  Dynamical/Responder/Parallel/Presentation}
  -> PFunctor/Dynamical/Responder/Parallel/DisplayedAssociativity
  -> PFunctor/Dynamical/Responder/Parallel/DisplayedCoherence
PFunctor/{Display/Category, PatternRunsOnMatter/Applications,
  Dynamical/Responder/Behavior} -> PFunctor/PatternRunsOnMatter/Display
PFunctor/{PatternRunsOnMatter/Display,
  Dynamical/Responder/Parallel/Compatibility}
  -> PFunctor/PatternRunsOnMatter/Parallel

  (Dynamical also draws on PFunctor/Comonoid for RunN,
   PFunctor/{Free/Basic, Resumption} for DynComputation,
   PFunctor/InternalHom for Responder, and PFunctor/Lens/Duoidal for Game.)

PFunctor/Free -> ITree/{Basic, Construct, Handler, Rec,
                        Events, Sim, Bisim, Trace}
PFunctor/Free/Resumption + ITree/Sim/Facts -> ITree/Resumption
ITree/Resumption + PFunctor/M/Vertex -> ITree/ResumptionWithTau
ITree/ResumptionWithTau + PFunctor/{Handler/Free, Resumption/WellFounded}
  -> ITree/Free
ITree/Resumption + PFunctor/{Dynamical/Trajectory, Resumption/Empty}
  -> ITree/Unfold
ITree/Free + PFunctor/PatternRunsOnMatter/Dynamical
  -> ITree/PatternRunsOnMatter
ITree/Bisim/Iter -> ITree/Do
  (the scoped productive `ForIn` instance and its invariant-scoped `WeakBisim`
   congruence, so `Do` sits above the bisimulation layer)

PFunctor/Free + Control -> Interaction/Basic/{TypeTree, Node, Decoration,
                            Syntax, Shape, Interaction, Strategy,
                            Append, Replicate, StateChain, Chain, Chain/Append,
                            Telescope, Sampler, MonadDecoration,
                            BundledMonad, Ownership, TypeTreeFintype}

Interaction/Basic -> Interaction/{TwoParty, Multiparty}
Interaction/Basic + PFunctor/Dynamical -> Interaction/Concurrent
  (concurrent processes and machines are dynamical systems over their step
   polynomials; TwoParty/Multiparty do not depend on PFunctor/Dynamical)

Interaction/{Concurrent, Basic} -> Interaction/UC/{Interface,
                                   OpenProcess, OpenProcessModel,
                                   OpenTheory, OpenSyntax, Notation,
                                   Emulates, MachineId, EnvAction,
                                   EnvOpenProcess, CorruptionModel,
                                   MomentaryCorruption, Leakage}

Interaction/UC/OpenTheory -> Interaction/UC/SubTheory
Interaction/UC/{OpenTheory, SubTheory}
  -> Interaction/UC/OpenTheory/Family
Interaction/UC/{Emulates, SubTheory} -> Interaction/UC/EmulatesWithin
Interaction/UC/{OpenSyntax/Expr, SubTheory}
  -> Interaction/UC/OpenSyntax/AtomSubTheory
  (SubTheory is a structural membership predicate and depends on the algebra
   alone; EmulatesWithin uses it specifically for allowed closing contexts.
   Protocol membership, resource and realizability claims, and links to
   CorruptionModel require separate bridges. The residual-context lemmas live
   with EmulatesWithin because the context-formers are defined in Emulates.)

Interaction/UC/OpenProcessModel -> Interaction/UC/OpenProcessFactorization
  (a structural result about OpenProcessActivationEquiv only; Emulates is
   model-agnostic and must not reach OpenProcess, so observation-level
   promotions of these laws live above both)

Interaction/UC/{Emulates, OpenProcessFactorization}
  -> Interaction/UC/ActivationObservation
  (Observation.activation promotes activation equivalence to a structural
   observation whose RespectsFactorization fields are the named
   activation-equivalence theorems; a packet- or sampler-aware observation is
   a separate, stronger construction and is not in tree)

Interaction/UC/SecureEmulation -> Interaction/UC/GlobalSubroutine
  (directional and unconditional emulation with a shared global resource;
   outer composition is currently available only for the stronger
   unconditional relation)

Interaction/UC/EmulatesWithin -> Interaction/UC/SecureEmulation
  (the existential-simulator judgment and its preorder; directional,
   unlike Emulates, and ordered per observation)

Interaction/UC/OpenProcess -> Interaction/UC/OpenProcessSamplerEquiv
  (strong sampled-path strengthening of activation equivalence, relative to
   an abstract relation family on m-computations; forgets onto
   OpenProcessActivationEquiv, while packet/action adequacy remains separate)

Interaction/UC/{OpenProcessFactorization, OpenProcessSamplerEquiv}
  -> Interaction/UC/Scheduler
Interaction/UC/{OpenProcessModel, Scheduler}
  -> Interaction/UC/ScheduledOpenProcessModel
  (positive scheduler masses, the flat three-way coherence contract, and an
   additive mass-aware open-process theory; concrete proportional sampling
   and distributional adequacy remain downstream)

Interaction/UC/{OpenProcessSamplerFactorization, Scheduler}
  -> Interaction/UC/ScheduledSamplerFactorization
  (the scheduler coherence law lifted through arbitrary component samplers
   along the existing left/right structural path reassociations)

Interaction/UC/{OpenProcessModel, OpenProcessFactorization,
                OpenProcessSamplerEquiv}
  -> Interaction/UC/OpenProcessSamplerFactorization
  (the five coherence laws at sampler equivalence, conditional on named
   scheduler-transport hypotheses; the activation laws keep their direct
   monad-free proofs)

Interaction/UC/{Emulates, OpenProcessSamplerFactorization}
  -> Interaction/UC/SamplerObservation
  (sampler-invariant observations respect factorization; the canonical
   sampler observation)
Interaction/UC/{OpenProcessModel, SubTheory}
  + Realizability/{DynSystem, DynSystemClosure}
  -> Interaction/UC/Realizability
  (structural open-process realizability and composition-closed sub-theories,
   with the composite closure theorems derived through the product-state
   combinator; sampler cost and computational security remain downstream)

PFunctor/Basic -> Realizability/StepClass
PFunctor/Dynamical/Combinators + Realizability/StepClass
  -> Realizability/DynSystem
Realizability/DynSystem -> Realizability/DynSystemClosure
  (closure of dynamical realizability under wrapped asynchronous choice;
   the product-state combinator behind the UC composite closure theorems)
PFunctor/Dynamical/DynComputation/Bounded -> Realizability/Machine
Realizability/{DynSystem, DynSystemClosure, StepClass, Machine}
  -> Realizability/Basic
Realizability/Basic -> Realizability/{Closure, Instances, Representation}
Realizability/Basic -> Realizability/Quantitative
Realizability/Quantitative -> Realizability/Quantitative/Closure
Realizability/Quantitative/Closure -> Realizability/Quantitative/BoundedClosure
{Complexity/SecondOrderPolynomial, Realizability/Quantitative/Closure}
  -> Realizability/Quantitative/Polynomial
{Realizability/Quantitative/BoundedClosure,
 Realizability/Quantitative/Polynomial}
  -> Realizability/Quantitative/Resource
Realizability/{Instances, Quantitative} -> Realizability/Quantitative/WordClass
Mathlib/Order/Monotone/Basic -> Complexity/SecondOrderPolynomial
  (Instances additionally draws on Mathlib's Computability and Fintype layers;
   Quantitative/Closure assembles executable structural code but asserts no
   polynomial-time closure; Quantitative/Polynomial packages explicit
   backend-relative polynomial certificates; Quantitative/Resource adds
   response-relative second-order run contracts without naming a complexity class;
   Complexity contains syntax, not feasibility;
   only the explicit Interaction/UC/Realizability bridge crosses from the
   interaction layer into Realizability/; nothing under PFunctor/ or ITree/
   depends on Realizability/)
```

`PolyFun.lean` is a generated umbrella import file, not a hand-maintained
module index. See [`generated-files.md`](generated-files.md).

Every Lean source uses module mode. The arrows above describe dependency
direction; a `public import` additionally records that the lower module is
part of the importing module's API surface. Within `Interaction/`, exported
declarations live in `public section`, implementation dependencies stay as
plain imports, and reducibility is exposed declaration-by-declaration.

## Where To Start By Task

- Working on the polynomial-functor substrate (positions / directions,
  lenses, charts, free monad, cofree / M-type, displayed `FreeM`): start
  in `PolyFun/PFunctor/`. See [`pfunctor.md`](pfunctor.md) for the layer
  guide.
- Working on state-indexed polynomial functors (multi-phase protocols,
  session-typed interaction): start in `PolyFun/IPFunctor/`. See
  [`ipfunctor.md`](ipfunctor.md).
- Working on coinductive interaction trees, bisimulation, simulation, or
  event signatures: start in `PolyFun/ITree/`. See [`itree.md`](itree.md).
- Working on the generic interaction framework (sequential `TypeTree`,
  decorations, strategies, two-party, multiparty, concurrent, UC open
  systems): start in `PolyFun/Interaction/`. See
  [`interaction.md`](interaction.md).
- Adding monad / comonad helpers, lawful re-exports, or free-monad
  algebra: start in `PolyFun/Control/`.
- Program-logic work (`MAlgOrdered`, `MAlgRelOrdered`, `ExactMonadAttach`,
  `wpFold`, `Std.Do` bridges): start with
  [`program-logic.md`](program-logic.md); definitions live under
  `PolyFun/Control/Monad/` and `PolyFun/PFunctor/Free/{Support, WP, Do}.lean`.
- Adding backend-relative code, exact interaction costs, or generic executable
  closure operations: start in `PolyFun/Realizability/Quantitative.lean` and
  `PolyFun/Realizability/Quantitative/Closure.lean`; for ranked termination,
  trace transport, and restricted pathwise closure, continue with
  `PolyFun/Realizability/Quantitative/BoundedClosure.lean`. Concrete complexity
  classes and adequacy theorems belong downstream.
- Updating notation: start in `PolyFun/Interaction/UC/Notation.lean`. See
  [`notation.md`](notation.md).

## Scope Boundary: No Cryptographic Content

PolyFun is intentionally *not* the place for cryptographic content.
Probabilistic semantics, evaluation distributions, oracle-simulation
security definitions, scheme-specific algebra, and concrete-protocol
runtime layers all live in
[`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio) and
depend on this library.

When in doubt, ask: *can this definition be stated against an arbitrary
monad `m` with `[Monad m]` and friends, with no probability, no security
predicate, and no concrete cryptographic algebra?* If the answer is yes,
it belongs in PolyFun. If the answer is no, it belongs downstream in
VCVio or a more specialized repo.

## Navigation Notes

- `PolyFun.lean` is generated. After adding, renaming, or deleting `.lean`
  files under `PolyFun/`, run `./scripts/update-lib.sh`.
- Files should stay under 1500 lines unless explicitly opted out per file.
  The long-file linter cap is enforced via the lint workflow.
- Before assuming a file is authoritative, check whether it is source or
  derived output. See [`generated-files.md`](generated-files.md).
