# Repo Map

This repo is easiest to navigate by subtree, not by individual file name.
Most developments cluster by layer: `PFunctor` substrate, `ITree`,
`Interaction` framework. Cross-layer notes belong here; per-layer details
live in the dedicated pages [`pfunctor.md`](pfunctor.md),
[`itree.md`](itree.md), and [`interaction.md`](interaction.md).

## Main Surfaces

```text
PolyFun/
  PFunctor/          polynomial functors, charts, lenses, equivalences,
                     M-type / cofree, free monad and displayed-free
  IPFunctor/         state-indexed polynomial functors and their free monads
                     (single-index FreeM, two-index FreeM₂ + IndexedMonad)
  ITree/             coinductive interaction trees, bisim/sim, handlers,
                     event signatures
  Interaction/       generic interaction framework
    Basic/           Spec, Node, Decoration, Strategy, Append, ...
    TwoParty/        sender/receiver roles, paired strategies
    Multiparty/      per-party local view modes, observation kernels
    Concurrent/      structural and dynamic concurrent semantics
    UC/              open-process / open-theory layer (no security content)
  Control/           monad and comonad infrastructure (Coalg, Comonad,
                     Lawful, Free, FreeCont, Hom, Iter, Trace)
  Logic/             small logic helpers (HEq)

docs/wiki/           agent-facing notes (this directory)
scripts/             repo utilities (validate, lint, update-lib, port helpers)
.github/workflows/   CI workflows
```

## Conceptual Layering

Imports flow strictly downward, cycles are a build error. The DAG is also
recorded in [`AGENTS.md`](../../AGENTS.md):

```text
PFunctor/{Basic, Bound, M, Equiv, Chart, Lens}
  -> PFunctor/{Cofree, Trace}
  -> PFunctor/Resumption
PFunctor/Free/Basic
  -> PFunctor/Free/Displayed
  -> PFunctor/Free/{Path, Displayed/Decoration}
  -> PFunctor/Free/Cursor
PFunctor/{Resumption, Free/Basic} -> PFunctor/Free/Resumption

Logic/HEq, Control/{Coalgebra, Comonad, Lawful, Monad}
  (free-standing helpers, depended on by both PFunctor and ITree)

PFunctor/Lens/{Basic, Cartesian, State}
  -> PFunctor/Lens/{Composite, Distributivity, Factorization, Duoidal}
  -> PFunctor/{InternalHom, CartesianClosed, Adjunctions, Comonoid}

PFunctor/{Lens, Cofree, M} + Control/Coalgebra
  -> PFunctor/Dynamical/{Basic, Safety, Combinators, Run, Speedup, Trajectory}
  -> PFunctor/Dynamical/{Behavior, Simulation, RunN, DynComputation, IOMachine}
  -> PFunctor/Dynamical/{Refinement, Responder, Game}

  (Dynamical also draws on PFunctor/Comonoid and PFunctor/Free/Basic
   for RunN and IOMachine, PFunctor/InternalHom for Responder, and
   PFunctor/Lens/Duoidal for Game.)

PFunctor/Free -> ITree/{Basic, Construct, Handler, Rec,
                        Events, Sim, Bisim}
PFunctor/Dynamical + ITree/Basic -> ITree/Unfold

PFunctor/Free + Control -> Interaction/Basic/{Spec, Node, Decoration,
                            Syntax, Shape, Interaction, Strategy,
                            Append, Replicate, StateChain, Chain,
                            Telescope, Sampler, MonadDecoration,
                            BundledMonad, Ownership, SpecFintype}

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
```

`PolyFun.lean` is a generated umbrella import file, not a hand-maintained
module index. See [`generated-files.md`](generated-files.md).

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
- Working on the generic interaction framework (sequential `Spec`,
  decorations, strategies, two-party, multiparty, concurrent, UC open
  systems): start in `PolyFun/Interaction/`. See
  [`interaction.md`](interaction.md).
- Adding monad / comonad helpers, lawful re-exports, or free-monad
  algebra: start in `PolyFun/Control/`.
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
