# PolyFun

Polynomial functors, interaction trees, and dependent interaction frameworks
in Lean 4, generic substrate for protocol theory, PL semantics, and
concurrent systems.

## Status: Experimental

> **PolyFun is in active bootstrap and is not yet stable.** Names, namespaces,
> module layout, design notes, and the wiki under [`docs/wiki/`](docs/wiki/)
> are all expected to change. Treat everything here as a work in progress.
> Documentation, including this README, [`AGENTS.md`](AGENTS.md),
> [`CONTRIBUTING.md`](CONTRIBUTING.md), and [`docs/wiki/`](docs/wiki/), is
> recently authored material that will be edited and refined as the
> formalization matures. Do not treat any of it as gospel; if you find
> something out of date, fix it in the same PR rather than copying it forward.

The first wholesale port from
[`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io) has just
landed; see [`PORTING-PLAN.md`](PORTING-PLAN.md) for the exhaustive plan,
file inventory, and migration sequence.

## Scope

`PolyFun` collects three layers of generic, domain-agnostic infrastructure
that emerged from the cryptographic-protocols formalization in `VCV-io`:

1. **Polynomial functors and lenses.** `PFunctor` cores (positions /
   directions), polynomial charts, lenses, equivalences, free monad
   `FreeM`, displayed `FreeM`, and the `Cofree` / M-type companion.
2. **Interaction trees** in the style of Xia, Zakowski, He, Hur, Malecha,
   Pierce, and Zdancewic (POPL 2020), modeled as the M-type of a one-step
   polynomial functor, with strong/weak bisimulation, simulation,
   handlers, and event signatures.
3. **Generic interaction framework** for sequential, two-party, multi-party,
   and concurrent interaction over a `Spec` polynomial substrate, with
   structural decoration, syntax/strategy/execution lenses, and an
   open-process layer for compositional reasoning.

Cryptographic content (probabilistic semantics, evaluation distributions,
oracle simulation, security definitions) lives in
[`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io)
and depends on this library.

## Build

```bash
lake exe cache get
lake build
```

Requires the toolchain pinned in [`lean-toolchain`](lean-toolchain) and
[`mathlib v4.29.0`](https://github.com/leanprover-community/mathlib4) (only
external dependency).

## Documentation

- [`AGENTS.md`](AGENTS.md), [`CLAUDE.md`](CLAUDE.md): one-screen guide for
  human and AI contributors. Symlinked.
- [`CONTRIBUTING.md`](CONTRIBUTING.md): style, naming, attribution, and large-
  contribution policy.
- [`REFERENCES.md`](REFERENCES.md): the bibliography backing module
  docstrings.
- [`docs/wiki/`](docs/wiki/): deeper agent-facing notes on the
  `PFunctor` substrate, interaction trees, the interaction framework,
  notation, and recurring gotchas. **Recently authored, expected to drift; see
  the warning above.**
- [`PORTING-PLAN.md`](PORTING-PLAN.md): the wholesale port plan from VCV-io.

## License

Apache-2.0.
