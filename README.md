# PolyFun

Polynomial functors, interaction trees, and dependent interaction frameworks
in Lean 4, generic substrate for protocol theory, PL semantics, and
concurrent systems.

## Status

PolyFun is a ready, buildable Lean 4 library. The repository builds without
`sorry` or `admit` placeholders, and the public documentation reflects the
current module layout and scope.

PolyFun originated as a wholesale extraction from
[`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio).

## Scope

`PolyFun` collects three layers of generic, domain-agnostic infrastructure
that emerged from the cryptographic-protocols formalization in `VCVio`:

1. **Polynomial functors and lenses.** `PFunctor` cores (positions /
   directions), polynomial charts, lenses, equivalences, free monad
   `FreeM`, displayed `FreeM`, and the `Cofree` / M-type companion.
2. **Interaction trees** in the style of Xia, Zakowski, He, Hur, Malecha,
   Pierce, and Zdancewic (POPL 2020), modeled as the M-type of a one-step
   polynomial functor, with strong/weak bisimulation, simulation,
   handlers, and event signatures.
3. **Generic interaction framework** for sequential, two-party, multi-party,
   and concurrent interaction over a `TypeTree` polynomial substrate, with
   structural decoration, syntax/strategy/execution lenses, and an
   open-process layer for compositional reasoning.

Cryptographic content (probabilistic semantics, evaluation distributions,
oracle simulation, security definitions) lives in
[`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio)
and depends on this library.

## Build

```bash
lake exe cache get
lake build
```

Requires the toolchain pinned in [`lean-toolchain`](lean-toolchain), along with
[`mathlib v4.32.0`](https://github.com/leanprover-community/mathlib4) and [`cslib v4.32.0`](https://github.com/leanprover/cslib).

## Documentation

- [`AGENTS.md`](AGENTS.md), [`CLAUDE.md`](CLAUDE.md): one-screen guide for
  human and AI contributors. Symlinked.
- [`CONTRIBUTING.md`](CONTRIBUTING.md): style, naming, attribution, and large-
  contribution policy.
- [`REFERENCES.md`](REFERENCES.md): the bibliography backing module
  docstrings.
- [`docs/wiki/`](docs/wiki/): deeper agent-facing notes on the
  `PFunctor` substrate, interaction trees, the interaction framework,
  notation, and recurring gotchas.

## License

Apache-2.0.
