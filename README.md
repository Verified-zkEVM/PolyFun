# PolyFun

Polynomial functors, interaction trees, and dependent interaction frameworks
in Lean 4 — generic substrate for protocol theory, PL semantics, and
concurrent systems.

## Status

Bootstrap. The first wholesale port from
[`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io) is in
progress; see [`PORTING-PLAN.md`](PORTING-PLAN.md) for the exhaustive plan,
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

## License

Apache-2.0.
