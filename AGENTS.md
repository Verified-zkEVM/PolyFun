# PolyFun — AI Agent Guide

PolyFun is a Lean 4 library for polynomial interfaces, programs, machines,
interaction trees, generic open-system composition, program logic, and
realizability. It extends Mathlib and CSLib. Cryptographic interpretations,
probability semantics, distinguishing advantage, and scheme-specific proofs
belong in [VCVio](https://github.com/Verified-zkEVM/VCVio).

`AGENTS.md` is the canonical agent guide; `CLAUDE.md` is its symlink.
Human readers should start with [README.md](README.md) and the
[documentation hub](docs/README.md). [CONTRIBUTING.md](CONTRIBUTING.md)
is the attribution and contribution policy.

## Start and validate

```bash
lake exe cache get
lake build
./scripts/validate.sh --lint --test --axioms
```

The wrapper builds production and example libraries plus the executable entry point, checks module/import/docs
integrity, and optionally runs linters, regressions, both separate consumers, CLI/filesystem tests, and
the zero-debt axiom gate. See [validation](docs/development/validation.md).
`lake test` builds `PolyFunTest`; `lake lint` covers production and example
libraries, with tests excluded. Use `lake lint -- --trace` after a fresh build
to inspect the environment checks.

## Source map and dependency direction

The canonical [repository map](docs/reference/repo-map.md#conceptual-layering)
records module layering. Update it when adding a module or changing an import
boundary. Imports flow downward and must remain acyclic.

| Root | Responsibility |
|---|---|
| `PolyFun/PFunctor/` | Polynomial operations, lenses/charts, free/cofree structures, handlers, resumptions and dynamical systems |
| `PolyFun/IPFunctor/` | Indexed containers, family/single-index/two-index free programs, indexed coinduction and notation |
| `PolyFun/ITree/` | Coinductive programs with silent steps, bisimulation, handlers and traces |
| `PolyFun/Interaction/Basic/` | `TypeTree`, decorations, syntax, strategies and sequential composition |
| `PolyFun/Interaction/{TwoParty,Multiparty,Concurrent}/` | Roles, local views, concurrency, fairness and refinement |
| `PolyFun/Interaction/Interface.lean` | Shared typed interfaces and directed boundaries |
| `PolyFun/Interaction/Execution/` | Reactive/request networks, routing, budgets and assemblies |
| `PolyFun/Interaction/Open/` | Open theory/syntax/processes, observations, contextual emulation and structural realizability bridge |
| `PolyFun/Control/` | Monad/comonad/coalgebra infrastructure, LTS and program-logic kernel |
| `PolyFun/Realizability/` | Represented types, admissible state machines, representation invariance and quantitative resource certificates |
| `PolyFun/Complexity/`, `PolyFun/Logic/` | Generic resource-bound syntax and small logic helpers |
| `ToCslib/` | Lowest production layer: upstream staging for free-monad, loop, order, bitvector and polynomial lemmas |
| `ComplexityBackends/` | Optional concrete complexity backends, one subdirectory per machine model (`CslibSingleTape/`), outside the generic umbrella |
| `Examples/` | Tutorials and the Parliament case study, target `PolyFunExamples` |
| `PolyFunTest/` | Regression tests; may import tutorials, with no reverse production dependency |

Start with `PFunctor/Basic.lean`, `PFunctor/Free/Basic.lean`, `ITree/Basic.lean`,
and `Interaction/Basic/{TypeTree,Decoration}.lean` under `PolyFun/`.
CSLib owns `PFunctor.FreeM` and the functor-generic `Cslib.FreeM`; extend them.
`ToCslib` imports core, CSLib and Mathlib, never PolyFun, a backend, probability
or cryptography. `ComplexityBackends` imports PolyFun and `ToCslib`; PolyFun never
imports a backend. `scripts/check-modules.sh` enforces both directions.

## Semantic boundaries

- Parameterize generic effects by an abstract monad. Keep oracle/probability
  interpretations, security policy and concrete protocol runtime semantics downstream.
- `TypeTree := PFunctor.FreeM TypeTree.basePFunctor PUnit`. Its `done` and
  `node` are `@[match_pattern, reducible]` wrappers; preserve pattern matching
  and definitional equality with the substrate.
- A coarse activation observation is not a packet-aware or probabilistic
  security observation. The structural open-process bridge does not assert
  real/ideal membership, quantitative bounds, sampler realizability, or a link
  to `CorruptionModel`; those need explicit instances. Follow the
  [open-system contract](docs/guides/open-systems.md).
- `StepClass` representations need not exist for every type. Fix boundary
  encodings; distinguish admissible local steps from whole-program resource
  bounds. Named cryptographic adversary classes remain downstream. See
  [realizability](docs/guides/realizability.md).

## Lean and API policy

All sources use module mode: header, blank line, `module`, blank line, imports,
blank line, module docstring. Use `public section` for the intended API,
`public import` for signature dependencies, plain `import` for implementation
dependencies, and `import all` for proof access to opaque bodies. Expose reducer
bodies individually when definitional equality is part of the public contract.
Broad `@[expose] public section` is forbidden under `PolyFun/Interaction/`.
Use ordinary-import canaries and the separate documentation consumer to check
public equations; see [module APIs](docs/development/module-api.md).

Follow Mathlib naming (`{head_symbol}_{operation}_{rhs_form}`); structures use
UpperCamelCase. Keep files below 1500 lines unless explicitly opted out.
`autoImplicit = false` is global in `lakefile.toml`; declare variables and do
not repeat that option per file. Lean, Mathlib and CSLib versions stay in sync.

Do not add `sorry`, `admit`, or non-standard axioms to finished work. Use `stop`
only when explicitly preserving partial proof work during a refactor. The axiom
baseline must stay empty; update mode refuses to record taint.

Do not disable linters to suppress errors, locally or globally. The narrow
exception is declaration-scoped `set_option linter.checkUnivs false in` for
mathematically intentional independent universes, with an adjacent explanation.
Per-declaration `@[nolint ...]` needs `Batteries.Tactic.Lint` imported. The pinned
CSLib `topNamespace` checker is unregistered; do not add a local replacement or
namespace exceptions for its module-system limitations. See
[lint policy](docs/development/linting.md).

## Std.Do quarantine

Definitions from `Std.Do` and `Std.Internal.Do` may be directly imported only
by `PolyFun/Control/Monad/`, `PolyFun/Control/Do/`, `PolyFun/PFunctor/Free/`,
`PolyFun/ITree/Do.lean`, and `PolyFunTest/Do/`. Tactics from `Std.Tactic.Do`
stay in `PolyFun/Control/Do/`, `PolyFun/PFunctor/Free/Do.lean`, and
`PolyFunTest/Do/`. Export constructions or scoped instances, never global WP
instances. `ToCslib` directly imports neither tier; transitive legacy `Std.Do.WP`
through CSLib's `IsMonadHom` is permitted. See [program logic](docs/guides/program-logic.md).

## Attribution and documentation

Copyright headers always name **PolyFun Contributors**. Preserve the human
`Authors:` line on ordinary edits; change it only for new or materially replaced
files. Do not add separate AI attribution. Follow the exact policy and header
in [CONTRIBUTING.md](CONTRIBUTING.md).

Docstrings describe current definitions, assumptions and live sibling APIs;
avoid removed names, change history and reactive wording. Use Mathlib-style
`/-! ## Title -/` section comments, never ASCII banners. Cite public papers
through [REFERENCES.md](REFERENCES.md).

Update the owning tutorial/guide/reference/development page with API and
workflow changes. Source is authoritative when prose disagrees. Promote durable
learnings into the existing docs, and keep one-time reviews and migration maps
outside the tracked tree. The [maintenance contract](docs/README.md#maintenance-contract)
and [review guide](docs/development/review-hardening.md) apply to every change.

## Generated files and scripts

`PolyFun.lean`, `ToCslib.lean` and `ComplexityBackends.lean` are generated; never
hand-edit them. Stage new/deleted/renamed source files before running
`./scripts/update-lib.sh`, `./scripts/update-lib.sh ToCslib` or
`./scripts/update-lib.sh ComplexityBackends`. See
[generated files](docs/development/generated-files.md).
Tutorial modules use a glob target and need no generated umbrella. The optional
case-study root `Examples/Parliament.lean` is generated with
`./scripts/update-lib.sh Examples.Parliament`; stage new case-study modules first.
Core libraries may not import examples, tests, or `PolyFunParliamentMain`.

Add repository scripts only for concrete recurring workflows under
[the scripts policy](CONTRIBUTING.md#repository-scripts). Reuse existing drivers
for validation. Keep temporary probes outside the tracked repository.
