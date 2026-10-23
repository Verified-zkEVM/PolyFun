# Cryptol language case study

`PolyFunCryptol` models a fragment of [Cryptol](https://github.com/GaloisInc/cryptol)
with PolyFun's general machinery. It follows Cryptol **3.6.0's reference semantics**
for its supported fragment ([CRYPTOL360](../REFERENCES.md#cryptol360--cryptol-syntax-and-reference-semantics)).
It is not a verification of the Haskell evaluator. The library is outside the
backend-neutral `PolyFun` umbrella. It imports PolyFun, ToCslib, CSLib and Mathlib,
and nothing in `PolyFun/`, `ToCslib/` or `ComplexityBackends/` imports it.

Foundation correspondences, cryptographic specifications and probability
statements belong in VCVio (`Interop/Cryptol/Bridge`). The typed-AST exporter,
Foundation census and status, and evaluator audit live here, because they
measure the language rather than any algorithm.
The [cross-repository tracker](https://github.com/Verified-zkEVM/VCVio/issues/879)
coordinates the remaining language and Foundation work.

## How the case study uses PolyFun

| Layer | PolyFun interface | Cryptol obligation |
|---|---|---|
| Resolved and native syntax | [`ScopedSignature`](../PolyFun/IPFunctor/Scoped/Basic.lean) terms, renaming, substitution and interpretation | Typing, primitive vocabulary and the supported fragment |
| Ordered polymorphic syntax | [`ScopedFamily`](../PolyFun/IPFunctor/Scoped/Family.lean) maps and substitution for numeric, type and proof binders | Lawful parameter actions, constraints and quantifier stages |
| Lazy meanings | [`DomainResult`](../PolyFun/Control/Domain/Result.lean), [`PointedDomain`](../PolyFun/Control/Domain/Pointed.lean) and [`ScopedDomain.Env.fixGroup`](../PolyFun/IPFunctor/Scoped/Domain.lean) | Demand rules that keep errors, bottom and suspended components distinct |
| Native implementations | [`CorrespondsOn`, `CertifiedMeaning` and `DataContract`](../PolyFun/Control/Semantics/Correspondence.lean) | Encodings and admissible inputs; totality is never inferred from finite inputs |
| Execution | [`Control.Transition`](../PolyFun/Control/Transition.lean) and its [tree and machine adapters](../PolyFun/ITree/Transition.lean) | Call-by-name machine states, fuel, soundness and adequacy |

The [interop guide](../docs/guides/interop.md) states these boundaries for any
frontend. Its scoped-execution tutorial is an independent consumer of the same
interfaces with a strict evaluation strategy.

## Contents

| Directory | Responsibility |
|---|---|
| `Model/` | Types, partial numeric expressions, constraints and schemes; resolved and ordered polymorphic syntax; lazy domains and denotation; call-by-name execution, soundness and monomorphic adequacy; primitive demand rules |
| `Translation/` | The native scoped IR and its representation relation; typed-AST decoding, scope and kind checks; open-module elaboration; proof-producing constraint evidence; declaration groups; certificates, quotation and export |
| `../PolyFunCryptolTest/` | Semantic, demand, polymorphism and translation regressions |
| `exporter/` | The [pinned typed-AST exporter](exporter/README.md) linked to the official Cryptol frontend |
| `scripts/` | Export, census, corpus and audit drivers, and the offline model, importer and module tests; see the [tooling guide](docs/tooling.md) |
| `fixtures/`, `artifacts/` | PolyFun's own Cryptol fixtures, the committed exports and the [Foundation status](docs/compatibility.md) |

The [tutorial](docs/tutorial.md) imports a small Cryptol function and proves facts
about it. The [model guide](docs/model.md) gives the precise claims, the coverage and gap
ledger, and the next milestones. The [evaluator survey](docs/evaluators.md) fixes the
semantic anchor, and the [Foundation status](docs/compatibility.md) measures coverage.

## Building and validation

```bash
lake build PolyFunCryptol PolyFunCryptolTest polyfun-cryptol --wfail
lake exe polyfun-cryptol model run productive_stream
lake exe polyfun-cryptol model arx-native 32 8
./scripts/validate.sh --lint --test --axioms
```

`./scripts/validate.sh` builds and lints the case study and includes it in the
zero-debt axiom gate. `--test` builds its regressions and runs the offline model,
importer and module-canary checks. `--cryptol-external` also compares the model
with the pinned Cryptol 3.6.0 executable named by `CRYPTOL_BINARY` and, given the
exporter and Foundation, regenerates every committed export; see the
[tooling guide](docs/tooling.md). Validation never downloads or installs Cryptol.
[NOTICE.md](NOTICE.md) lists the third-party material.

## Scope and trust

The official parser, renamer, typechecker and module loader, together with the
typed-AST serializer, are external assumptions. Lean checks the exact exported
artifact it receives. Retyping an export does not prove source fidelity. Candidate
transformations, such as the official specializer's output, are checked in Lean
before any certificate is reused.

The supported fragment is narrower than full Cryptol. Partial numeric types,
nominal types and `case`, record and sequence updates, multi-branch
comprehensions, modular and rational types, most `Cryptol::Reference` fallbacks,
and polymorphic operational adequacy remain open. Unsupported constructs fail
explicitly. They are never replaced by default or bottom meanings. General recursion is a
least fixed point in the object semantics, and no axiom is added for it.
