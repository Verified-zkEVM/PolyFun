# Validation

Fetch precompiled dependencies on a fresh checkout, then run the full suite:

```bash
lake exe cache get
./scripts/validate.sh --lint --test --axioms
```

For routine local feedback, `./scripts/validate.sh` runs the required build,
module, import, and documentation checks. Add the flags when changing APIs,
proofs, examples, import boundaries, or validation infrastructure.

## What the wrapper checks

| Check | Scope |
|---|---|
| Default build | `PolyFun`, `ToCslib`, `ComplexityBackends`, `PolyFunCryptol`, `PolyFunExamples`, `+PolyFunParliamentMain`, and `+PolyFunCryptolMain`, with `--wfail` |
| Module policy | Module mode, explicit Interaction API, no production imports of examples/tests/executables, `Std.WP` quarantine, library layering (`ToCslib` imports neither `PolyFun` nor a backend; `PolyFun` imports no backend; nothing below `PolyFunCryptol` imports it), `import all` boundaries (tests may open backends, backends and the Cryptol case study never open `PolyFun` or `ToCslib`, only the case study and its tests open it, module canaries open nothing) |
| Generated imports | Generated umbrellas match the tracked source tree |
| Documentation | Checker regressions, agent symlink, local paths and heading anchors, module docstrings, README excerpt synchronization |
| `--lint` | Batteries environment linters and Mathlib text-style checks over production and example libraries plus the executable entry point |
| `--test` | `PolyFunTest` with warnings and printed output fatal (`--wfail --iofail`), `lake test`, native CLI/filesystem tests, both separate consumers, `PolyFunCryptolTest`, and the offline Cryptol model fixtures |
| `--cryptol-external` | `--test` plus a comparison of the Cryptol model with the pinned Cryptol 3.6.0 executable named by `CRYPTOL_BINARY` |
| `--axioms` | Axiom-sweep fixture matrix and zero-debt check over production, tutorial, case-study, and executable module roots |

The committed axiom baseline is a zero-debt policy, not an allowlist. Both
arrays stay empty. `--update-baseline` refuses to record taint and is only
useful after removing all debt. Do not introduce `sorry`, `admit`, or
non-standard axioms to finished work.

The report written with `lake exe polyfun-axiomsweep --out FILE` also carries
`sorryGraph`: every declaration in the `sorryAx` closure, with its kind, its
elaborated statement, whether it uses `sorryAx` directly, and its tainted kernel
dependencies, internal auxiliaries included. Downstream projects read it to
trace inherited proof obligations; PolyFun's own `--check` still rejects them.

## New or moved source files

Stage additions, deletions, and renames before generating the relevant umbrella:

```bash
git add PolyFun ToCslib ComplexityBackends PolyFunCryptol
./scripts/update-lib.sh
./scripts/update-lib.sh ToCslib
./scripts/update-lib.sh ComplexityBackends
./scripts/update-lib.sh PolyFunCryptol
./scripts/validate.sh --lint --test --axioms
```

The generator reads tracked paths and rejects untracked source files. Never
edit generated umbrellas by hand. Tutorial and test libraries use glob targets;
they have no generated umbrella. The Parliament case study uses
`./scripts/update-lib.sh Examples.Parliament`. Add new tutorial modules to the explicit
environment-lint, text-lint, and axiom-sweep module lists in `lakefile.toml`,
`scripts/validate.sh`, and the text-lint workflow. See [generated files](generated-files.md).

## Focused commands

```bash
lake build PolyFunExamples --wfail
lake build PolyFunTest --wfail --iofail
lake test
lake -d test/DocumentationConsumer build --wfail
lake build polyfun-parliament --wfail
python3 scripts/test-parliament-cli.py
lake -d test/ParliamentConsumer build --wfail
lake build PolyFunCryptolTest polyfun-cryptol --wfail --iofail
python3 PolyFunCryptol/scripts/test_model.py
lake lint
lake exe lint-style PolyFun ToCslib ComplexityBackends \
  Examples.Tutorials.Requests Examples.Tutorials.Machines Examples.Tutorials.IndexedPrograms \
  Examples.Tutorials.InteractionTrees \
  Examples.Parliament PolyFunParliamentMain
python3 scripts/test-docs-integrity.py
python3 scripts/check-docs-integrity.py
```

Build the relevant libraries before running environment linters. Use
`lake lint -- --trace` to see which checks actually run. `checkUnivs` runs
during elaboration; text-style linting is a separate check. The test library
is outside `lake lint` scope. See [lint policy](linting.md).

The [documentation consumer](../../test/DocumentationConsumer/README.md) and
`test/ParliamentConsumer` depend on PolyFun as separate packages and use ordinary
imports. They share the root's dependency cache and pins. This catches missing public equations that an
internal `import all` test could conceal.

When changing the README example, update both its fenced block and the named
region in [Requests.lean](../../Examples/Tutorials/Requests.lean). The checker
compares imports plus the region body; `lake build PolyFunExamples` elaborates
the source and its result proofs.

## CI mapping

- [CI](../../.github/workflows/ci.yml): three parallel jobs, including
  merge-queue candidates:
  - `build` runs the wrapper with `--axioms`;
  - `Lint (environment linters)` builds the production and example libraries
    with `--wfail` and runs `lake lint`;
  - `Test` builds `PolyFunTest` with `--wfail --iofail` and runs `lake test`,
    the CLI tests and both consumers.

  Every job restores two caches: dependencies keyed on the toolchain and
  manifest, and PolyFun's own `.lake/build` keyed per commit and restored from
  the newest `main` build. Each job therefore rebuilds only what the checkout
  changed. Only `build` on `main` saves the caches, and a newer push to `main`
  waits for the running job rather than cancelling its save. A nightly clean
  build of `main` skips the build cache, so nothing passes only because of it.
- [Import check](../../.github/workflows/check-imports.yml): generated imports.
- [Docs integrity](../../.github/workflows/docs-integrity.yml): checker tests,
  links, anchors, excerpts and module docs.
- [Text lint](../../.github/workflows/linting.yml): source style for production
  and tutorial libraries.
- [API docs](../../.github/workflows/docs.yml): generated source documentation
  published on pushes to `main`. Its Lean action builds the documented roots and
  leaves the tests and environment lint to CI: a single `lake lint` process over
  every root needs about 7 GB, which shuts the hosted runner down, so the linters
  run one root per process in the CI lint job.

All required jobs must pass on the revision under review. Retargeted or
restacked PRs need fresh checks, including intermediate base branches. A
style-only result does not cover compilation or proof validation.

## Toolchain updates

Lean, Mathlib and CSLib stay in sync. Update `lean-toolchain`, both consumers'
matching `lean-toolchain`, and both dependency pins in `lakefile.toml`, then
run `lake update` and the full suite. Keep the root manifest committed and
review the resolved versions. Consumer manifests are regenerated locally.
Compatibility tests for existing deprecated APIs should assert their expected
diagnostics with strict `#guard_msgs` rather than suppressing warnings.

A release candidate is pinned like a stable version, with its `-rcN` tag
wherever the version appears. When a change to `lean-toolchain` reaches `main`,
the [release-tag workflow](../../.github/workflows/release-tag.yml) creates the
matching PolyFun release tag.

Acknowledging an experimental feature with `set_option experimental.vcgen true`
is not a linter suppression. `PolyFunTest/Do/Algebra.lean` pins the warning that
`vcgen` prints without that option, so a change to its text fails the test.
