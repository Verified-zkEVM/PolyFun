# Validation

## Python tooling

Install [uv](https://docs.astral.sh/uv/getting-started/installation/) for
all repository Python entry points, including validation scripts and CI.
CI uses uv 0.13.6. The uv commands below select Python
3.12; uv downloads it if needed. Run them from the repository root.
These checks use only the standard library. `--no-project` runs them without
installing a Python package or creating a project environment.

## Full validation

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
| Default build | `PolyFun`, `ToCslib`, `ComplexityBackends`, `PolyFunIO`, `PolyFunExamples`, and `+PolyFunParliamentMain`, with `--wfail` |
| Module policy | Module mode, explicit Interaction API, no production imports of examples/tests/executables, `Std.WP` quarantine, library layering (`ToCslib` imports neither `PolyFun` nor a backend, and `PolyFun` imports no backend), `import all` boundaries (tests may open backends, backends never open `PolyFun` or `ToCslib`, module canaries open nothing) |
| Generated imports | Generated umbrellas match the tracked source tree |
| Documentation | Checker regressions, agent symlink, local paths and heading anchors, module docstrings, README excerpt synchronization |
| `--lint` | Batteries environment linters and Mathlib text-style checks over production and example libraries plus the executable entry point |
| `--test` | `PolyFunTest` with warnings and printed output fatal (`--wfail --iofail`), `lake test`, native CLI/filesystem tests, and both separate consumers |
| `--axioms` | Axiom-sweep fixture matrix and zero-debt check over production, tutorial, case-study, and executable module roots |

The committed axiom baseline is a zero-debt policy, not an allowlist. Both
arrays stay empty. `--update-baseline` refuses to record taint and is only
useful after removing all debt. Do not introduce `sorry`, `admit`, or
non-standard axioms to finished work.

The report written with `lake exe polyfun-axiomsweep --out FILE` also carries
`sorryGraph`. It lists every declaration in the `sorryAx` closure, internal
auxiliaries included. Each entry gives the kind, the elaborated statement, whether
the declaration uses `sorryAx` directly, and its tainted kernel dependencies.
Downstream projects read the graph to trace inherited proof obligations. PolyFun's
own `--check` still rejects any such declaration.

## New or moved source files

Stage additions, deletions, and renames before generating the relevant umbrella:

```bash
git add PolyFun ToCslib ComplexityBackends
./scripts/update-lib.sh
./scripts/update-lib.sh ToCslib
./scripts/update-lib.sh ComplexityBackends
./scripts/validate.sh --lint --test --axioms
```

The generator reads tracked paths and rejects untracked source files. Never
edit generated umbrellas by hand. Tutorial and test libraries use glob targets,
so they have no generated umbrella. The Parliament case study uses
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
uv run --no-project --python 3.12 python scripts/test-parliament-cli.py
lake -d test/ParliamentConsumer build --wfail
lake exe runLinter PolyFun   # once for each root in lintDriverArgs
lake exe lint-style PolyFun ToCslib ComplexityBackends \
  Examples.Tutorials.Requests Examples.Tutorials.Machines Examples.Tutorials.IndexedPrograms \
  Examples.Tutorials.InteractionTrees \
  Examples.Parliament PolyFunParliamentMain
uv run --no-project --python 3.12 python ./scripts/test-docs-integrity.py
uv run --no-project --python 3.12 python ./scripts/check-docs-integrity.py
```

Build the relevant libraries before running environment linters, and run them
one root per process. Use `lake exe runLinter --trace <root>` to see which checks
actually run. `checkUnivs` runs during elaboration. Text-style linting is a
separate check. The test library is not a lint root. See [lint policy](linting.md).

The [documentation consumer](../../test/DocumentationConsumer/README.md) and
`test/ParliamentConsumer` depend on PolyFun as separate packages and use ordinary
imports. They share the root's dependency cache and pins. These separate packages catch missing public
equations that an internal `import all` test could conceal.

When changing the README example, update both its fenced block and the named
region in [Requests.lean](../../Examples/Tutorials/Requests.lean). The checker
compares imports plus the region body. `lake build PolyFunExamples` elaborates
the source and its result proofs.

## CI mapping

- [CI](../../.github/workflows/ci.yml): three parallel jobs, including
  merge-queue candidates:
  - `build` runs the wrapper with `--axioms`.
  - `Lint (environment linters)` builds the production and example libraries
    with `--wfail` and runs Batteries' `runLinter` once per `lintDriverArgs` root.
  - `Test` builds `PolyFunTest` with `--wfail --iofail` and runs `lake test`,
    the CLI tests and both consumers.

  Every job restores two caches, each from the newest `main` entry for the same toolchain and
  manifest. One holds the dependencies. The other holds PolyFun's own `.lake/build`. Each job
  therefore rebuilds only what the checkout changed. Only `build` on `main` saves the caches. Before
  it saves, it also builds `PolyFunTest`, `polyfun-parliament` and Batteries' `runLinter`, which only
  the other jobs use. That build only fills the caches: the other jobs report its failures, and a
  failure in it still saves what did build. It saves the build cache on every run. It saves the
  dependency cache when the list of dependency build outputs changes: new pins, or a PolyFun import
  that first reaches a dependency module. New pins start the dependency cache empty, so the old pins'
  outputs do not accumulate in it. A newer push to `main` waits for the running job rather than
  cancelling its save. A nightly clean build of `main` skips the build cache, so nothing passes only
  because of it.
- [Import check](../../.github/workflows/check-imports.yml): generated imports.
- [Docs integrity](../../.github/workflows/docs-integrity.yml): checker tests,
  links, anchors, excerpts and module docs.
- [Text lint](../../.github/workflows/linting.yml): source style for production
  and tutorial libraries.
- [API docs](../../.github/workflows/docs.yml): generated source documentation
  published on pushes to `main`. Its Lean action builds the documented roots and
  leaves the tests and environment lint to CI. The CI lint job runs the linters
  with one root per process; [lint policy](linting.md#commands-and-coverage)
  explains why.
- [Frontier](../../.github/workflows/frontier.yml): builds the nested `PolyFunFrontier`
  package on cslib-frontier's toolchain, checks its pins against cslib-frontier's
  (`PolyFunFrontier/scripts/check-pins.py`) and runs the axiom sweep over it. It runs when
  `PolyFunFrontier/` or PolyFun's library changes, as a separate workflow, so a cslib-frontier
  change never blocks PolyFun's own checks.
- [Writing](../../.github/workflows/writing.yml): tests for the writing checker,
  and [writing suggestions](write-technical-prose.md#use-the-checker) for the
  changed prose and the PR description. The suggestions are warnings and do not
  fail the job.

All required jobs must pass on the revision under review. Retargeted or
restacked PRs need fresh checks, including intermediate base branches. A
style-only result does not cover compilation or proof validation.

## Toolchain updates

Lean, Mathlib and CSLib stay in sync. Update `lean-toolchain`, both consumers'
matching `lean-toolchain`, and both dependency pins in `lakefile.toml`, then
run `lake update` and the full suite. Keep the root manifest committed and
review the resolved versions. Consumer manifests are local artifacts that Lake regenerates.
Both consumers resolve into the root's package cache
(`packagesDir = "../../.lake/packages"`). Their ignored `lake-manifest.json` and
`.lake/` stay on disk between runs, so a stale consumer manifest checks the
root's packages out at its old revisions. A worktree whose `.lake/packages` is a
symlink passes the damage to the checkout it points at. Before validating a
toolchain or manifest change, run `rm -f test/*/lake-manifest.json` and
`rm -rf test/*/.lake`. If a build then fails inside a dependency, compare
`git -C .lake/packages/<pkg> rev-parse HEAD` with the root manifest's pin and
check the pin out (`git -C .lake/packages/<pkg> checkout --detach <rev>`) before
rebuilding. Never build the consumers on two toolchains against one cache.
Compatibility tests for existing deprecated APIs should assert their expected
diagnostics with strict `#guard_msgs` rather than suppressing warnings.

`PolyFunFrontier/` does not follow these pins: it uses cslib-frontier's toolchain and CSLib and
Mathlib commits, which `PolyFunFrontier/scripts/bump.sh` moves together. Build it in its own
worktree, since its build of PolyFun lands in the root's `.lake/build` on the other toolchain.

Pin a release candidate like a stable version, with its `-rcN` tag wherever
the version appears. When a change to `lean-toolchain` reaches `main`,
the [release-tag workflow](../../.github/workflows/release-tag.yml) creates the
matching PolyFun release tag.

Acknowledging an experimental feature with `set_option experimental.vcgen true`
is not a linter suppression. `PolyFunTest/Do/Algebra.lean` pins the warning that
`vcgen` prints without that option, so a change to its text fails the test.
