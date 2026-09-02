# Quickstart

This page is the recommended agent playbook for commands and validation.
Use it as the main guide for routine local checks.

## Recommended Validation

For a convenient routine check, run:

```bash
./scripts/validate.sh
```

On a cold clone, fetch precompiled dependencies first:

```bash
lake exe cache get
./scripts/validate.sh
```

`./scripts/validate.sh` is the recommended convenience wrapper for routine
local validation. By default it runs:

1. `lake build --wfail` (warnings — including `mathlibStandardSet` style
   warnings — are hard failures, matching CI)
2. `./scripts/check-modules.sh` (all Lean sources use module mode and the
   Interaction public-scope policy is respected)
3. `./scripts/check-imports.sh` (umbrella `PolyFun.lean` matches the
   tracked source tree)
4. `python3 ./scripts/test-docs-integrity.py` and
   `python3 ./scripts/check-docs-integrity.py` (checker regression fixtures,
   CLAUDE.md symlink, tracked-markdown links, repository-rooted Lean paths,
   and module docstrings in their standard prologue position)

## Validation By Change Type

### Existing Lean files only

```bash
./scripts/validate.sh
```

### Added, renamed, or deleted files under `PolyFun/`

```bash
git add path/to/newfile.lean
./scripts/validate.sh
```

`./scripts/update-lib.sh` only considers tracked files, and fails fast if
untracked `PolyFun/**/*.lean` files are present.

### Lean-heavy refactors or cleanup

```bash
./scripts/validate.sh --lint --test
```

`--lint` adds `lake lint` (Batteries' environment linters: `docBlame`,
`simpNF`, `checkUnivs`, …) to the convenience wrapper. `--test` adds
`lake test` (builds the `PolyFunTest` library). `--axioms` adds
the executable fixture matrix and `lake exe polyfun-axiomsweep --check`. The check scans
every imported `PolyFun.*` declaration and fails on any `sorryAx` or non-standard
axiom dependency. The committed `scripts/axiom_baseline.json` is a zero-debt
policy, not an allowlist: both arrays must remain empty. Update mode refuses to
record taint and is only useful for resetting a stale baseline after all debt is
removed. The main CI `build` job runs `validate.sh --axioms`, so a taint finding
fails CI. Separate `lint` and `test` CI jobs run
`lake lint` / `lake test`, and the `linting.yml` workflow runs the text style
lint, so treat all three as required for merge. Text style (copyright headers,
line length, module docstrings) is additionally enforced at build time by the
`mathlibStandardSet` linters.

## Optional Direct Commands

You can still run the underlying pieces directly when debugging a specific
issue:

```bash
lake build
./scripts/check-modules.sh
./scripts/check-imports.sh
python3 ./scripts/test-docs-integrity.py
python3 ./scripts/check-docs-integrity.py
```

If you specifically need to regenerate `PolyFun.lean`, use:

```bash
./scripts/update-lib.sh
```

To run the environment linters or the test library on their own:

```bash
lake lint   # Batteries runLinter over all production libraries
lake test   # builds the PolyFunTest library (worked examples / regression tests)
```

`lake lint` and `lake test` are wired in [`lakefile.toml`](../../lakefile.toml)
via `lintDriver = "batteries/runLinter"` (with the production library roots in
`lintDriverArgs`)
and `testDriver = "PolyFunTest"`. The `PolyFunTest` library is glob-based
(`PolyFunTest.+`), holds the worked examples and notation smoke tests, and is
deliberately outside the `lake lint` scope.

## CI Mapping

- [`../../.github/workflows/ci.yml`](../../.github/workflows/ci.yml): runs
  three independent jobs on every push to `main` and on pull requests — a
  `build` job (`./scripts/validate.sh`, which includes
  `lake build --wfail`), a `lint` job (`lake lint`, the environment linters),
  and a `test` job (`lake test`, the
  `PolyFunTest` library). All builds pass `--wfail`, so any compiler or
  `mathlibStandardSet` warning fails CI rather than slipping through. The
  `build` job is a required status check on `main`.
- [`../../.github/workflows/check-imports.yml`](../../.github/workflows/check-imports.yml):
  checks that `PolyFun.lean` matches the tracked source tree. `Check
  Library File Imports` is a required status check on `main`.
- [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml):
  runs the checker's regression fixtures and `./scripts/check-docs-integrity.py`
  (CLAUDE.md symlink, tracked markdown links, repository-rooted Lean paths,
  and module docstrings). `Check Docs Integrity` is a required status check
  on `main`. This is the agent-documentation liveness check: any PR that
  breaks an internal link or documented Lean path in `AGENTS.md`, `README.md`,
  `CONTRIBUTING.md`, `REFERENCES.md`, or a tracked page under `docs/`, or drops
  a production/test module docstring from its prologue, will fail this job.
- [`../../.github/workflows/linting.yml`](../../.github/workflows/linting.yml):
  runs the community `leanprover-community/lint-style-action` (the Lean-based
  Mathlib text style linter: copyright headers, line length, module
  docstrings).
- [`../../.github/workflows/docs.yml`](../../.github/workflows/docs.yml):
  builds and publishes searchable API documentation from `main`.
- [`../../.github/workflows/release-tag.yml`](../../.github/workflows/release-tag.yml)
  and [`../../.github/workflows/review.yml`](../../.github/workflows/review.yml):
  release tagging and review helper workflows ported from
  [`Verified-zkEVM/ArkLib`](https://github.com/Verified-zkEVM/ArkLib).

## Toolchain

Lean, Mathlib, and cslib stay in sync. To upgrade them, update
[`lean-toolchain`](../../lean-toolchain) and both dependency pins in
[`lakefile.toml`](../../lakefile.toml). Then run `lake update` and validate the
result before opening a pull request.
