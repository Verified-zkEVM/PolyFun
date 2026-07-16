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
2. `./scripts/check-imports.sh` (umbrella `PolyFun.lean` matches the
   tracked source tree)
3. `python3 ./scripts/check-docs-integrity.py` (CLAUDE.md symlink and
   tracked-markdown link resolution)

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
`lake test` (builds the `PolyFunTest` library). The main CI `build` job runs
`validate.sh` without these flags, but separate `lint` and `test` CI jobs run
`lake lint` / `lake test`, and the `linting.yml` workflow runs the text style
lint, so treat all three as required for merge. Text style (copyright headers,
line length, module docstrings) is additionally enforced at build time by the
`mathlibStandardSet` linters.

## Optional Direct Commands

You can still run the underlying pieces directly when debugging a specific
issue:

```bash
lake build
./scripts/check-imports.sh
python3 ./scripts/check-docs-integrity.py
```

If you specifically need to regenerate `PolyFun.lean`, use:

```bash
./scripts/update-lib.sh
```

To run the environment linters or the test library on their own:

```bash
lake lint   # Batteries runLinter over the PolyFun library
lake test   # builds the PolyFunTest library (worked examples / regression tests)
```

`lake lint` and `lake test` are wired in [`lakefile.toml`](../../lakefile.toml)
via `lintDriver = "batteries/runLinter"` (with `lintDriverArgs = ["PolyFun"]`)
and `testDriver = "PolyFunTest"`. The `PolyFunTest` library is glob-based
(`PolyFunTest.+`), holds the worked examples and notation smoke tests, and is
deliberately outside the `lake lint` scope.

## CI Mapping

- [`../../.github/workflows/ci.yml`](../../.github/workflows/ci.yml): runs
  three independent jobs on every push to `main` and on pull requests — a
  `build` job (`lake build --wfail` + `./scripts/validate.sh`), a `lint` job
  (`lake lint`, the environment linters), and a `test` job (`lake test`, the
  `PolyFunTest` library). All builds pass `--wfail`, so any compiler or
  `mathlibStandardSet` warning fails CI rather than slipping through. The
  `build` job is a required status check on `main`.
- [`../../.github/workflows/check-imports.yml`](../../.github/workflows/check-imports.yml):
  checks that `PolyFun.lean` matches the tracked source tree. `Check
  Library File Imports` is a required status check on `main`.
- [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml):
  runs `./scripts/check-docs-integrity.py` (CLAUDE.md symlink, tracked
  markdown link resolution). `Check Docs Integrity` is a required status
  check on `main`. This is the agent-documentation liveness check: any
  PR that breaks an internal link in `AGENTS.md`, `README.md`,
  `CONTRIBUTING.md`, `REFERENCES.md`, or any tracked page under `docs/`
  will fail this job.
- [`../../.github/workflows/linting.yml`](../../.github/workflows/linting.yml):
  runs the community `leanprover-community/lint-style-action` (the Lean-based
  Mathlib text style linter: copyright headers, line length, module
  docstrings).
- [`../../.github/workflows/summary.yml`](../../.github/workflows/summary.yml):
  optional AI-generated PR summary; gated on `GEMINI_API_KEY` repository
  secret. Skipped (with a notice) if the secret is not set.
- [`../../.github/workflows/release-tag.yml`](../../.github/workflows/release-tag.yml),
  [`../../.github/workflows/update.yml`](../../.github/workflows/update.yml),
  [`../../.github/workflows/review.yml`](../../.github/workflows/review.yml):
  release tagging, dependency-update PRs, and review-helper workflows
  ported from
  [`Verified-zkEVM/ArkLib`](https://github.com/Verified-zkEVM/ArkLib).

## Toolchain

Lean toolchain, Mathlib, and cslib stay in sync. All currently `v4.32.0`. When
upgrading, update [`lean-toolchain`](../../lean-toolchain) and the
`require mathlib` / `require cslib` pins in
[`lakefile.toml`](../../lakefile.toml) simultaneously.
