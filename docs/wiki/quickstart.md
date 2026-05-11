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

1. `lake build`
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
./scripts/validate.sh --lint
```

This adds `./scripts/lint-style.sh` to the convenience wrapper. The main CI
build runs `validate.sh` without `--lint`, but a separate `linting.yml`
workflow runs the style lint, so treat lint passes as required for merge.

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

To run the style lint on its own:

```bash
./scripts/lint-style.sh
```

## CI Mapping

- [`../../.github/workflows/ci.yml`](../../.github/workflows/ci.yml): runs
  `lake build` and `./scripts/validate.sh` on every push to `main` and on
  pull requests. The `build` job is a required status check on `main`.
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
  runs `./scripts/lint-style.sh` (Mathlib-derived style linter).
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

Lean toolchain and Mathlib stay in sync. Both currently `v4.29.0`. When
upgrading, update [`lean-toolchain`](../../lean-toolchain) and the
`require mathlib` line in [`lakefile.toml`](../../lakefile.toml)
simultaneously.

## VCV-io Resync Helpers

PolyFun originated as a generic extraction from
[`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io). Two
repo-local helpers support follow-up resyncs:

- [`../../scripts/port-from-vcvio.sh`](../../scripts/port-from-vcvio.sh):
  wholesale copy of in-scope files from a VCV-io worktree.
- [`../../scripts/rename-namespaces.sh`](../../scripts/rename-namespaces.sh):
  bulk `ToMathlib.*` / `VCVio.Interaction.*` to `PolyFun.*` namespace
  rename.

These are intended for one-shot or rare resync use, not for routine
development. Most contributions should never need to invoke them.
