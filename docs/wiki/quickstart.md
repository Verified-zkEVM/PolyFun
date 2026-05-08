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
local validation. By default it runs `lake build` followed by
`./scripts/check-imports.sh`.

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
  pull requests.
- [`../../.github/workflows/linting.yml`](../../.github/workflows/linting.yml):
  runs `./scripts/lint-style.sh` (Mathlib-derived style linter).
- [`../../.github/workflows/check-imports.yml`](../../.github/workflows/check-imports.yml):
  checks that `PolyFun.lean` matches the tracked source tree.
- [`../../.github/workflows/release-tag.yml`](../../.github/workflows/release-tag.yml),
  [`../../.github/workflows/update.yml`](../../.github/workflows/update.yml),
  [`../../.github/workflows/summary.yml`](../../.github/workflows/summary.yml),
  [`../../.github/workflows/review.yml`](../../.github/workflows/review.yml):
  release tagging, dependency-update PRs, summary stats, and review-helper
  workflows ported from
  [`Verified-zkEVM/ArkLib`](https://github.com/Verified-zkEVM/ArkLib).

## Toolchain

Lean toolchain and Mathlib stay in sync. Both currently `v4.29.0`. When
upgrading, update [`lean-toolchain`](../../lean-toolchain) and the
`require mathlib` line in [`lakefile.toml`](../../lakefile.toml)
simultaneously.

## Ongoing Port from VCV-io

PolyFun is being seeded from
[`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io). The
current port plan, file inventory, and risk register live in
[`../../PORTING-PLAN.md`](../../PORTING-PLAN.md). Two repo-local helpers
support follow-up resyncs:

- [`../../scripts/port-from-vcvio.sh`](../../scripts/port-from-vcvio.sh):
  wholesale copy of in-scope files from a VCV-io worktree.
- [`../../scripts/rename-namespaces.sh`](../../scripts/rename-namespaces.sh):
  bulk `ToMathlib.*` / `VCVio.Interaction.*` to `PolyFun.*` namespace
  rename.

These are intended for one-shot or rare resync use, not for routine
development. Most contributions should never need to invoke them.
