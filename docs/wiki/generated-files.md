# Generated and Derived Files

Edit the source of truth, not the output.

| Path | What it is | Edit directly? | Source of truth / refresh path |
| --- | --- | --- | --- |
| `CLAUDE.md` | compatibility symlink | No | Edit `AGENTS.md` |
| `PolyFun.lean` | generated module with umbrella public imports | No | `./scripts/update-lib.sh` or `./scripts/check-imports.sh` |
| `ToCslib.lean` | generated umbrella for the staging library | No | `./scripts/update-lib.sh ToCslib` or `./scripts/check-imports.sh` |
| `.lake/` | build artifacts and cache | No | `lake build`, `lake exe cache get` |
| `lake-manifest.json` | resolved dependency lockfile | Manual edits unsafe | Update `lean-toolchain` and both dependency pins in `lakefile.toml`, then run `lake update` |

## Important Notes

- `./scripts/update-lib.sh [ToCslib]` only uses tracked `PolyFun/**/*.lean` (or
  `ToCslib/**/*.lean`) files and
  fails fast if untracked Lean files would be skipped. Stage new files
  first, then rerun. It emits a `module` command followed by sorted
  `public import` commands so importing `PolyFun` re-exports the library API.
- `./scripts/check-imports.sh` is the lightweight read-only check used in
  CI: it regenerates `PolyFun.lean` to a temp file and diffs against the
  committed copy.
- `./scripts/check-docs-integrity.py` validates the CLAUDE.md symlink,
  resolves internal markdown links and repository-rooted Lean paths in tracked
  top-level docs and `docs/`, and checks that production/test Lean files keep a
  module docstring in the standard post-import prologue slot. Its regression
  fixtures live in `./scripts/test-docs-integrity.py`; the validation wrapper
  and CI run both scripts. Run them after any documentation or Lean-module
  rename, move, addition, or deletion. CI runs this via
  [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml).
- If a path looks derived, confirm its source of truth before editing it.
- The wiki itself is *not* generated. Keep it maintained with source changes;
  see [`README.md`](README.md) for the maintenance contract.
