# Generated and Derived Files

Edit the source of truth, not the output.

| Path | What it is | Edit directly? | Source of truth / refresh path |
| --- | --- | --- | --- |
| `CLAUDE.md` | compatibility symlink | No | Edit `AGENTS.md` |
| `PolyFun.lean` | generated umbrella imports | No | `./scripts/update-lib.sh` or `./scripts/check-imports.sh` |
| `.lake/` | build artifacts and cache | No | `lake build`, `lake exe cache get` |
| `lake-manifest.json` | resolved dependency lockfile | Manual edits unsafe | `lake update` (or the `update.yml` workflow) |

## Important Notes

- `./scripts/update-lib.sh` only uses tracked `PolyFun/**/*.lean` files and
  fails fast if untracked Lean files would be skipped. Stage new files
  first, then rerun.
- `./scripts/check-imports.sh` is the lightweight read-only check used in
  CI: it regenerates `PolyFun.lean` to a temp file and diffs against the
  committed copy.
- `./scripts/check-docs-integrity.py` validates the CLAUDE.md symlink and
  resolves all internal markdown links in tracked top-level docs and
  `docs/`. Run it (or `./scripts/validate.sh`, which calls it) after any
  doc rename, move, or deletion. CI runs this via
  [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml).
- If a path looks derived, confirm its source of truth before editing it.
- The wiki itself is *not* generated. Keep it maintained with source changes;
  see [`README.md`](README.md) for the maintenance contract.
