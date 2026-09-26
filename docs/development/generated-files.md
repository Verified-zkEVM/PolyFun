# Generated and Derived Files

Edit the source of truth, not the output.

| Path | What it is | Edit directly? | Source of truth / refresh path |
| --- | --- | --- | --- |
| `CLAUDE.md` | compatibility symlink | No | Edit `AGENTS.md` |
| `PolyFun.lean` | generated module with umbrella public imports | No | `./scripts/update-lib.sh` or `./scripts/check-imports.sh` |
| `ToCslib.lean` | generated umbrella for the staging library | No | `./scripts/update-lib.sh ToCslib` or `./scripts/check-imports.sh` |
| `ComplexityBackends.lean` | generated umbrella for the optional backend library | No | `./scripts/update-lib.sh ComplexityBackends` or `./scripts/check-imports.sh` |
| `Examples/Parliament.lean` | generated case-study umbrella | No | `./scripts/update-lib.sh Examples.Parliament` |
| `PolyFunTest/Downstream/Surface.lean` | generated downstream-surface canary | No | edit `scripts/downstream-surface.json`, then `python3 scripts/downstream-surface.py check --fix`; rescan consumers with `python3 scripts/downstream-surface.py refresh --vcvio ../VCVio --arklib ../ArkLib` |
| `.lake/` | build artifacts and cache | No | `lake build`, `lake exe cache get` |
| `lake-manifest.json` | resolved dependency lockfile | Manual edits unsafe | Update `lean-toolchain` and both dependency pins in `lakefile.toml`, then run `lake update` |

## Important Notes

- `./scripts/update-lib.sh [ToCslib|ComplexityBackends]` only uses tracked
  `<Lib>/**/*.lean` files and fails fast if untracked Lean files would be
  skipped. Stage new files first, then rerun. It emits a `module` command
  followed by sorted `public import` commands so importing `PolyFun` re-exports
  the library API. `ToCslib.lean` and `ComplexityBackends.lean` are Lake library
  roots in their own right, so the generator wraps their import lists in the
  standard file header and the library's module docstring (both fixed text
  inside the script; edit them there, not in the output), which
  `check-docs-integrity.py` requires of every umbrella except `PolyFun.lean`. An import of a
  module that declares `deprecated_module` receives the suffix `-- deprecated_module: ignore`,
  so the umbrella builds without deprecation warnings while ordinary consumers still see them;
  see [compatibility](compatibility.md).
- `./scripts/check-imports.sh` regenerates each umbrella, compares it with a
  temporary backup, and restores the original. It reports any difference
  without retaining the regenerated output.
- `./scripts/check-docs-integrity.py` validates the CLAUDE.md symlink,
  resolves internal Markdown paths and heading anchors across tracked docs,
  `Examples/`, and the consumer fixture. It checks repository-rooted Lean
  paths, README excerpts against their checked source, and module docstrings
  across production, tutorials, tests, and the separate consumer. Its regression
  fixtures live in `./scripts/test-docs-integrity.py`; the validation wrapper
  and CI run both scripts. Run them after any documentation or Lean-module
  rename, move, addition, or deletion. CI runs this via
  [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml).
- If a path looks derived, confirm its source of truth before editing it.
- The documentation itself is *not* generated. Keep it maintained with source changes;
  see [`README.md`](../README.md) for the maintenance contract.

The `Examples.Parliament` generator argument maps to the nested
`Examples/Parliament` source directory. Its public import index receives the same
tracked-source coverage check as the production roots. Tutorials remain glob-based
and do not need an umbrella. Documentation checks include both consumer packages
and the executable entry point, while excluding their `.lake` build artifacts.
