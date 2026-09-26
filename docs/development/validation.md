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
| Default build | `PolyFun`, `ToCslib`, `ComplexityBackends`, `PolyFunExamples`, and `+PolyFunParliamentMain`, with `--wfail` |
| Module policy | Module mode, explicit Interaction API, no production imports of examples/tests/executables, `Std.Do` quarantine, library layering (`ToCslib` imports neither `PolyFun` nor a backend; `PolyFun` imports no backend), `import all` boundaries (tests may open backends, backends never open `PolyFun` or `ToCslib`, module canaries open nothing) |
| Generated imports | Generated umbrellas match the tracked source tree |
| Downstream surface | `PolyFunTest/Downstream/Surface.lean` matches `scripts/downstream-surface.json`, the modules and declarations VCVio and ArkLib consume; the test build then checks they still exist |
| Documentation | Checker regressions, agent symlink, local paths and heading anchors, module docstrings, README excerpt synchronization |
| `--lint` | Batteries environment linters and Mathlib text-style checks over production and example libraries plus the executable entry point |
| `--test` | `PolyFunTest` with warnings fatal, `lake test`, native CLI/filesystem tests, and both separate consumers |
| `--axioms` | Axiom-sweep fixture matrix and zero-debt check over production, tutorial, case-study, and executable module roots |

The committed axiom baseline is a zero-debt policy, not an allowlist. Both
arrays stay empty. `--update-baseline` refuses to record taint and is only
useful after removing all debt. Do not introduce `sorry`, `admit`, or
non-standard axioms to finished work.

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
edit generated umbrellas by hand. When a production module moves, leave a
`deprecated_module` shim at the old path and record it in
[compatibility](compatibility.md); the generator marks the umbrella's import
of a shim so warning-fatal builds stay green. Tutorial and test libraries use glob targets;
they have no generated umbrella. The Parliament case study uses
`./scripts/update-lib.sh Examples.Parliament`. Add new tutorial modules to the explicit
environment-lint, text-lint, and axiom-sweep module lists in `lakefile.toml`,
`scripts/validate.sh`, and the text-lint workflow. See [generated files](generated-files.md).

## Focused commands

```bash
lake build PolyFunExamples --wfail
lake build PolyFunTest --wfail
lake test
lake -d test/DocumentationConsumer build --wfail
lake build polyfun-parliament --wfail
python3 scripts/test-parliament-cli.py
lake -d test/ParliamentConsumer build --wfail
lake lint
lake exe lint-style PolyFun ToCslib ComplexityBackends \
  Examples.Tutorials.Requests Examples.Tutorials.Machines Examples.Tutorials.IndexedPrograms \
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

- [CI](../../.github/workflows/ci.yml): independent build/axiom, environment
  lint, and test/consumer jobs, including merge-queue candidates.
- [Import check](../../.github/workflows/check-imports.yml): generated imports.
- [Docs integrity](../../.github/workflows/docs-integrity.yml): checker tests,
  links, anchors, excerpts and module docs.
- [Text lint](../../.github/workflows/linting.yml): source style for production
  and tutorial libraries.
- [API docs](../../.github/workflows/docs.yml): generated source documentation
  published on pushes to `main`. The Lean action also runs tests and environment
  lint, so its explicit build targets must cover every root in `lintDriverArgs`,
  including the executable entry point. Keep those targets in sync when adding
  lint roots; the default `lake build` target alone does not cover them.

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
