# Linter setup and exception maintenance

## Commands and coverage

```bash
lake exe cache get
lake build PolyFun ToCslib PolyFunTest --wfail
lake lint -- --trace
lake exe lint-style PolyFun ToCslib
python3 scripts/audit-linters.py
python3 scripts/audit-linters.py --json > /tmp/polyfun-linters.json
python3 scripts/audit-linters.py --extra docBlameThm --json > /tmp/polyfun-doc-trial.json
python3 scripts/test-linter-audit.py
python3 scripts/test-linter-coverage.py
```

The convenience command `./scripts/validate.sh --lint --test --axioms` runs
both production builds with warnings treated as failures, the environment
and text-style checks, the test library, and the existing integrity/axiom
gates. `PolyFunTest` is excluded from production environment linting; its
examples and compatibility checks are elaborated with warnings fatal.
The separate text-style CI job covers both production roots. Scripts and
synthetic fixtures are not production library roots.

The read-only audit uses the pinned Batteries checks, importing each root
separately as the runner does. It reports registration, active checks,
linter-set membership, raw findings, source options, and exception status.
It checks `@[nolint]` declarations directly to distinguish needed from stale
annotations. JSON exceptions are accounted for across the union of roots.
It refuses to audit dependency checkouts that differ from the manifest.
Run a fresh build first: neither an existing olean nor a successful audit
proves the sources are up to date.

`--check` fails on unsuppressed environment findings, stale annotations,
and duplicate, stale, or inactive-linter JSON entries. It is an opt-in
maintenance gate, not an exception generator. The Unicode inventory is a
source-presence/duplicate check for the currently used `ERR_UNICODE` format;
`lint-style` remains authoritative for whether a character is allowed.
Unrecognized text exception formats are reported, never silently discarded.

`--exported` is a diagnostic for ordinary-import visibility, **not** the
runner's environment. Batteries uses `importModules` at its default
`private` level, loading private bodies and documentation. Using the
`exported` or `server` level instead produces misleading missing-documentation
and type-check findings. The coverage fixtures exercise actual compiled
modules, including private declarations and repeated runs over warm artifacts.

## Pinned upstream comparison

Baseline: PolyFun `e4099b4`, Lean `v4.33.1`, Mathlib `0df444a360`,
cslib `98e395a701`, Batteries `4488d40d07`. Exact current revisions remain in
the manifest; the audit prints them on every run.

| Project | Build-time policy | Environment runner | Text / additional checks |
| --- | --- | --- | --- |
| PolyFun | Mathlib standard set; long files capped at 1500; Lean defaults; fatal build warnings | Batteries, explicitly `PolyFun` and `ToCslib` | Mathlib text lint; Unicode enabled with exceptions; module/import/docs/axiom gates |
| Mathlib | Standard set, explicit header check for its initialization layer, long-file cap 1500 | Batteries, explicitly `Mathlib` | Repository-specific Python/import/scripts checks; separate weekly and nightly sets |
| cslib | Mathlib standard set; explicit `flexible` setting already included in that set | Batteries, default production target | Unicode globally disabled; Mathlib-specific infrastructure checks disabled; separate weekly report |
| Batteries | Core defaults plus `missingDocs`; test target relaxes `missingDocs` | Its own runner, default targets | Its own CI/style conventions; no Mathlib dependency |
| Lean / Std | Core compiler/linter defaults and core build configuration | Lake also has a distinct built-in environment-linter registry | Core CMake enables warning failures; built-in lint is not a drop-in replacement for Batteries |

Sources: [Mathlib configuration](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/lakefile.lean),
[Mathlib sets](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Init.lean),
[cslib configuration](https://github.com/leanprover/cslib/blob/98e395a701f2027a413ad24729e1a11a6c772eb4/lakefile.toml),
[Batteries configuration](https://github.com/leanprover-community/batteries/blob/4488d40d070b9700d4d5a6aa342f0d40c31b2a2d/lakefile.toml),
[core build](https://github.com/leanprover/lean4/blob/v4.33.1/src/CMakeLists.txt),
[built-in lint](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/CLI/BuiltinLint.lean).

The baseline runtime trace runs the same 14 environment linters on both
production roots: `checkType`, `defsWithUnderscore`, `deprecatedNoSince`,
`docBlame`, `impossibleInstance`, `nonClassInstance`, `simpComm`, `simpNF`,
`structureInType`, `subsetDotNotationLinter`, `synTaut`, `tacticDocs`,
`unusedArguments`, and `unusedHavesSuffices`. The audit's registry also lists
disabled checks. A linter definition or an option in a Lake file alone does
not demonstrate registration or execution. Core's `checkUnivs`, for example,
is a build-time check, not one of these environment checks.

The initial runtime audit covered 15,342 PolyFun and 407 ToCslib declarations,
with no unsuppressed environment findings. There were 49 JSON entries for
inactive `topNamespace`, eight unused-argument annotations (seven stale),
40 scoped universe suppressions, nine deprecated-test suppressions, and
36 Unicode entries representing nine effective file/character exceptions.
These are baseline measurements, not fixed budgets or permission for new debt.

## Exception policy and upstream work

Keep the upstream runner and standard set. Do not enable every optional
check: trial a category, assess applicability, and land fixes and enforcement
together. The Mathlib weekly/nightly sets remain diagnostic candidates;
they are not missing mandatory production checks. A baseline trial of both
registered optional environment checks found 2,270 `docBlameThm` findings
(2,249 PolyFun; 21 ToCslib) and 149 `explicitVarsOfIff` findings (all PolyFun).
They remain optional, matching upstream: documenting every theorem is a
separate editorial campaign, and changing iff binders would alter public
call sites. Use `--extra` to reproduce the trial without changing enforcement.

The pinned [cslib namespace linter](https://github.com/leanprover/cslib/blob/98e395a701f2027a413ad24729e1a11a6c772eb4/Cslib/Foundations/Lint/Basic.lean)
is defined but lacks `@[env_linter]`. Namespace exceptions are inert at this
pin. Revisit policy when registration changes; do not rename established
public APIs merely to eliminate these entries.

Never run `lake lint -- --update` against the committed allowlist as an
unreviewed cleanup step. The pinned runner writes all current failures and
rewrites the shared file independently for each root. This can introduce new
exceptions and erase another root's entries. Existing upstream
[Batteries PR #1600](https://github.com/leanprover-community/batteries/pull/1600)
addresses pruning without admitting new failures or discarding another root's
entries. Track that PR rather than duplicating it. Until a supported fix is
available, produce candidates in scratch directories and review the combined
result. The local audit never writes an exception file.

Mathlib text exceptions match file and error payload, ignoring line numbers.
For Unicode, one file/character entry covers every occurrence in that file.
Keep the diagrammatic composition symbol `⨟`; normalize duplicate entries,
not the notation. Retain a minimal documented allowlist until an upstream
Unicode extension or accepted symbol makes it unnecessary. An upstream
configuration improvement belongs in a separate dependency/tooling change.

Retain independent universes where composition requires them. Explain each
needed `checkUnivs` suppression next to its declaration. Keep unused-argument
exceptions only when a meaningful public interface requires the argument;
changing names, binder behavior, or definitional equality to reduce a count
is not a compatibility-preserving cleanup.

Deprecated compatibility tests intentionally exercise old names. Their
scoped `linter.deprecated` suppressions are permitted only around the
individual examples. The test-library header exception accommodates worked
examples; it does not exempt production declarations or remove the separate
module-docstring integrity check.

## Category rollout and VCVio

Keep infrastructure, namespace exceptions, Unicode, unused arguments,
universe checks, and compatibility tests in separate reviewable PRs. Every
category reports raw before/after findings, retained reasons, validation,
and public API impact. Pure removal of stale suppressions needs no new
mathematical tests; universe or interface changes need ordinary-import
and universe-polymorphic regressions. Follow the full
[review standard](review-hardening.md).

PolyFun is the faster-moving pilot. VCVio needs a new audit against its own
pins and library roots before adoption: the inspected checkout had no explicit
environment lint driver, disabled Unicode globally, and multiple production,
optional, and dormant roots. Start with reports, then resolve and enforce one
category at a time. Keep dependency updates and public API migrations separate
from cleanup. Do not copy PolyFun's root list or exception policy wholesale.
