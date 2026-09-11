# Linter setup and exception maintenance

## Commands and coverage

```bash
lake exe cache get
lake build PolyFun ToCslib PolyFunCslib PolyFunTest --wfail
lake lint -- --trace
lake exe lint-style PolyFun ToCslib PolyFunCslib
```

The convenience command `./scripts/validate.sh --lint --test --axioms` runs
all production builds with warnings fatal, environment and text-style
linting, the test library, and the integrity/axiom checks.

`PolyFun`, `ToCslib`, and `PolyFunCslib` are separate production roots. All must be named in
environment linting and standalone text linting. The default target is only
`PolyFun`, so `lake exe lint-style` alone misses the other two roots. The style CI job
uses the upstream action for the default target and an explicit command for
the auxiliary roots. Update coverage when adding another production library.

The checks serve different purposes:

- Build-time linters include Mathlib's standard set and core's `checkUnivs`.
  `--wfail` makes their warnings fail the build.
- `lake lint` uses Batteries' environment runner, with all production roots
  supplied by `lintDriverArgs`. `--trace` shows which checks actually run.
- `lake exe lint-style PolyFun ToCslib PolyFunCslib` uses Mathlib's source-text checks,
  including Unicode. Build-time checks do not cover every text-style rule.

`PolyFunTest` is built with warnings fatal and excluded from production
environment linting. Its headers use the same standard checks as production. Run a fresh build before environment linting: the
[Batteries runner](https://github.com/leanprover-community/batteries/blob/4488d40d070b9700d4d5a6aa342f0d40c31b2a2d/scripts/runLinter.lean)
can reuse existing oleans. It imports each root independently at private
visibility, including private bodies and documentation.

## Registration and upstream tools

Keep the upstream runner and standard linter set. A definition or Lake option
alone does not demonstrate that an environment linter is registered or runs.
For example, the
[cslib namespace linter at the recorded pin](https://github.com/leanprover/cslib/blob/98e395a701f2027a413ad24729e1a11a6c772eb4/Cslib/Foundations/Lint/Basic.lean)
lacks `@[env_linter]` and is outside this project's lint policy. It checks private
internal names instead of source names and can reject valid namespaces such as
`Id` and `LawfulMonad` when no nested namespace is registered. Namespace placement
remains part of API review; retiring the inactive exception list does not
represent fixes to those APIs. Recheck registration when dependency pins change;
the exact revisions are in `lake-manifest.json`.

Mathlib's `pythonStyle`, `checkInitImports`, and `allScriptsDocumented` options
are inactive by default in the pinned upstream configuration and absent from
`mathlibStandardSet`. We use those defaults: the Python runner expects Mathlib's
script layout, the import check inspects Mathlib's graph, and the script catalog
check is optional. Removing redundant overrides does not enable these checks.

Optional checks should be assessed against the library's intended API before
enforcement. Use upstream commands or temporary probes for those reviews.
Record findings in the PR and follow the
[repository script policy](../../CONTRIBUTING.md#repository-scripts) before
adding tooling to repeat an audit.

## Exception maintenance

Exception cleanup should address one category at a time. Test candidate
removals in an isolated worktree, rebuild, and rerun the relevant upstream
checks. Record retained reasons and any public API impact. Inspect both
`@[nolint]` annotations and JSON exceptions: either can hide a finding.

Do not run `lake lint -- --update` against the committed allowlist as an
unreviewed cleanup step. The recorded Batteries pin writes all current
failures and rewrites the shared file independently for each root. This can
introduce new exceptions and erase another root's entries.
[Batteries PR #1600](https://github.com/leanprover-community/batteries/pull/1600)
addresses pruning without admitting new failures or discarding another
root's entries. Check the runner at the installed pin before using update
mode, and review the combined result across roots.

[Mathlib text exceptions](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/Linter/TextBased.lean)
match the file and error payload, ignoring line numbers. One Unicode
file/character entry covers every occurrence in that file. Check for duplicate
entries and deleted paths; preserve intentional notation such as `⨟` while
removing obsolete exceptions.

Follow the linter policy in [AGENTS.md](../../AGENTS.md#critical-gotchas).
Existing suppressions do not authorize new ones. Preserve independent
universes where composition requires them, and test compatibility before
changing binders or public interfaces to eliminate a finding.

Downstream projects need their own root inventory and checks against their
own dependency pins. Validate their configuration before adopting enforcement;
PolyFun's root list and exception file are specific to this library.
