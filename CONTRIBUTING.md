# Contributing to PolyFun

Thanks for contributing.

Start with:

- [`README.md`](README.md) for the project overview and scope
- [Documentation hub](docs/README.md) for concepts and reading routes
- [Repository map](docs/reference/repo-map.md) and [validation](docs/development/validation.md) for contributor workflows
- [`AGENTS.md`](AGENTS.md) for the concise agent policy
- [`REFERENCES.md`](REFERENCES.md) for the citations used by module docstrings

Before sending work for review:

- Fetch dependencies with `lake exe cache get`, then run
  `./scripts/validate.sh --lint --test --axioms`.
- Stage new/deleted/renamed source files before regenerating the matching
  umbrella with `./scripts/update-lib.sh`, `./scripts/update-lib.sh ToCslib` or
  `./scripts/update-lib.sh ComplexityBackends`.
- Finished work should not contain `sorry` or `admit`. Use `stop` only when
  explicitly preserving partial proof work during a refactor.
- Keep repo-wide Lean options in `lakefile.toml`. Do not restate
  `autoImplicit = false` with per-file `set_option` lines.
- Do not disable linters locally or globally to make warnings disappear.
  Fix the underlying issue instead of adding `set_option linter.* false`,
  `set_option weak.linter.* false`, or repo-level linter suppressions.

## Scope

PolyFun hosts generic, domain-agnostic infrastructure: polynomial functors,
free / displayed-free / cofree structures, interaction trees, state machines,
generic interaction, program logic, and realizability. PRs that
introduce *cryptographic* content (probabilistic semantics, evaluation
distributions, oracle-simulation security definitions, scheme-specific
algebra) belong in [`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio)
or downstream consumers, not here.

If a PolyFun definition has a load-bearing dependency on a probability
monad, oracle simulator, or security predicate, parameterize the generic
construction over an arbitrary monad or observation
and let downstream consumers instantiate it.

## Repository Scripts

Add a script only when it serves a concrete, recurring library development,
validation, or maintenance workflow. The PR must identify that workflow,
explain why an upstream command, Lake target, or existing script cannot
reasonably provide it, and justify maintaining the additional code.

Keep temporary review probes, migration experiments, and one-time audits
outside the tracked repository. Record their findings and validation evidence
in the PR, and put lasting guidance in the owning documentation page. Tests for
maintained
repository behavior belong on the narrowest existing test surface; a useful
review experiment alone does not justify a new script or CI job.

## Attribution And File Headers

This repo uses explicit Lean file headers. Every Lean file under
`PolyFun/` uses a single canonical copyright holder, "PolyFun
Contributors", matching the convention used by
[`Verified-zkEVM/ArkLib`](https://github.com/Verified-zkEVM/ArkLib).
The standard header is:

```lean
/-
Copyright (c) CURRENT_YEAR PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
```

* `CURRENT_YEAR` is the calendar year when the file is created.
* The first line *always* attributes copyright to "PolyFun
  Contributors" — never to an individual. This keeps copyright
  ownership with the project and avoids per-file divergence as
  contributors come and go.
* The `Authors:` line *always* names individual humans. List the
  people credited for the file's design and content; comma-separate
  multiple authors. This line is the human-attribution channel and is
  preserved on routine edits.

Attribution policy:

1. **New files**: add the standard header with the current year,
   "PolyFun Contributors" as copyright holder, and the author
   name(s) that should be credited for the new file on the
   `Authors:` line.
2. **Routine edits to existing files**: preserve the existing
   `Authors:` line. Do not rewrite attribution just because you
   touched the file. The copyright line stays "PolyFun Contributors"
   regardless of who edits.
3. **Substantial rewrites or replacements**: if a file is effectively
   replaced with new content, update the `Authors:` line to reflect
   the new authorship. The copyright line still stays "PolyFun
   Contributors".
4. **Copied or ported material**: if a new file is derived from an
   existing file or external source and substantial original
   structure / content remains, preserve any required upstream
   `Authors:` attribution. Files imported from
   `Verified-zkEVM/VCVio` during the initial bootstrap had their
   copyright line normalized to "PolyFun Contributors" but their
   `Authors:` line retained verbatim.
5. **AI assistance**: do not add a separate AI-attribution line. Use
   the repo's normal header format with only the credited human
   author name(s) on the `Authors:` line.

When in doubt, prefer:

- preserving the `Authors:` line on incremental edits
- updating the `Authors:` line only when the file is genuinely new or
  materially replaced
- never changing the copyright holder line away from "PolyFun
  Contributors"

## Documentation Expectations

- Every ordinary Lean source file should have a module docstring near the
  top using `/-! ... -/`.
- Import-only umbrella modules such as `PolyFun.lean`, along with
  `lakefile.toml`, should stay bare.
- Public definitions and major theorems should have declaration docstrings
  using `/-- ... -/`.
- Module docstrings should give a concise title and summary, and include
  notation or references when that context materially helps a reader.
- Declaration docstrings should describe what a definition is or what a
  theorem states, not how it evolved.
- Docstrings must be intrinsic and descriptive. Cross-reference live
  definitions when helpful, but do not mention removed or renamed
  declarations, change history, or reactive phrases such as "replaces"
  or "renamed from". The one exception is a compatibility shim or alias,
  whose docstring names the replacement; see
  [`docs/development/compatibility.md`](docs/development/compatibility.md).
- If a file cites papers, include a references section in the module
  docstring or cite the source via [`REFERENCES.md`](REFERENCES.md).
- For ordinary Lean source files, use this prologue layout:
  1. copyright / license / authors header
  2. one blank line
  3. the `module` command
  4. one blank line
  5. imports
  6. one blank line
  7. module docstring

  Keep exactly one blank line between these blocks.

## Module Scopes And Public APIs

Every tracked Lean source in `PolyFun/` and `PolyFunTest/` uses module mode.
Production modules normally place their exported declarations in a
`public section`. Test and worked-example modules normally use
`@[expose] public section`: their definitional regression checks intentionally
normalize local fixtures, while remaining outside the production library.

- Use `public import` only when declarations from the imported module occur in
  this module's public signatures or are intentionally re-exported.
- Use plain `import` for implementation-only dependencies.
- Use `import all` before the corresponding regular or public import when
  proofs need opaque declaration bodies from another module, and comment which
  definition they unfold. Library boundaries for `import all` (tests may open
  `ComplexityBackends`, backends never open `PolyFun`, module canaries open
  nothing) are listed in `docs/development/module-api.md` and enforced by
  `scripts/check-modules.sh`.
- Prefer `@[expose]` on individual definitions whose reduction is part of the
  public API. Do not use `@[expose] public section` in `PolyFun/Interaction/`.

Run `./scripts/check-modules.sh` after changing module scopes. The full
validation wrapper runs this check automatically.

### Transparency Attributes

Start from the representation's intended API. A failed `rw`, `subst`, or
instance search does not by itself justify making a definition more transparent.
Check upstream constructors, projections, eliminators, and equation lemmas first;
reduce the failure to an ordinary-import consumer before changing the interface.
For example, polynomial objects use `PFunctor.Obj.mk` / `fst` / `snd` / `rec`,
while genuinely Sigma-valued positions and directions use Sigma operations.

Definitional equality is also a useful API commitment. Preserve it where it
supports dependent indices, constructor wrappers, or coherent instance paths:

- **No attribute** is the normal state. Use public equations for ordinary
  rewriting and recursive computation.
- **`@[implicit_reducible]`** is appropriate when a definition is intended to
  compute in types. Core's `Init.MetaTypes` recommends this for operations in
  type parameters. Explain the dependent consumer; an elaboration diagnostic
  alone is insufficient evidence.
- **`@[instance_reducible]`** exposes a definition to instance synthesis.
  Justify the instance path and test it together with competing inherited paths.
- **`@[reducible]`** is appropriate for intentional transparent wrappers and
  instance-building definitions whose projections must agree during synthesis.
  Mathlib's hierarchy note explicitly relies on reducible non-instances for
  this purpose. It changes indexing and can invalidate head-keyed `rfl` simp
  lemmas. Do not apply it to recursive functions.
- The `TypeTree.done` / `TypeTree.node` constructor wrappers intentionally
  support pattern matching and reduction to upstream `FreeM` constructors.
  Preserve those contracts; do not hide all reducers as a blanket policy.
- An imported declaration may need a per-file
  `attribute [local implicit_reducible] Foo.bar` for genuine dependent typing.
  First check its public API, then document the missing reduction, affected
  consumer, and upstream resolution. Do not use overrides to restore an old
  simplifier normal form or to bypass a new upstream abstraction boundary.
- `allowUnsafeReducibility` requires a specific upstream correction and a
  justification for a global override. A local override is not automatically
  preferable to fixing the consumer. The option is currently unused.
- Use equation lemmas for structural or well-founded recursion instead of new
  `with_unfolding_all` proofs.

See [public module APIs](docs/development/module-api.md) for exposure versus
transparency and [review hardening](docs/development/review-hardening.md) for the
source-backed design review.

### Section Headers Within A File

Use Mathlib-style doc-comment section headers, **not** ASCII banners.

For an inline section break inside a Lean file, use a one-line docstring
header that doc-gen will render in the generated documentation:

```lean
/-! ## Section title -/
```

Or, for a section with its own paragraph of explanation:

```lean
/-!
## Section title

Optional paragraph describing what the section contains.
-/
```

Do **not** use ASCII banners such as:

```lean
-- ============================================================================
-- § Section title
-- ============================================================================
```

ASCII banners are visually loud, do not appear in the generated
documentation, and make the file feel partitioned in a way that the
type system does not enforce. Prefer the `/-!` form, which both reads
as natural prose and surfaces in `doc-gen4` output. If a section is
large enough to warrant its own banner, it is usually large enough to
warrant its own `namespace` or its own file.

## Style Notes

- Keep imports at the top of the file.
- Follow Mathlib naming conventions where possible. See the
  [Mathlib naming guide](https://leanprover-community.github.io/contribute/naming.html)
  for the full set of rules. The capitalization rules in particular:
  - Terms of `Prop`s (e.g. proofs, theorem names) use `snake_case`.
  - `Prop`s and `Type`s (or `Sort`) (inductive types, structures, classes)
    are in `UpperCamelCase`.
  - Functions are named the same way as their return values (e.g. a
    function of type `A → B → C` is named as though it is a term of
    type `C`).
  - All other terms of `Type`s (basically anything else) are in
    `lowerCamelCase`.
- Respect the module layering documented in [`AGENTS.md`](AGENTS.md).
- Use `/-! ## Title -/` doc-headers, not ASCII banners, for inline
  section breaks (see *Documentation Expectations* above).

## Licensing

This project is licensed under Apache 2.0. By contributing, you agree
that your contributions are licensed under the same terms.

## Documentation and examples

Use the [documentation hub](docs/README.md) to find each topic's owning page.
Update it in the same PR as a public API, command, import boundary, or layout
change. Keep the README focused on purpose, a checked example, installation,
and reading routes. Explain assumptions and theorem scope in the guides and
source docstrings; use the bibliography for public literature references.

Teaching programs belong under `Examples/Tutorials/` in the optional
`PolyFunExamples` target. Regressions and adversarial cases belong in
`PolyFunTest/`. Production libraries import neither. Add public-consumer checks
in [the separate fixture](test/DocumentationConsumer/README.md) when examples
rely on equations across a package boundary.

The README's `lean-example` marker selects a named region from a compiled Lean
module. Change that source and the excerpt together. The integrity checker
validates excerpt equality, local paths, Markdown heading anchors, and module
docstrings. Historical progress notes belong in Git/PR history; preserve useful
rationale in the owning guide before removing a stale document.

## Case-study validation

Maintained applications live under `Examples/` in the optional `PolyFunExamples`
library. Parliament's recurring `scripts/test-parliament-cli.py` checks process
exit codes, terminal input, writer locks, publication, and recovery using temporary
directories. The validation wrapper and CI run it after building `polyfun-parliament`.
Every spawned process needs a bounded wait and cleanup on failure.

Generate its public import index with `./scripts/update-lib.sh Examples.Parliament`.
This optional library root is distinct from tutorial modules, which need no umbrella.
Use the separate `test/ParliamentConsumer` package to check its public interfaces.
