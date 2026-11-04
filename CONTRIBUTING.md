# Contributing to PolyFun

Contribute a definition, proof, test, example, or documentation change. This guide tells you how
to prepare the change, validate it, and describe it for review. Read these pages first:

- [`README.md`](README.md) for the project overview and scope
- [Documentation hub](docs/README.md) for concepts and reading routes
- [Repository map](docs/reference/repo-map.md) and [validation](docs/development/validation.md)
  for contributor workflows
- [`AGENTS.md`](AGENTS.md) for the concise agent policy
- [`REFERENCES.md`](REFERENCES.md) for the citations used by module docstrings

## Before You Start

### Check the scope

PolyFun hosts generic, domain-agnostic infrastructure. It contains polynomial functors,
interaction trees, state machines, generic interaction, program logic, and realizability. It
also contains free, displayed-free, and cofree structures. *Cryptographic* content belongs in
[`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio) or in downstream consumers.
Examples of such content are probabilistic semantics, evaluation distributions,
oracle-simulation security definitions, and scheme-specific algebra.

If a PolyFun definition has a load-bearing dependency on a probability
monad, oracle simulator, or security predicate, parameterize the generic
construction over an arbitrary monad or observation
and let downstream consumers instantiate it.

### Check for overlap and upstream results

Before you start a substantial change, search the open pull requests and issues for the same
target:

```bash
gh pr list -R Verified-zkEVM/PolyFun --state open --search "<declaration or topic>"
gh issue list -R Verified-zkEVM/PolyFun --state open --search "<declaration or topic>"
```

If an open PR covers the same declarations, ask its author whether the work is active.
Do not duplicate active work. If you open a PR for the same target, link the earlier PR and
explain how your work relates to it.

If earlier work appears abandoned, you may ask a maintainer whether to proceed. A maintainer may
waive the overlap requirement for that contribution.

Before you add a generic definition or lemma, search the pinned Lean core, Mathlib, Batteries,
and CSLib for it. The [upstream-first rules](docs/development/review-hardening.md#upstream-first-mathematics)
describe the search and the evidence to record.

## Prepare and Validate a Change

Before review:

1. Fetch the dependency cache with `lake exe cache get`.
2. If you add, delete, or rename source files, stage them with `git add`.
3. Then regenerate each affected umbrella, such as `PolyFun.lean` or `ToCslib.lean`.
   [Generated files](docs/development/generated-files.md) gives the command for each umbrella.
4. Run the full suite with `./scripts/validate.sh --lint --test --axioms`.

The [validation guide](docs/development/validation.md) explains each check, the focused commands,
and the CI jobs. Every change must also obey these source rules:

- Finished work should not contain `sorry` or `admit`. Use `stop` only to preserve partial proof
  work explicitly during a refactor.
- Repository-wide Lean options stay in `lakefile.toml`. Do not restate `autoImplicit = false`
  with a `set_option` line in a file.
- Do not disable linters locally or globally to remove warnings. Fix the underlying issue instead
  of adding `set_option linter.* false`, `set_option weak.linter.* false`, or repository-level
  linter suppressions.

## Pull Requests

### Title format

Use this format for the PR title:

```text
<type>(<optional-scope>): <subject>
```

Choose the type from this list:

- `feat`: a definition, theorem, example, or other library feature
- `fix`: a correction of a defect
- `docs`: documentation
- `refactor`: a change to the organization, names, or interfaces
- `test`: tests and regressions
- `ci`: CI workflows and checks
- `chore`: maintenance, such as dependency updates

Use the scope to identify the affected area in lowercase, for example `pfunctor`, `ipfunctor`,
`itree`, `interaction`, `execution`, `control`, `realizability`, `examples`, or `deps`. Write a
short subject that names the change. It can be an imperative phrase, such as "add lens
monomorphisms", or a noun phrase for the result, such as "exact equations for stateful
interpretation". Keep ordinary words lowercase. Preserve the capitalization of names such as
`FreeM`, and do not end the subject with a period.

For a title without a scope, omit both parentheses, as in `docs: clarify the interface`.

GitHub can use a lone commit subject as the default squash subject. With several commits,
it uses the PR title. The default squash body joins the commit messages. Review and edit that
message to describe the final tree. A rebase merge preserves the individual commit messages.

### Description

Keep the description proportional to the change. Omit topics that do not apply. Give the reader
the information needed to assess the contribution:

- State the problem, the change, and its purpose.
- Identify headline declarations and the scope of each statement.
- Give the public API delta, including removals, renamed declarations, deprecated aliases, and
  instance changes.
- State the validation commands, their results, and the commit that they cover.
- For a substantial PR, record the [review passes](docs/development/review-hardening.md#required-review-passes)
  and the final audit note from the [hardening checklist](docs/development/review-hardening.md#hardening-checklist).
- For a new script, identify its workflow under the [script policy](#repository-scripts).
- Link related issues, the base of a stack, overlapping work, and any downstream VCVio check.
- Describe the known gaps and the parts of a source that the change does not formalize.

Keep the claims in the title and the description consistent with the code and the evidence. A
successful build does not establish fidelity to a source or axiom cleanliness.

### Size and stacking

Give each PR one topic. Separate mechanical changes from mathematical changes when each part can
be reviewed and validated independently. Split a broad change when its independent claims cannot
be reviewed and reverted separately.

Use a native GitHub stack for a contribution that needs several dependent PRs. Name the base of
each PR in its description. Each PR must build and pass its checks against that base. A retargeted
or restacked PR needs fresh checks. The [stack rules](docs/development/review-hardening.md#native-github-stacks)
describe how a stack is merged and checked.

### Writing

The [writing guide](docs/development/writing.md) offers advice for documentation, docstrings,
comments, commit messages, PR and issue text, and review comments. Use it to improve clarity and
precision. Leave clear, correct text alone, even if it does not follow a rule or the checker reports
it. The contribution requirements in this document retain their stated force.

Use the [writing workflow](docs/development/write-technical-prose.md) when you draft or revise
that text. Keep claims, hypotheses, uncertainty, and requirement strength unchanged during a style
edit. The [vocabulary](docs/development/writing-vocabulary.md) records technical meanings. It does
not prohibit other meanings when their context is clear.

The [writing checker](docs/development/write-technical-prose.md#use-the-checker) offers optional
suggestions on changed prose. CI shows its findings as warnings. The findings do not fail a PR,
and an empty report does not establish conformance to the standard.

### Tool-assisted contributions

Authors stay responsible for content produced with an AI agent or another tool:

- Read the headline statements and the full description before you request review.
- Keep temporary plans, handoff notes, and session logs out of the contribution.
- Replace inaccessible planning codes with the maintained source or an explanation.
- Coordinate concurrent tool runs so that they do not open competing PRs for the same target.

## Repository Scripts

Add a script only when it serves a concrete, recurring workflow for library development,
validation, or maintenance. The PR must identify that workflow. It must explain why an upstream
command, a Lake target, or an existing script cannot reasonably provide the workflow. It must also
justify the maintenance of the additional code.

Keep temporary review probes, migration experiments, and one-time audits outside the tracked
repository. Record their findings and validation evidence in the PR. Put lasting guidance in the
owning documentation page. Tests for maintained repository behavior belong on the narrowest
existing test surface. A useful review experiment alone does not justify a new script or CI job.

## Attribution And File Headers

PolyFun uses explicit Lean file headers. Every Lean file under `PolyFun/` names one copyright
holder, "PolyFun Contributors". [`Verified-zkEVM/ArkLib`](https://github.com/Verified-zkEVM/ArkLib)
uses the same convention. The standard header is:

```lean
/-
Copyright (c) CURRENT_YEAR PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
```

* `CURRENT_YEAR` is the calendar year when the file is created.
* The first line *always* gives the copyright to "PolyFun Contributors", never to an individual.
  The project then keeps the copyright, and the headers do not diverge as contributors change.
* The `Authors:` line *always* names individual humans. List the people credited for the design
  and content of the file, separated by commas. This line is the human-attribution channel, and
  routine edits preserve it.

Follow this attribution policy:

1. **New files**: add the standard header with the current year and "PolyFun Contributors" as
   the copyright holder. Name the credited authors on the `Authors:` line.
2. **Routine edits to existing files**: preserve the existing `Authors:` line. Do not rewrite
   attribution only because you edited the file. The copyright line stays "PolyFun Contributors".
3. **Substantial rewrites or replacements**: if new content effectively replaces a file, update
   the `Authors:` line for the new authorship. The copyright line stays "PolyFun Contributors".
4. **Copied or ported material**: a new file can keep substantial structure or content from
   another source. In that case, preserve any required upstream `Authors:` attribution. For
   example, the files imported from `Verified-zkEVM/VCVio` at the start of the project kept their
   `Authors:` line verbatim. Their copyright line names "PolyFun Contributors".
5. **AI assistance**: do not add a separate AI-attribution line. Use the normal header format, with
   only the credited human authors on the `Authors:` line.

When the policy does not decide a case, prefer these choices:

- Preserve the `Authors:` line on incremental edits.
- Update the `Authors:` line only when the file is new or materially replaced.
- Never change the copyright holder away from "PolyFun Contributors".

## Documentation Expectations

- Every ordinary Lean source file should have a module docstring near the top, written with `/-! ... -/`.
- Import-only umbrella modules such as `PolyFun.lean`, and `lakefile.toml`, should stay bare.
- Public definitions and major theorems should have declaration docstrings, written with `/-- ... -/`.
- A module docstring should give a concise title and summary, with notation or references when
  that context materially helps a reader.
- A declaration docstring should describe what a definition is or what a theorem states, not how it
  evolved.
- Docstrings must be intrinsic and descriptive. Cross-reference live definitions when that helps. Do
  not mention removed or renamed declarations, change history, or reactive phrases such as
  "replaces" or "renamed from".
- If a file cites papers, include a references section in the module docstring, or cite the
  source through [`REFERENCES.md`](REFERENCES.md).
- Ordinary Lean source files use this prologue layout, with exactly one blank line between the
  blocks:
  1. the copyright, license, and authors header
  2. the `module` command
  3. the imports
  4. the module docstring

## Module Scopes And Public APIs

Every tracked Lean source in `PolyFun/` and `PolyFunTest/` uses module mode. Production modules
normally put their exported declarations in a `public section`. Test and worked-example modules
normally use `@[expose] public section`. Their definitional regression checks intentionally
normalize local fixtures, and these modules stay outside the production library.

- Use `public import` only when declarations from the imported module occur in the public
  signatures of this module or are intentionally re-exported.
- Use plain `import` for implementation-only dependencies.
- Use `import all` before the corresponding regular or public import when proofs need opaque
  declaration bodies from another module. Comment which definition they unfold.
- The library boundaries for `import all` are in [module APIs](docs/development/module-api.md),
  and `scripts/check-modules.sh` enforces them. Tests can open `ComplexityBackends`. Backends never
  open `PolyFun`. Module canaries open nothing.
- Prefer `@[expose]` on individual definitions whose reduction is part of the public API. Do not
  use `@[expose] public section` in `PolyFun/Interaction/`.

Run `./scripts/check-modules.sh` after you change module scopes. The full validation wrapper runs
this check automatically.

### Transparency Attributes

Start from the intended API of the representation. A failed `rw`, `subst`, or instance search does
not by itself justify a more transparent definition. Check upstream constructors, projections,
eliminators, and equation lemmas first. Reduce the failure to an ordinary-import consumer before
you change the interface. For example, polynomial objects use `PFunctor.Obj.mk`, `fst`, `snd`,
and `rec`. Genuinely Sigma-valued positions and directions use Sigma operations.

Definitional equality is also a useful API commitment. Preserve it where it supports dependent
indices, constructor wrappers, or coherent instance paths:

- **No attribute** is the normal state. Use public equations for ordinary rewriting and recursive
  computation.
- **`@[implicit_reducible]`** is appropriate when a definition is intended to compute in types. Core's
  `Init.MetaTypes` recommends this attribute for operations in type parameters. Explain the
  dependent consumer. An elaboration diagnostic alone is not sufficient evidence.
- **`@[instance_reducible]`** exposes a definition to instance synthesis. Justify the instance
  path, and test it together with competing inherited paths.
- **`@[reducible]`** is appropriate for intentional transparent wrappers. It also suits
  instance-building definitions whose projections must agree during synthesis. Mathlib's hierarchy
  note explicitly relies on reducible non-instances for this purpose. The attribute changes
  indexing and can invalidate head-keyed `rfl` simp lemmas. Do not apply it to recursive functions.
- The `TypeTree.done` and `TypeTree.node` constructor wrappers intentionally support pattern
  matching and reduction to upstream `FreeM` constructors. Preserve those contracts. Do not hide
  all reducers as a blanket policy.
- An imported declaration can need a per-file `attribute [local implicit_reducible] Foo.bar` for
  genuine dependent typing. First check its public API. Then document the missing reduction, the
  affected consumer, and the upstream resolution. Do not use overrides to restore an old simplifier
  normal form or to bypass a new upstream abstraction boundary.
- `allowUnsafeReducibility` requires a specific upstream correction and a justification for a
  global override. A local override is not automatically preferable to a fix in the consumer.
  PolyFun does not use the option.
- Use equation lemmas for structural or well-founded recursion instead of new
  `with_unfolding_all` proofs.

[Public module APIs](docs/development/module-api.md) explains exposure and transparency.
[Review hardening](docs/development/review-hardening.md) gives the source-backed design review.

### Section Headers Within A File

Use Mathlib-style doc-comment section headers, **not** ASCII banners.

For an inline section break inside a Lean file, use a one-line docstring header. Doc-gen renders
it in the generated documentation:

```lean
/-! ## Section title -/
```

For a section with its own paragraph of explanation, use this form:

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

ASCII banners are visually loud and do not appear in the generated documentation. They also
divide the file in a way that the type system does not enforce. The `/-!` form reads as natural
prose and appears in the `doc-gen4` output. A section that needs its own banner usually needs its
own `namespace` or its own file.

## Style Notes

- For proof-only cleanup, preserve declaration names, signatures, binder and universe parameters,
  attributes, imports, and intended definitional equations.
- Prefer a direct theorem application or constructor to a one-step tactic wrapper. Reuse existing
  map, preservation, and extensionality laws before you introduce induction or unfold
  representations.
- Use `rfl` for definitional equations and proof-irrelevance equalities when the public reduction
  contract of the module permits it. Do not expose an opaque body only to shorten a proof.
- Combine identical induction branches only when the common proof stays readable. Keep explicit
  dependent transports and case splits when they explain the types. Fewer lines alone do not
  justify heavier automation.
- Keep theorem docstrings concise, and state the useful relation or assumptions. Check claims
  about equivalence, bounds, and codomains against the declaration, including empty cases.
- Record reusable guidance in the owning documentation. Keep per-file cleanup inventories outside
  the tracked tree.
- Keep imports at the top of the file.
- Follow the [Mathlib naming guide](https://leanprover-community.github.io/contribute/naming.html)
  where possible. These capitalization rules apply in particular:
  - Terms of `Prop`s, such as proofs and theorem names, use `snake_case`.
  - `Prop`s and `Type`s (or `Sort`), such as inductive types, structures, and classes, use
    `UpperCamelCase`.
  - Name a function as you would name its return value. For example, name a function of type
    `A → B → C` as a term of type `C`.
  - All other terms of `Type`s use `lowerCamelCase`.
- Respect the module layering in [`AGENTS.md`](AGENTS.md).
- Use `/-! ## Title -/` doc headers, not ASCII banners, for inline section breaks. See
  [section headers](#section-headers-within-a-file).

## Documentation and examples

Use the [documentation hub](docs/README.md) to find the owning page of each topic. Update that
page in the same PR as a change to a public API, a command, an import boundary, or the layout.
Keep the README focused on purpose, a checked example, installation, and reading routes. Explain
assumptions and theorem scope in the guides and source docstrings. Use the bibliography for
public literature references.

Teaching programs belong under `Examples/Tutorials/` in the optional `PolyFunExamples` target.
Regressions and adversarial cases belong in `PolyFunTest/`. Production libraries import neither.
When examples rely on equations across a package boundary, add public-consumer checks in
[the separate fixture](test/DocumentationConsumer/README.md).

The `lean-example` marker in the README selects a named region from a compiled Lean module.
Change that source and the excerpt together. The integrity checker validates excerpt equality,
local paths, Markdown heading anchors, and module docstrings. Historical progress notes belong in
Git and PR history. Preserve useful rationale in the owning guide before you remove a stale
document.

## Case-study validation

Maintained applications live under `Examples/` in the optional `PolyFunExamples` library. The
recurring Parliament test, `scripts/test-parliament-cli.py`, uses temporary directories. It checks
process exit codes, terminal input, writer locks, publication, and recovery. The validation wrapper
and CI run it after they build `polyfun-parliament`. Every spawned process needs a bounded wait and
cleanup on failure.

Generate the public import index of the case study with
`./scripts/update-lib.sh Examples.Parliament`. This optional library root is distinct from the
tutorial modules, which need no umbrella. Use the separate `test/ParliamentConsumer` package to
check its public interfaces.

## Licensing

This project is licensed under Apache 2.0. By contributing, you agree
that your contributions are licensed under the same terms.
