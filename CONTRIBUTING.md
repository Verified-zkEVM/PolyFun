# Contributing to PolyFun

Thanks for contributing.

Start with:

- [`README.md`](README.md) for the project overview and scope
- [`AGENTS.md`](AGENTS.md) for repo workflow, module layering, and proof guidance
- [`REFERENCES.md`](REFERENCES.md) for the citations used by module docstrings

Before sending work for review:

- Run `lake exe cache get && lake build`.
- After adding new `.lean` files, run `./scripts/update-lib.sh`.
- Finished work should not contain `sorry` or `admit`. Use `stop` only when
  explicitly preserving partial proof work during a refactor.
- Keep repo-wide Lean options in `lakefile.toml`. Do not restate
  `autoImplicit = false` with per-file `set_option` lines.
- Do not disable linters locally or globally to make warnings disappear.
  Fix the underlying issue instead of adding `set_option linter.* false`,
  `set_option weak.linter.* false`, or repo-level linter suppressions.

## Scope

PolyFun hosts generic, domain-agnostic infrastructure: polynomial functors,
free / displayed-free / cofree structures, interaction trees, and the
generic interaction framework over a polynomial substrate. PRs that
introduce *cryptographic* content (probabilistic semantics, evaluation
distributions, oracle-simulation security definitions, scheme-specific
algebra) belong in [`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio)
or downstream consumers, not here.

If a PolyFun definition has a load-bearing dependency on a probability
monad, oracle simulator, or security predicate, that's a smell — please
parameterize over an arbitrary monad and let downstream consumers
instantiate.

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
  or "renamed from".
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
  proofs need opaque declaration bodies from another module.
- Prefer `@[expose]` on individual definitions whose reduction is part of the
  public API. Do not use `@[expose] public section` in `PolyFun/Interaction/`.

Run `./scripts/check-modules.sh` after changing module scopes. The full
validation wrapper runs this check automatically.

### Transparency Attributes

Lean orders unfolding by transparency level (`reducible < instances <
implicit < default < all`) and, since Lean 4.33, respects those levels
strictly: assigned metavariable types are compared at *implicit*
transparency, and typeclass resolution unfolds only up to *instances*
transparency. A plain `def` no longer unfolds during unification in those
positions. Choose the weakest attribute that fixes the failure:

- **No attribute** is the normal state. Prefer an equation or simp lemma
  over a transparency change when a proof merely rewrites through a
  definition.
- **`@[implicit_reducible]`** is the standard fix for Lean 4.33
  unification failures (`rw` not finding a visible pattern, `subst`
  motive errors, goals "not type-correct under the implicit transparency
  level"). It unfolds during implicit-transparency checks only; simp
  validation, simp and typeclass indexing are unaffected, so `rfl` simp
  lemmas keyed on the definition stay valid. Per the core documentation
  (`Init.MetaTypes`), operations occurring in type parameters should be
  implicit-reducible as a basic rule.
- **`@[instance_reducible]`** when *instance synthesis* must see through
  the definition. This changes typeclass discrimination-tree indexing;
  use it only for genuine instance-resolution failures.
- **`@[reducible]`** only for thin type wrappers all automation should
  index through (the `TypeTree.done` / `TypeTree.node` pattern). It
  invalidates `rfl` simp lemmas whose head is the wrapper, and is never
  appropriate on recursive functions.
- **`attribute [local implicit_reducible] Foo.bar`** is the sanctioned,
  option-free way to grant one file implicit-transparency access to an
  imported declaration (including Mathlib/cslib ones). Add a short
  comment naming the proofs that need it. `attribute [local reducible]`
  on imported declarations requires `allowUnsafeReducibility` and is not
  permitted.
- **`set_option allowUnsafeReducibility true`** is reserved for a
  *global* attribute on an imported declaration, always with a comment
  justifying why a local attribute does not suffice and pointing at the
  upstream fix. The option is currently unused: every override of an
  imported declaration is a per-file `attribute [local implicit_reducible]`.
- **`with_unfolding_all`** should not appear in new proofs; prefer
  equation lemmas for well-founded or structural recursion.

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
