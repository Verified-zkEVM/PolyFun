# Gotchas and Troubleshooting

## Critical (Will Bite You Immediately)

### 1. `autoImplicit = false` is set globally in `lakefile.toml`

Every variable must be explicitly declared. Do not rely on Lean's
auto-implicit mechanism, and do not add
`set_option autoImplicit false` in individual files.

**Symptom**: `unknown identifier` for variables you expected Lean to
infer.

### 2. `TypeTree.done` and `TypeTree.node` are `@[match_pattern, reducible]` wrappers

`TypeTree` is defined as `PFunctor.FreeM TypeTree.basePFunctor PUnit`, with
`done` / `node` exposed as `@[match_pattern, reducible]` wrappers over
`PFunctor.FreeM.{pure, liftBind}`. Pattern matching on `done` / `node` works
transparently; `rfl` against the polynomial substrate also works. **Do
not break either invariant when refactoring** the substrate or these
wrappers.

### 3. No cryptographic content

Do not introduce dependencies on probability monads (`PMF`,
`evalDist`, `ProbComp`), evaluation distributions, oracle simulation
typeclasses, security predicates, or concrete cryptographic algebra
(specific groups, fields, hash functions). Parameterize over an abstract
monad `m : Type v → Type w` with `[Pure m]` / `[Monad m]` / `[LawfulMonad m]`
instead. Cryptographic content belongs in
[`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio)
downstream.

When in doubt, ask: *can I state this against an arbitrary monad with no
probability and no security predicate?* If yes, it belongs here. If no,
push it downstream.

### 4. Files should stay under 1500 lines

Unless explicitly opted out per file. The long-file linter cap is
enforced repo-wide.

### 5. Do not disable linters to silence errors

Do not use `set_option linter.* false`,
`set_option weak.linter.* false`, or add repo-level `leanOptions` that
turn lints off. Fix the root cause instead. Treat linter failures as
real problems and fix the underlying declaration, proof, naming, or
formatting issue.

## Type System

### 6. Core types are `@[reducible]` thin wrappers

`TypeTree`, `Decoration`, `Strategy`, and friends are `def` / `abbrev` /
`@[reducible]` over `PFunctor.FreeM` machinery. Lean may unfold them
aggressively. Use the canonical eliminators
(`PFunctor.FreeM.rec` / `FreeM.induction` and the
`Decoration` / `Path` analogues) rather than pattern matching on
`PFunctor.FreeM.pure` / `liftBind` directly.

### 7. Universe polymorphism

`PFunctor` carries two universe parameters `(uA, uB)`; `FreeM`,
`Decoration`, `TypeTree`, `Strategy`, and the open-process layer add more
on top (one for the monad's argument universe, one for its result
universe). Universe unification errors are common when composing
across layers because lens-style `MonadLift` parents drag in extra
metavariables.

**Fix**: Use `{ι : Type*}` rather than `{ι : Type u}` to let universes
resolve independently. Keep `α β : Type` (not `Type u`) when a single
universe suffices.

### 8. `do`-notation bind uses a different `Bind` instance (Lean 4.29+)

Lean 4.29 changed `do`-block elaboration so the desugared bind may use
a `Bind` instance that differs syntactically from `Monad.toBind`. This
means `pure_bind`, `bind_assoc`, and `bind_pure` won't fire via `simp`
or `rw` on goals produced by `do` notation in special cases of more
non-standard instances.

**Symptom**: `simp [pure_bind]` or `rw [bind_assoc]` does nothing on a
`do`-block goal.

**Fix**: Use the restated lemmas in
[`PolyFun/Control/Lawful/Basic.lean`](../../PolyFun/Control/Lawful/Basic.lean)
(namespace `LawfulMonad`):
`do_pure_bind`, `do_bind_pure`, `do_bind_assoc`, `do_bind_pure_comp`,
`do_map_bind`, `do_bind_map_left`. All are `@[simp]`.

## Proof Patterns

### 8b. Keep one canonical concrete-step relation type

`PFunctor.DynSystem.StepRel s₁ s₂` is the canonical relation type on explicit
concrete steps (`s₁.Step → s₂.Step → Prop`). Its process-specific views
(`ProcessOver.StepRel`, `Process.StepRel`, and
`Observation.Process.StepRel`) should remain abbrevs of that one type.
Keeping the source state inside each step avoids hidden implicit state
arguments and makes applications, composition witnesses, and type errors show
the dependent data at the point where it is used.

### 8c. Alias layers over generic types: shadow the chained operations

`ProcessOver`, `Machine`, `ProcessOver.Run`, … are abbrevs over the
generic `PFunctor.DynSystem` types. Dot notation on a binder whose
declared type is the alias resolves methods in the alias's namespace,
but a value *returned by a generic operation* has the generic head, so
chained calls (`run.tail.eventsUpTo`) lose the alias namespace. When a
generic operation returns the aliased type and is used in chains,
re-export it as an abbrev with the alias-typed signature
(`abbrev Run.tail (run : Run process) : Run process := DynSystem.Run.tail run`);
the alias is definitionally transparent, so proofs are unaffected.

### 8d. Alias layers: alias-namespace lemmas are not dot-callable on generic-headed values

The reverse direction of 8c. Lemmas that live in an *alias's* namespace
(e.g. `Interaction.Concurrent.Refinement.SafetyRefinement.safe_of_satisfies`
over `SafetyRefinement := PFunctor.DynSystem.SafetyRefinement ...`) cannot
be reached by dot notation on a value whose head symbol is the generic
structure — and structure projections always produce generic-headed
values (`bisim.forth : DynSystem.SafetyRefinement ...`), even when `bisim`'s
declared type is the alias. So `bisim.forth.safe_of_satisfies` fails while
`sim.safe_of_satisfies` on a binder `sim : SafetyRefinement ...` succeeds.
Use full application (`SafetyRefinement.safe_of_satisfies bisim.forth ...`)
at such sites, or keep the lemma in the generic namespace if it is not
specific to the alias layer.

### 9. Avoid `cast` / `Eq.mp` / `Eq.mpr` in core definitions

Per [`AGENTS.md`](../../AGENTS.md): keep core definitions, especially in
`PolyFun/Interaction/`, free of proof-generated transports such as
`cast`, `Eq.mp`, `Eq.mpr`, `eq_mpr`, or casts introduced by `rw`,
`simp`, `convert`, or similar tactics. These usually indicate that the
dependent indexing or recursion principle is not definitionally aligned.
Prefer redesigning the type or API so branches compute by pattern
matching.

Intrinsic typed reindexing operations such as `Fin.castLE`, `Fin.succ`,
or established Mathlib combinators are acceptable when they are the
intended data transformation.

### 10. Preserve partial proof attempts with `stop`

When a proof attempt is not finished or is currently broken, insert a
local `stop` marker instead of deleting large proof blocks. This
preserves search context for later agents.

### 11. Prefer existing combinators over bespoke wrappers

Per [`AGENTS.md`](../../AGENTS.md): if a definition is just snoc, append,
update, projection, or reindexing and a clear standard combinator
already expresses it, use that combinator directly. Do not write a
wrapper definition just to give the operation a project-specific name.

## Module Structure

### 12. Module organization: no thin re-export umbrellas inside subdirectories

When splitting a file into a folder of submodules, do **not** add a
sibling `X.lean` whose only content is a chain of
`import X.A; import X.B`. Each caller imports the specific submodule it
actually uses.

**Allowed umbrellas** (strictly top-level roots only): `PolyFun.lean` is
the only allowed umbrella. It is generated by
[`scripts/update-lib.sh`](../../scripts/update-lib.sh); see
[`generated-files.md`](generated-files.md).

**Not allowed**: umbrellas inside a subdirectory (e.g. a top-level
`PolyFun.PFunctor` umbrella beside the `PolyFun/PFunctor/` folder, or a
`PolyFun.Interaction.Basic` umbrella beside the
`PolyFun/Interaction/Basic/` folder). Even if a module "feels cohesive",
callers must import the specific submodule they use.

### 13. Full cutover, no backward-compatibility shims

When refactoring APIs, notations, or proof infrastructure, update all
call sites in one pass. Do not add deprecated aliases, migration
wrappers, or compatibility layers.

### 14. Agent guidance files must be committed

Agents dispatched to `git worktree` clones need to read
[`AGENTS.md`](../../AGENTS.md), this wiki, and any other guidance files.
Ensure these are committed so all worktrees see them. Do not park
durable guidance in untracked `*-NEVER-COMMIT.md` notes; those are
strictly ephemeral.

## Build and Tooling

### 15. Always run `lake exe cache get` before `lake build`

Building Mathlib from source takes hours. Always fetch the precompiled
cache first.

### 16. After adding new `.lean` files, run `./scripts/update-lib.sh`

This regenerates `PolyFun.lean`, the umbrella import file covered by the
build import check
([`scripts/check-imports.sh`](../../scripts/check-imports.sh)). CI
checks that it is up to date. Stage new files first;
`./scripts/update-lib.sh` deliberately fails if untracked
`PolyFun/**/*.lean` files are present.

### 17. Lean toolchain and Mathlib version must stay in sync

Both currently `v4.29.0`. When upgrading, update both
[`lean-toolchain`](../../lean-toolchain) and the `require mathlib` line
in [`lakefile.toml`](../../lakefile.toml) simultaneously.

### 18. Use public references in shared docs

When a proof framework follows an external paper, cite the public paper
by title, venue, or URL rather than pointing agents at a repo-local file
path. Foundational citations live in
[`REFERENCES.md`](../../REFERENCES.md); module docstrings reference
those keys (`Hancock-Setzer`, `Spivak-Niu`, etc.) rather than copying
prose.
