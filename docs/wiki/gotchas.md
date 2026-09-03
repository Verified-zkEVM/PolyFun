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

### 6a. Transparency after Lean 4.33

Lean 4.33 split the transparency ladder (`reducible < instances <
implicit < default < all`) and compares assigned metavariable types at
implicit transparency. Semireducible definitions no longer unfold during
unification in `rw` / `simp` / `subst` / instance-argument positions.
Symptoms and fixes (see the Transparency Attributes section of
`CONTRIBUTING.md` for the policy):

- `rw` "did not find an occurrence" though the pattern is visibly there,
  or a goal is "not type-correct under the implicit transparency level"
  → `@[implicit_reducible]` on the definition the implicit arguments go
  through, or `attribute [local implicit_reducible]` (option-free) for
  imported declarations.
- "failed to synthesize instance" for an instance that clearly exists →
  check first whether a `[local reducible]`-style attribute is
  *over-unfolding* the goal (remove it); otherwise
  `@[instance_reducible]` on the wrapper the goal's head hides behind.
- A `rfl` simp lemma rejected as trivial → its LHS head was made
  `@[reducible]`; demote the head to `@[implicit_reducible]` and the
  lemma is valid again.
- A simp lemma silently never fires → its statement may freeze an
  unreduced projection into the discrimination-tree key (e.g. a
  `Sum.inl` binder ascribed through `(P + Q).A`); restate the binder
  with the reduced component types.
- `calc` failing with a `Trans` instance error where a plain `.trans`
  works → typeclass resolution runs below implicit transparency; keep
  the term-level `.trans` form with a comment.

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

### 8. `do`-notation bind uses a different `Bind` instance

Lean's `do`-block elaboration may use a `Bind` instance that differs
syntactically from `Monad.toBind`. This
means `pure_bind`, `bind_assoc`, and `bind_pure` won't fire via `simp`
or `rw` on goals produced by `do` notation in special cases of more
non-standard instances.

**Symptom**: `simp [pure_bind]` or `rw [bind_assoc]` does nothing on a
`do`-block goal.

**Fix**: Use the restated lemmas in
[`PolyFun/Control/Lawful/Basic.lean`](../../PolyFun/Control/Lawful/Basic.lean)
(namespace `LawfulMonad`):
`do_bind_assoc`, `do_bind_pure_comp`, `do_bind_map_left`, and the dependent-pair
specialization `bind_pure_sigma_mk`.

### 8e. A predicate whose leading argument is implicit cannot be passed as an argument

A parameter of type `∀ {Δ : PortBoundary}, F Δ → Prop` looks like the right
way to write a boundary-indexed predicate, and it works fine as a *structure
field* (`SubTheory.mem`, because `D.mem W` is a projection applied to a known
`D`). It breaks as soon as such a predicate is **passed** somewhere: a term
whose type starts with an implicit binder has that binder inserted eagerly, so
the argument arrives eta-expanded as `fun {Δ} ↦ P (Δ := ?m)` and `?m` is never
solved. Symptoms are "don't know how to synthesize implicit argument", motives
printed with doubled binders (`fun {Δ} {Δ} ↦ ...`), and
`Internal error in mkElimApp` from `induction`.

**Fix**: make the index explicit in anything that gets passed —
`∀ (Δ : PortBoundary), F Δ → Prop`. See `SubTheory.generated`'s generator
argument in
[`PolyFun/Interaction/UC/SubTheory.lean`](../../PolyFun/Interaction/UC/SubTheory.lean).
The same applies to the carrier of an indexed family: `Atom` in
`AllowedGen` / `atomSubTheory` is explicit because solving
`?Atom ?Δ ≡ Atom Δ` is not a first-order problem.

### 8f. `@[expose]` defs, or downstream modules cannot unfold them

Under the module system a `def` in a `public section` still has an opaque
body outside its own file unless it is `@[expose]`. A definition that
downstream proofs are meant to *compute with* — a lattice element like
`SubTheory.top`, an order like `SubTheory.le`, a generated construction —
must carry the attribute, or the first cross-module `exact`/`rfl` against it
fails with an unhelpful type mismatch. Lean warns when the attribute is
redundant (instances are exposed by default), so add it and delete what it
flags rather than guessing.

A public characterization theorem does not necessarily preserve constructor
notation. For example, `Refines k₁ k₂ ↔ ∃ f, ...` permits rewriting while an
ordinary-import proof `⟨f, h⟩ : Refines k₁ k₂` still needs the predicate body
or an explicit introduction theorem. If the literal witness shape is part of
the documented API, expose that predicate narrowly and add an ordinary-import
canary for the exact spelling, as in
[`PolyFunTest/ModuleAPI/Interaction.lean`](../../PolyFunTest/ModuleAPI/Interaction.lean).

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

Lean, Mathlib, and cslib must use the same release. When upgrading, update
[`lean-toolchain`](../../lean-toolchain) and both dependency pins in
[`lakefile.toml`](../../lakefile.toml). Then run `lake update` and validate the
result.

### 18. Use public references in shared docs

When a proof framework follows an external paper, cite the public paper
by title, venue, or URL rather than pointing agents at a repo-local file
path. Foundational citations live in
[`REFERENCES.md`](../../REFERENCES.md); module docstrings reference
those keys (`Hancock-Setzer`, `Spivak-Niu`, etc.) rather than copying
prose.

### 11a. `simp` lemmas over `FreeM` do not fire on reducible interfaces

A lemma such as `PFunctor.FreeM.liftM_lift_bind` or `foldFreeM_lift_bind'` has the implicit
response type `P.B a` inside its left-hand side (as the type argument of `>>=`), and `simp`'s
discrimination tree indexes that argument as the projection `PFunctor.B`. On an interface declared
with `abbrev` — `abbrev coinP : PFunctor := ⟨PUnit, fun _ => Bool⟩` — the goal's `coinP.B a`
reduces to `Bool` while the tree is built, so the lemma is never retrieved and `simp` reports it
unused; the same statement over a `def` interface, or over a generic `P`, matches. `rw` is
unaffected. State canaries and downstream lemmas over a generic or `def`-declared interface, or
rewrite explicitly, rather than "fixing" the lemma.

### 11b. `vcgen` finds no spec unless the `Std.Internal.Do` root is imported

`vcgen` consults the `@[spec]` database, and `Spec.bind` / `Spec.pure` live in
`Std.Internal.Do.Triple.SpecLemmas`. A file that imports only `Std.Internal.Do.WP.Basic`
(or reaches the stack through such a module) gets `No spec found for program …` on every
`do` block, with an empty candidate list. Import the root `Std.Internal.Do`; the bridge
modules under `PolyFun/Control/Monad/*/WP.lean` do so for this reason. A leaf with no
registered specification is left as a verification condition with
`vcgen -errorOnMissingSpec`.

### 11c. Projections re-synthesize instance-implicit structure arguments

`Triple`, `WPConjunctive`, and `LawfulWPMonadAttach` take their `WP` / `WPMonad` as
instance-implicit parameters. Projecting (`h.le_wp`) or constructing (`⟨h⟩`, `refine ⟨…⟩`) a
value whose interpretation is a *non-instance* construction (`MAlgOrdered.toWP α`,
`MonadAttach.toWPMonadDemonic`) makes Lean synthesize the instance afresh and fail. Bind the
construction first — `let inst := MAlgOrdered.toWP α` — so it is found as a local instance;
`let`, not `have`, so it stays definitionally the term in the statement.

### 11d. `grind =` cannot index `ite`, `dite`, or thunked applicative operands

`@[grind =]` rejects a lemma whose left-hand side is `f (if c then x else y)` ("invalid
pattern"): `grind` reserves `ite` / `dite` for its own case splitting and will not use them as
pattern heads. Likewise `x <* y` and `x *> y` store `y` under the thunk `fun _ => y`, which a
pattern cannot bind. Such lemmas stay `@[simp]`; `grind` splits the `if` itself and reaches the
applicative forms through `simp`'s normalization to `>>=`.

### 12. `Std.Do` imports are quarantined

Only `PolyFun/Control/Do/Basic.lean`, `PolyFun/PFunctor/Free/Do.lean`, and
`PolyFunTest/Do/` may import `Std.Do`, `Std.Internal.Do`, or `Std.Tactic.Do`
(core's two weakest-precondition stacks and the `mvcgen` / `vcgen` tactics). The
upstream API is evolving quickly (`vcgen` on the `Std.Internal.Do` stack is
replacing `mvcgen`, and that stack becomes a public `Std.WP` in v4.35), so the
dependency stays confined to those files, and everything they export is a
construction (`def`), never a global instance: a global `Std.Do.WP` instance on
`FreeM P` would race downstream registrations on reducible unfoldings such as
oracle-computation types. Register the provided structures `scoped` or `local`
downstream. See [`program-logic.md`](program-logic.md).
