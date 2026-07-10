# PolyFun — AI Agent Guide

Lean 4 library for polynomial functors, interaction trees, and a generic
interaction framework over a polynomial substrate. Built on Mathlib.

## Fast Start

1. Run `lake exe cache get && lake build`.
2. To gauge the Polynomial-functor / FreeM substrate, start with
   [`PolyFun/PFunctor/Basic.lean`](PolyFun/PFunctor/Basic.lean) and
   [`PolyFun/PFunctor/Free/Basic.lean`](PolyFun/PFunctor/Free/Basic.lean).
3. To gauge interaction trees, start with
   [`PolyFun/ITree/Basic.lean`](PolyFun/ITree/Basic.lean).
4. To gauge the protocol-flavored interaction framework, start with
   [`PolyFun/Interaction/Basic/Spec.lean`](PolyFun/Interaction/Basic/Spec.lean)
   and [`PolyFun/Interaction/Basic/Decoration.lean`](PolyFun/Interaction/Basic/Decoration.lean).

`AGENTS.md` is the canonical guide. `CLAUDE.md` is a symlink to this file.

## What This Project Is

PolyFun packages three layers of generic, domain-agnostic infrastructure
that emerged from the cryptographic-protocols formalization in
[`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io):

1. **Polynomial functors and lenses.** `PFunctor` cores (positions /
   directions), polynomial charts, lenses (Cartesian, state),
   equivalences, free monad `FreeM`, displayed `FreeM`, and the
   `Cofree` / M-type companion. The Spivak-Niu *Poly* category and its
   internal-language fragments live here.
2. **Interaction trees** in the style of Xia-Zakowski-He-Hur-Malecha-
   Pierce-Zdancewic (POPL 2020), modeled as the M-type of a one-step
   polynomial functor, with strong / weak bisimulation, simulation,
   handlers, and event signatures.
3. **Generic interaction framework** for sequential, two-party,
   multi-party, and concurrent interaction over a `Spec` polynomial
   substrate (`Spec := PFunctor.FreeM Spec.basePFunctor PUnit`), with
   structural decoration, syntax / strategy / execution lenses, and an
   open-process layer for compositional reasoning. Hancock-Setzer
   recursion over interaction interfaces.

PolyFun is intentionally *not* the place for cryptographic content.
Probabilistic semantics, evaluation distributions, oracle-simulation
security definitions, scheme-specific algebra, and concrete-protocol
runtime layers all live in
[`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io)
and depend on this library.

## Repo Map

- `PolyFun/PFunctor/`: polynomial functors, charts, lenses, equivalences,
  M-type / cofree, free monad and displayed-free machinery.
- `PolyFun/IPFunctor/`: state-indexed polynomial functors (`IPFunctor I`)
  and their indexed free monads. `Free/Basic.lean` holds the single-index
  `FreeM` (state-polymorphic continuations); `Free/Indexed.lean` holds the
  two-index `FreeM₂` carrying a `LawfulIndexedMonad` instance.
- `PolyFun/ITree/`: coinductive interaction trees, bisimulation,
  simulation, handlers, event signatures.
- `PolyFun/Interaction/`: protocol-flavored generic interaction framework.
  - `Basic/`: `Spec`, node contexts, decorations, syntax / shape /
    interaction, strategies, append / replicate / state-chain
    composition.
  - `TwoParty/`: sender / receiver roles, paired strategies, refinement,
    swap, composition.
  - `Multiparty/`: native multiparty local views and per-party profiles.
  - `Concurrent/`: structural concurrent specs, frontiers, processes,
    machines, traces, fairness, liveness, refinement, bisimulation,
    interleaving, observation.
  - `UC/`: open-process / open-theory layer, structural composition
    (interfaces, par, wire, plug), corruption models, environment
    actions, leakage. *Generic only* — security-flavored UC layers
    (computational equivalence, asymptotic security) live in VCV-io.
- `PolyFun/Control/`: monad and comonad infrastructure transitively
  required by the above (coalgebra, comonad, free / freecont monad
  algebra, monad iter / hom, lawful re-exports).
- `PolyFun/Logic/`: small logic helpers (`HEq`).
- `PolyFunTest/`: separate test / worked-example library (glob
  `PolyFunTest.+`), built by `lake test` and kept out of the `lake lint`
  scope. Holds the dynamical / interaction worked examples and the
  `IPFunctor` `do`-notation smoke tests. Imports `PolyFun` one-way; nothing
  in `PolyFun` depends on it.

## Module Layering

Imports flow strictly downward; cycles are a build error.

```
PFunctor/{Basic, Bound, M, Equiv, Chart, Lens}
  → PFunctor/{Cofree, Trace}
  → PFunctor/Free/{Basic, Path}
  → PFunctor/Free/{Displayed, Displayed/Decoration}

PFunctor/{Lens, Cofree, M} + Control/Coalgebra
  → PFunctor/Dynamical/{Basic, System, Combinators, Run, Trajectory}
  → PFunctor/Dynamical/Behavior

Control/Monad/Indexed, PFunctor/Free/Basic
  → IPFunctor/Basic → IPFunctor/Free/{Basic, Indexed}
  → IPFunctor/Notation, IPFunctor/Notation/{Indexed, Deterministic}

Logic/HEq, Control/{Coalgebra, Comonad, Lawful, Monad}
  (free-standing helpers, depended on by both PFunctor and ITree)

PFunctor/Free → ITree/{Basic, Construct, Handler, Rec,
                       Events, Sim, Bisim}
PFunctor/Dynamical + ITree/Basic → ITree/Unfold

PFunctor/Free + Control → Interaction/Basic/{Spec, Node, Decoration,
                            Syntax, Shape, Interaction, Strategy,
                            Append, Replicate, StateChain, Chain,
                            Telescope, Sampler, MonadDecoration,
                            BundledMonad, Ownership, SpecFintype}

Interaction/Basic + PFunctor/Dynamical
  → Interaction/{TwoParty, Multiparty, Concurrent}
  (processes and machines are dynamical systems over their step polynomials)

Interaction/{Concurrent, Basic} → Interaction/UC/{Interface,
                                  OpenProcess, OpenProcessModel,
                                  OpenTheory, OpenSyntax, Notation,
                                  Emulates, MachineId, EnvAction,
                                  EnvOpenProcess, CorruptionModel,
                                  MomentaryCorruption, Leakage}
```

New files must respect this DAG. Re-exports through
`PolyFun.lean` are auto-generated; do not hand-edit.

## Attribution, Headers, And Docstrings

Follow [`CONTRIBUTING.md`](CONTRIBUTING.md) for the repo's explicit
attribution policy.

- The copyright line on every Lean file is `Copyright (c) <YEAR>
  PolyFun Contributors. All rights reserved.` — *always* "PolyFun
  Contributors", never an individual. This matches the
  [`Verified-zkEVM/ArkLib`](https://github.com/Verified-zkEVM/ArkLib)
  convention and keeps copyright ownership with the project.
- The `Authors:` line names individual humans (comma-separated for
  multiple authors). This is the human-attribution channel and is
  preserved on routine edits.
- New Lean files should use the standard copyright / license /
  authors header and a module docstring.
- For ordinary Lean source files, use the standard prologue layout:
  header, blank line, imports, blank line, module docstring.
- Docstrings must be intrinsic and descriptive. Cross-reference live
  sibling definitions when helpful, but do not mention removed or
  renamed declarations, change history, or reactive wording such as
  "replaces" or "renamed from".
- Preserve the `Authors:` line on routine edits. The copyright line
  stays "PolyFun Contributors" regardless of who edits.
- Only rewrite the `Authors:` line when a file is genuinely new or
  materially replaced.
- Do not add a separate AI-attribution line.
- For inline section breaks within a Lean file, use Mathlib-style
  doc-comment headers `/-! ## Title -/` (or the multi-line
  `/-! ## Title \n\n explanation -/` form). **Do not use ASCII banners**
  such as `-- ====...===` flanking a `-- § Title` line. The `/-!` form
  is rendered by `doc-gen4`; ASCII banners are not, and they make the
  file feel artificially partitioned. If a section is large enough to
  want a loud header, it is usually large enough to want its own
  `namespace` or its own file. See *Section Headers Within A File* in
  [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Naming Conventions

Follow Mathlib convention: `{head_symbol}_{operation}_{rhs_form}`.
Examples: `FreeM.bind_pure`, `Decoration.map_comp`, `ITree.bisim_bind`.
Structures use UpperCamelCase: `PFunctor`, `Spec`, `Decoration`,
`SyntaxOver`, `InteractionOver`, `ITree.Shape`.

## Critical Gotchas

1. **`autoImplicit = false` is set globally in `lakefile.toml`.** Do not
   add `set_option autoImplicit false` in individual files. Every
   variable must be explicitly declared.
2. **No cryptographic content.** Do not introduce dependencies on
   probability monads, evaluation distributions, security predicates,
   or concrete-scheme algebra. Parameterize over an abstract monad
   instead. Cryptographic content belongs in
   [`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io).
3. **`Spec.done` and `Spec.node` are `@[match_pattern, reducible]`**
   wrappers over `PFunctor.FreeM.{pure, roll}`. Pattern matching on
   them works transparently; `rfl` against the polynomial substrate
   also works. Do not break either invariant when refactoring.
4. **Files should stay under 1500 lines** unless explicitly opted out
   per file. The long-file linter cap is enforced repo-wide.
5. **Do not disable linters to silence errors.** Do not use
   `set_option linter.* false`, `set_option weak.linter.* false`, or
   add repo-level `leanOptions` that turn lints off. Fix the root
   cause instead.
6. **`PolyFun.lean` is generated.** Do not hand-edit it. After adding,
   renaming, or deleting `.lean` files under `PolyFun/`, run
   `./scripts/update-lib.sh`.
7. **Do not introduce `sorry` or `admit` in finished work.** Use `stop`
   only when explicitly preserving partial proof work during a refactor.

## Building

```bash
lake exe cache get && lake build
```

After adding new `.lean` files: `./scripts/update-lib.sh`.
For routine local validation: `./scripts/validate.sh`.

Environment linters and the test library have Lake drivers:

```bash
lake lint   # Batteries runLinter over the PolyFun library
lake test   # builds the PolyFunTest library
```

`./scripts/validate.sh --lint --test` folds both into the convenience wrapper.
Both run as independent CI jobs (`lint`, `test`) alongside `build`. Adding a
per-declaration `@[nolint <linter>]` exception requires
`import Batteries.Tactic.Lint` in that file.

Lean toolchain and Mathlib stay in sync (both currently `v4.31.0`).
Files should stay under 1500 lines.

## Further Reading

Deeper agent-facing notes live in [`docs/wiki/`](docs/wiki/). Use this
`AGENTS.md` for the one-screen overview and the wiki for details that are
too specific or too changeable to keep at the repo root.

- [`docs/wiki/README.md`](docs/wiki/README.md): hub and maintenance contract.
- [`docs/wiki/quickstart.md`](docs/wiki/quickstart.md): commands and
  validation playbook.
- [`docs/wiki/repo-map.md`](docs/wiki/repo-map.md): subtree map and where to
  start by task.
- [`docs/wiki/generated-files.md`](docs/wiki/generated-files.md): derived
  outputs and source-of-truth rules.
- [`docs/wiki/pfunctor.md`](docs/wiki/pfunctor.md): the polynomial-functor
  substrate.
- [`docs/wiki/ipfunctor.md`](docs/wiki/ipfunctor.md): state-indexed
  polynomial functors and their indexed free monads.
- [`docs/wiki/itree.md`](docs/wiki/itree.md): interaction trees layer.
- [`docs/wiki/interaction.md`](docs/wiki/interaction.md): generic interaction
  framework (`Spec`, two-party, multiparty, concurrent, UC).
- [`docs/wiki/notation.md`](docs/wiki/notation.md): notation reference (UC
  composition operators).
- [`docs/wiki/gotchas.md`](docs/wiki/gotchas.md): recurring traps and
  troubleshooting.

### Wiki Maintenance Contract

The wiki is maintained alongside the Lean source. Treat it as the canonical
long-form companion to this guide, while remembering that source files are the
final authority for names, imports, and theorem statements:

- If a page contradicts the source, the source wins. Fix the page in the
  same PR.
- If a PR changes commands, repo structure, generated-file behavior, file
  naming, namespaces, or load-bearing public APIs, update the matching wiki
  page in the same PR. Add a new page when that is the cleaner split.
- Promote recurring agent learnings into [`docs/wiki/`](docs/wiki/); do not
  let stable guidance live only in ephemeral notes (`*-NEVER-COMMIT.md`,
  scratch chats, scratch worktrees).
- Prefer linking to canonical docs (Lean source, Mathlib, papers in
  [`REFERENCES.md`](REFERENCES.md)) over copying their contents.

## References

Module docstrings cite a small set of foundational papers. The
canonical bibliography is [`REFERENCES.md`](REFERENCES.md).

Highlights:

- Hancock-Setzer 2000 — recursion over interaction interfaces; the
  free interaction structure on a polynomial container.
- Altenkirch-Ghani-Hancock-McBride-Morris 2015 — *Indexed Containers*
  (JFP 25, e5).
- Spivak-Niu 2024 — *Polynomial Functors: A General Theory of
  Interaction* (MIT Press); the patterns/matter pairing
  `FreeM ⊣ Cofree`.
- Xia-Zakowski-He-Hur-Malecha-Pierce-Zdancewic 2020 —
  *Interaction Trees* (POPL).
- Escardó-Oliva 2023 — games as type trees (TCS 974).
- McBride 2010; Dagand-McBride 2014 — displayed algebras / ornaments.
