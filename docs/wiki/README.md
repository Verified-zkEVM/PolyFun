# PolyFun Agent Wiki

This directory is the deeper companion to [`AGENTS.md`](../../AGENTS.md). Use
`AGENTS.md` for the one-screen overview and this wiki for details that are
too specific or too changeable to keep at the repo root.

## Status And Maintenance

These pages are the long-form companion to [`AGENTS.md`](../../AGENTS.md).
They are maintained with the Lean source and should move in the same PR as
load-bearing changes to commands, module layout, generated files, or public
APIs.

- If a page contradicts a Lean source file, the source wins.
- Fix stale guidance in the same PR you noticed it in.
- The repo's load-bearing files (the actual Lean source under
  [`PolyFun/`](../../PolyFun/), [`AGENTS.md`](../../AGENTS.md),
  [`CONTRIBUTING.md`](../../CONTRIBUTING.md), [`REFERENCES.md`](../../REFERENCES.md))
  are the source of truth. The wiki is supporting commentary.

See the *Wiki Maintenance Contract* section in
[`AGENTS.md`](../../AGENTS.md) for the canonical policy.

## Start Here

- [`quickstart.md`](quickstart.md): canonical agent command and validation
  playbook.
- [`repo-map.md`](repo-map.md): where to edit and how the main subtrees
  relate.
- [`generated-files.md`](generated-files.md): derived outputs and their
  sources of truth.

## Layer-Specific Notes

- [`pfunctor.md`](pfunctor.md): the polynomial-functor substrate
  (`PFunctor`, lenses, charts, equivalences, free monad `FreeM`,
  displayed `FreeM`, `Cofree` / M-type).
- [`ipfunctor.md`](ipfunctor.md): the state-indexed polynomial functor
  substrate (`IPFunctor`, single-index `FreeM`, two-index `FreeM₂`
  with `IndexedMonad` instance).
- [`ipfunctor-do-notation.md`](ipfunctor-do-notation.md): worked
  walkthrough of the three `do`-notation flavors for
  `IPFunctor.FreeM` / `FreeM₂`, with a small two-phase-protocol
  example.
- [`itree.md`](itree.md): coinductive interaction trees.
- [`interaction.md`](interaction.md): the generic interaction framework
  (sequential `TypeTree`, two-party, multiparty local views, concurrent
  processes, UC open systems).
- [`realizability.md`](realizability.md): realizability of free programs by
  state machines whose transition functions satisfy a given predicate
  (`StepClass`, `Realization`, `IsRealizableBy`).
- [`uc.md`](uc.md): UC semantic contract, paper-to-code traceability ledger,
  observation boundaries, and PolyFun/VCVio ownership split.

## Cross-Cutting Notes

- [`review-hardening.md`](review-hardening.md): required migration, API,
  mathematical, adversarial, lint, and content-control review passes.
- [`bisimulation.md`](bisimulation.md): glossary of the bisimulation and
  behavioural-equivalence notions (strong / delay / weak), the generic
  `Control.LTS` framework, and how the ITree, dynamical, and UC layers relate.
- [`program-logic.md`](program-logic.md): the program-logic kernel
  (`MAlgOrdered`, relational algebras, `MonadSupport` and the always/never
  judgments, free-monad wp, and the core-`Std.Do` quarantine).
- [`notation.md`](notation.md): notation reference. Currently scoped to UC
  composition (`∥`, `⊞`, `⊠`), boundary tensor / swap, and the scoped
  satisfaction judgments (`⊨`, `⊨ₐ`, `⊨ₛ`, `⊭`).
- [`gotchas.md`](gotchas.md): recurring Lean traps and PolyFun-specific
  pitfalls.

## Design Notes

Longer-form design and reading notes live in [`../reading/`](../reading/). The
one with repo-wide scope:

- [`../reading/upstream-alignment.md`](../reading/upstream-alignment.md): ledger
  of PolyFun's generic machinery against Lean core, Batteries, Mathlib, and
  cslib, with an adopt / keep / upstream / track verdict per abstraction. Re-run
  the survey when the toolchain pin moves.

## Maintenance Contract

- [`AGENTS.md`](../../AGENTS.md) is the canonical root guide.
  [`CLAUDE.md`](../../CLAUDE.md) is only a symlink.
- Keep one primary owner topic per page. The current pages are:
  - `quickstart.md` for commands, validation, and when to run which checks.
  - `repo-map.md` for repo structure and main work areas.
  - `generated-files.md` for derived outputs and source-of-truth rules.
  - `pfunctor.md` for the `PFunctor` / `FreeM` / `Cofree` substrate.
  - `ipfunctor.md` for the state-indexed `IPFunctor` / `FreeM` / `FreeM₂` substrate.
  - `itree.md` for interaction trees, bisimulation, and handlers.
  - `interaction.md` for the interaction framework above `FreeM`.
  - `realizability.md` for step classes and machine realizability.
  - `uc.md` for the UC semantic contract and external-model alignment.
  - `review-hardening.md` for the repository-wide review and hardening standard.
  - `notation.md` for notation cross-references.
  - `gotchas.md` for recurring traps.
- Add new pages when a recurring topic no longer fits cleanly in an existing
  guide.
- If a PR changes commands, repo structure, generated-file behavior, file
  naming, namespaces, or load-bearing public APIs, update the matching page
  in the same PR.
- Keep these files committed so worktrees and delegated agents see the same
  guidance.
- Promote recurring, repo-specific agent learnings here once they prove
  stable. Do not let stable guidance live only in ephemeral
  `*-NEVER-COMMIT.md` notes.
- Prefer links to canonical docs (Lean source, Mathlib, public papers) over
  copying their contents.

## Canonical Project Docs

- [`../../README.md`](../../README.md): project overview, scope, and build
  status.
- [`../../AGENTS.md`](../../AGENTS.md): canonical agent guide (also
  [`CLAUDE.md`](../../CLAUDE.md) as a symlink).
- [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md): style, naming,
  attribution, and large-contribution policy.
- [`../../REFERENCES.md`](../../REFERENCES.md): bibliography backing module
  docstrings.
