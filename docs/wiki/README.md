# PolyFun Agent Wiki

This directory is the deeper companion to [`AGENTS.md`](../../AGENTS.md). Use
`AGENTS.md` for the one-screen overview and this wiki for details that are
too specific or too changeable to keep at the repo root.

## Status: Recently Authored, Expect Drift

These pages were written together with the initial port of `PolyFun` from
[`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io) and have
not yet had time to settle. They are the best current reference for
agent-facing context, but they are **not gospel**:

- If a page contradicts a Lean source file, the source wins.
- Fix stale guidance in the same PR you noticed it in. Do not copy a stale
  paragraph forward into a new doc.
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
- [`itree.md`](itree.md): coinductive interaction trees.
- [`interaction.md`](interaction.md): the generic interaction framework
  (sequential `Spec`, two-party, multiparty local views, concurrent
  processes, UC open systems).

## Cross-Cutting Notes

- [`notation.md`](notation.md): notation reference. Currently scoped to UC
  composition (`∥`, `⊞`, `⊠`) and boundary tensor / swap.
- [`gotchas.md`](gotchas.md): recurring Lean traps and PolyFun-specific
  pitfalls.

## Maintenance Contract

- [`AGENTS.md`](../../AGENTS.md) is the canonical root guide.
  [`CLAUDE.md`](../../CLAUDE.md) is only a symlink.
- Keep one primary owner topic per page. The current pages are:
  - `quickstart.md` for commands, validation, and when to run which checks.
  - `repo-map.md` for repo structure and main work areas.
  - `generated-files.md` for derived outputs and source-of-truth rules.
  - `pfunctor.md` for the `PFunctor` / `FreeM` / `Cofree` substrate.
  - `itree.md` for interaction trees, bisimulation, and handlers.
  - `interaction.md` for the interaction framework above `FreeM`.
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

- [`../../README.md`](../../README.md): project overview and experimental
  status banner.
- [`../../AGENTS.md`](../../AGENTS.md): canonical agent guide (also
  [`CLAUDE.md`](../../CLAUDE.md) as a symlink).
- [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md): style, naming,
  attribution, and large-contribution policy.
- [`../../REFERENCES.md`](../../REFERENCES.md): bibliography backing module
  docstrings.
- [`../../PORTING-PLAN.md`](../../PORTING-PLAN.md): the wholesale port plan
  from [`Verified-zkEVM/VCV-io`](https://github.com/Verified-zkEVM/VCV-io).
