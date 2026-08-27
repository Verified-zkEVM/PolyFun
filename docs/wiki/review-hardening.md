# Review Hardening Standard

PolyFun changes are reviewed as mathematical library contributions, not only as
branches that compile. A review finding is complete only when it produces a
code change, a regression, a narrower statement, an upstream proposal, or an
explicit removal of content that should not ship.

## Required Review Passes

Every substantial pull request records four passes:

1. **Migration and CI.** Reconstruct the semantic diff on current `main`, remove
   merged dependencies and historical merge commits, and run the full current
   validation suite.
2. **API and layering.** Audit imports, public declarations, instances,
   notation, universe parameters, definitional equalities, and downstream
   consumers. Prefer stable public equations to unfolding implementation
   details.
3. **Mathematical and adversarial review.** Try to falsify headline statements
   on empty, zero, degenerate, and universe-polymorphic examples before reading
   their proofs. Commit every useful counterexample or boundary case as a test.
4. **Maintenance review.** Check Mathlib naming and documentation conventions,
   simp orientation, environment linters, axiom cleanliness, generated files,
   and the accuracy of source or paper claims.

The maintenance pass is source-backed: compare module docstrings and wiki
claims to the declarations and imports that actually ship, then check the
agent guide against the repository tree. Treat version-specific prose,
repository-rooted paths written as code, and descriptions copied across a
dependency boundary as likely drift points. `scripts/check-docs-integrity.py`
checks both markdown links and repository-rooted Lean paths, but semantic
accuracy still requires review.

## Upstream-First Mathematics

Before adding a generic definition or lemma, search the pinned Lean core,
Mathlib, Batteries, and cslib trees by statement shape and abstraction rather
than only by the proposed local name. Confirm plausible matches with a small
Lean example. Prefer upstream categories, filters, monad laws, transition
systems, finite mathematics, and algebraic structures over parallel APIs.

If a reusable result is genuinely absent, keep the local result narrow and
record the upstream search and the condition under which the local declaration
can be deleted. PolyFun remains the correct home for polynomial, interaction,
qualitative machine structure, and backend-relative quantitative accounting.
Probability, concrete complexity-class and machine-adequacy claims, and
cryptographic policy remain downstream.

## Hardening Checklist

A merge-ready change must have:

- a focused current-`main` diff and fresh CI;
- minimal, correctly classified imports and no accidental transitive API;
- an explicit public API delta, including removals and instance changes;
- ordinary-import canaries for load-bearing public laws;
- tests placed on the narrowest useful surface: ordinary-import canaries for
  public API, focused proof regressions beside the owning subsystem, and
  worked examples in `PolyFunTest/` rather than production modules;
- minimized regressions for every discovered failure or counterexample;
- satisfiable assumptions and statements that cover their documented scope;
- Mathlib-style names, intrinsic docstrings, and lint-clean simp declarations;
- no new `sorry`, `admit`, unsafe proof shortcut, or non-standard axiom;
- explicit axiom checks for headline declarations; and
- a final audit note saying what was attacked, what was hardened, and what
  remains outside the result.

Lint exceptions do not substitute for fixes. Any permitted declaration-scoped
exception must be justified next to the declaration. A broad or mixed change is
split when its independent claims cannot be reviewed and reverted separately.

## Content Control

Public statements should describe their intrinsic mathematics rather than a
development campaign. Paper-facing claims name the exact modeled theorem and
state missing computational, probabilistic, or realizability bridges. False or
vacuous statements are narrowed or removed; they are not preserved by adding
an opaque premise that carries the intended result.

For changes that affect VCVio, validate an ordinary downstream consumer against
the candidate PolyFun revision before merge. Stable lessons learned during a
review are folded back into this page; transient per-PR status belongs in the
pull request or tracking issue.
