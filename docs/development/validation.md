# Validation

Fetch precompiled dependencies on a fresh checkout, then run the full suite:

```bash
lake exe cache get
./scripts/validate.sh --examples --lint --test --axioms
```

Routine `./scripts/validate.sh` builds the core, upstream staging, optional complexity
backends, `PolyFunIO`, and small tutorials, then checks modules, generated imports and
documentation. It does not build the standalone applications.

## What the wrapper checks

| Flag | Scope |
|---|---|
| Default | Explicit library builds with `--wfail`; layering, module mode, Std.Do quarantine, ordinary-import boundaries, generated imports, docs checker regressions and integrity |
| `--lint` | Environment and text-style linters for the selected libraries |
| `--test` | Root regressions with `--wfail --iofail`, `lake test`, and the separate documentation consumer |
| `--axioms` | Axiom-sweep fixture matrix and the empty-baseline gate over selected library roots |
| `--examples` | Additionally build the independent Notes, Parliament and Pipeline libraries/executables; apply the selected lint/test/axiom flags in each package, including CLI/filesystem tests with `--test` |

The root `lake build`, `lake test`, and `import PolyFun` do not pull in the
applications. Root regressions may import small tutorials, not standalone apps.
`PolyFunIO` is an optional library outside the generic umbrella. No reverse import
from core, upstream staging, or applications into shared layers is permitted.

The committed axiom baseline is a zero-debt policy, not an allowlist. Both arrays
stay empty. Update mode refuses to record taint. Never add `sorry`, `admit`, or
non-standard axioms to finished work.

## New or moved source files

Stage the exact additions, deletions, and renames before generating the relevant umbrella:

```bash
./scripts/update-lib.sh
./scripts/update-lib.sh ToCslib
./scripts/update-lib.sh ComplexityBackends
./scripts/update-lib.sh PolyFunIO
./scripts/update-lib.sh Parliament
./scripts/update-lib.sh Notes
./scripts/update-lib.sh Pipeline
```

The generator reads tracked paths and rejects untracked source files. Never edit
generated umbrellas by hand. Tutorial and test libraries use glob targets.
See [generated files](generated-files.md).

## Focused commands

```bash
lake build PolyFunIO PolyFunExamples --wfail
lake build PolyFunTest --wfail --iofail
lake test
lake -d test/DocumentationConsumer build --wfail
lake -d Examples/Parliament build --wfail
lake -d Examples/Parliament test
lake -d Examples/Parliament lint
lake -d Examples/Notes build --wfail
lake -d Examples/Notes test
lake -d Examples/Notes lint
lake -d Examples/Pipeline build --wfail
lake -d Examples/Pipeline test
lake -d Examples/Pipeline lint
python3 scripts/test-parliament-cli.py
python3 scripts/test-notes-cli.py
python3 scripts/test-pipeline-cli.py
python3 scripts/test-docs-integrity.py
python3 scripts/check-docs-integrity.py
```

Build before environment linting; use `lake lint -- --trace` to inspect checks.
Tests are outside the production lint target. See [lint policy](linting.md).

The [documentation consumer](../../test/DocumentationConsumer/README.md) and the
standalone applications depend on the root by path. They share downloaded dependency
packages, but own their build artifacts. They use ordinary imports, including the
Parliament public-API canary, so missing exported equations cannot be hidden by
`import all`.

When changing a marked documentation example, update both its source region and
the excerpt. The integrity checker compares them; the owning Lake package elaborates
the Lean source.

## CI mapping

[CI](../../.github/workflows/ci.yml) retains the required `build`,
`Lint (environment linters)`, and `Test` jobs. They explicitly opt into all three
applications. Build caches include the root and all three package build directories;
dependency caches share the root manifest/toolchain key. Nightly clean builds skip
the build cache. Import, docs-integrity, text-style and API-doc workflows remain
separate checks. API docs cover the root libraries and tutorials; application
documentation is maintained beside each package.

All required jobs must pass on the revision under review. Style-only checks do not
cover compilation or proof validation.

## Examples as usability checks

The independent application READMEs describe manual operation; this page owns validation.
The existing CLI drivers test help and invalid invocations, real journal bytes, recovery,
and bounded PTY conversations that wait for each flushed prompt before sending the next answer.
`cli_test_support.py` shares that PTY harness; it is not a separate runner or CI job.
Each driver includes the README's principal session: Notes creates, edits, browses and reopens
a notebook; Parliament adopts the first motion through guided prompts, then verifies and replays
its export; Pipeline reports the toolchain file and checks continuation and insufficient fuel.
These cases assert visible results and saved data independently of the Lean renderers.

| Surface | Evidence and limits |
|---|---|
| Notes preview | EOF, cancel, invalid fields and stale versions perform zero writes; save uses ordinary edit acknowledgement |
| Six edit representations | Same result and visible console effects in scripted tests; universal indexed-handler and machine/resumption/tree bridges plus a five-query bound in `Notes.Correctness`; silent-step budgets remain representation-specific |
| Parliament comparison | Both branches use actual command checking; no live answer, persist or publish; no substantive ruling oracle |
| Parliament rules and replay | `ParliamentTest.Boundaries`, `Scenarios`, `Edges`, and `Semantics` cover vote/calendar/edit boundaries, complete journals, external rulings, renewal, repeated appeals, and minutes lifecycle; replay compares complete final states and ordered events |
| Parliament application | `ParliamentTest.Application` runs the meeting scenarios through persistence/publication phases and checks rejected inputs, ambiguous write failures, readback, resumption and tampering; CLI checks add real files, EOF, recovery, immutable exports and locks |
| Histories | Read-only browsing enforced by the application machine, not just the terminal backend |
| Generated Notes commands | Fixed Plausible seeds `20261001`, `17`, `8191`, 32 sequences each, at most 12 commands; independent newest-first version stacks, every chunk cut, faults before/after each write |
| Public usability | Separate documentation consumer composes handlers and chunks through ordinary imports; wrong indexed phases and response types fail elaboration |
| Parallel, routing, policy tutorials | Unequal lengths and interpretation order; stale conditional writes and retained traffic; safety versus progress |
| Pipeline | Universal sequential-report equivalence and a reachable-state `TokenBudgetCertificate` for an arbitrary deterministic file map; actual IO checks cover repeated paths, read errors, binary/Unicode bytes, every chunk cut, zero and insufficient fuel, no file writes |
| Reviewable workflows | Decorations and dependent evidence survive cursor restriction; rejection preserves the apply log |
| Fair work queues | Weak fairness drains a finite backlog without arrivals; an explicit valid execution starves a queue, while alternating service is strongly fair |
| Bounded controller | Finite local-step realization, busy-slot rejection, and equivalent boundary encodings; no wall-clock or asymptotic complexity claim |

Generated checks produce no proof of a universal property. Failures report the seed and shrunken
command codes; preserve any discovered counterexample as a deterministic regression before fixing
it. Domain proofs, public-equation canaries, byte-level IO checks, and generated checks serve
different purposes. No schema migration or stronger durability claim is implied.

The structure follows patterns already present upstream: separate effects, execution and an
independent operational specification in CSLib's `CslibTests/FreeMonad.lean`; small authoring APIs
followed by application combinators and correctness in the ITree tutorial; and promotion of
reusable lemmas out of application examples, as in Mathlib's Archive. `lean4-cli` is explicitly
declared by each app at the already-pinned toolchain version. Plausible is used only as a test
data generator, never as a proof tactic.

The focused examples cover handled assembly, fairness, displayed metadata and finite-state
realizability without conflating them: fairness is an assumption on a ticketed run, metadata
certificates certify source locations rather than user approval, and finite-state admission
does not bound the cost of filesystem IO. Remaining gaps include concrete quantitative
complexity backends, indexed coinduction, and observation-relative open-system refinement.

## Toolchain updates

Keep the root, documentation consumer, Notes, Parliament and Pipeline toolchains synchronized
with Mathlib and CSLib. Update root pins and run `lake update`, then update the
path-dependent packages and run the full suite. The root manifest is committed;
local package manifests are regenerated and ignored.
