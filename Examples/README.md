# PolyFun examples

Run a small nonprobabilistic application, then explore the PolyFun programs and handlers
behind it. All commands here and in the application READMEs run from the repository root.

## Choose an application

| Application | Use it for | PolyFun focus |
|---|---|---|
| [Notes](Notes/README.md) — start here | Create local notes, edit their text, and browse earlier revisions | Typed forms, a returning machine, and interchangeable handlers |
| [Pipeline](Pipeline/README.md) | Produce a read-only byte report for local files | Communicating components, typed routing, and pause/continuation |
| [Parliament](Parliament/README.md) | Record motions, judgments, votes, and draft minutes | A larger indexed model, certified history, and explicit IO boundaries |

Start a notebook in a fresh directory; Lake builds the executable if needed:

```sh
lake -d Examples/Notes exe polyfun-notes new notes-data
```

Follow [Notes' first session](Notes/README.md#run-the-example) to create and edit a note.
Then choose Pipeline for composition or Parliament for a deeper case study; neither is a
prerequisite for the other. Each README includes a complete session and its operational limits.

Each application is an independent Lake package depending on this checkout. Root
`lake build`, `lake test`, and `import PolyFun` do not pull them in. Notes and Parliament
use the optional `PolyFunIO` console and storage library, outside the generic umbrella.

## Explore one concept at a time

For the shortest source-reading path, read [Requests](Tutorials/Requests.lean) and its
[first-program walkthrough](../docs/tutorials/first-program.md), then return to Notes.
The following groups are choices, not a required ten-part course.

### Foundations

| Tutorial | What to explore |
|---|---|
| [Requests](Tutorials/Requests.lean) | One dependent sequence of requests, two handlers |
| [Machines](Tutorials/Machines.lean) | A counter's state, outputs, and continuation of finite runs |
| [Indexed programs](Tutorials/IndexedPrograms.lean) | Protocol phases, indexed sequencing, and forgetting indices |
| [Interaction trees](Tutorials/InteractionTrees.lean) | State events and ticks interpreted through different handlers |

### Composition and decisions

| Tutorial | What to explore |
|---|---|
| [Parallel reports](Tutorials/ParallelReports.lean) | Independent sources and explicit joint-request interpretation order |
| [Versioned requests](Tutorials/VersionedRequests.lean) | Routed clients, retained traffic, and stale-write rejection |
| [Update policies](Tutorials/UpdatePolicies.lean) | All-response safety, allowed answers, and why safety is not progress |
| [Reviewable workflows](Tutorials/ReviewableWorkflows.lean) | Edit approval, source metadata, dependent certificates, and cursor navigation |

### Liveness and implementation constraints

| Tutorial | What to explore |
|---|---|
| [Fair work queues](Tutorials/FairWorkQueues.lean) | Fair service drains finite backlogs; valid executions can still starve |
| [Bounded controller](Tutorials/BoundedController.lean) | Two worker slots, finite-state realizability, and equivalent representations |

Build the optional tutorials, then open a module in your Lean editor or check it directly:

```sh
lake build PolyFunExamples
lake env lean Examples/Tutorials/Requests.lean
```

These files contain checked definitions and proofs, not interactive executables. Use ordinary
imports such as `import Examples.Tutorials.Requests`; declarations live under
`PolyFunExamples.<TutorialName>`. There is no generic `Examples` umbrella.

For a runnable comparison of computation models, try
[Notes' six representation demos](Notes/README.md#try-the-small-computation-demos).
The [Parliament walkthrough](Parliament/Docs/walkthrough.md) develops certified prefixes,
safety, resumptions, interaction trees, and writer-handler erasure.

## Run the sessions on CI

Open the repository's [CI workflow](https://github.com/Verified-zkEVM/PolyFun/actions/workflows/ci.yml),
choose **Run workflow**, select your branch, and optionally enable **clean_build**.
The workflow builds all three opt-in packages and runs bounded scripted sessions through their
actual executables. Inspect the **Test** job's example output. This is automated terminal input,
not an interactive remote shell; use the application README commands for local interaction.

The [validation script](../scripts/validate.sh) maintains the same checks locally.
Testing methodology and coverage belong in the [validation guide](../docs/development/validation.md).
