# Parliament: an executable PolyFun case study

This example runs a bounded model of Robert's Rules of Order Newly Revised
(12th edition), records human judgments, and produces typed, unapproved draft
minutes. It demonstrates how certified transitions become an executable application
through polynomial interfaces and interchangeable handlers.

## Run the example

From the PolyFun repository root:

```sh
lake build PolyFunExamples polyfun-parliament
lake exe polyfun-parliament new --config Examples/Parliament/Fixtures/assembly.json --dir demo-meeting < Examples/Parliament/Fixtures/meeting.input
lake exe polyfun-parliament verify demo-meeting/journal.json demo-meeting/exports/rev-18
```

The supplied input records attendance, obtains a human admissibility ruling, and adopts
“fund the library.” The [sample Markdown minutes](Fixtures/draft/minutes.md) show the
result. The meeting remains unfinished because quitting the application is not adjournment.
The [sample JSON](Fixtures/draft/minutes.json) and [journal](Fixtures/draft/journal.json)
can also be verified directly:

```sh
lake exe polyfun-parliament verify Examples/Parliament/Fixtures/draft/journal.json Examples/Parliament/Fixtures/draft
```

For an interactive meeting, print a configuration template, edit the organization,
roster, quorum, and dates, then start a fresh directory:

```sh
lake exe polyfun-parliament example-config > assembly.json
lake exe polyfun-parliament new --config assembly.json --dir meeting-data
lake exe polyfun-parliament resume meeting-data
lake exe polyfun-parliament replay meeting-data/journal.json --out reconstructed
```

Enter `help` for guided commands, `judge` to answer an outstanding request, `export`
to publish a draft, or `quit` to export and exit. EOF also exports without implying
adjournment. `new` never resets an existing directory. Accepted commands are saved
before acknowledgment; export revisions are immutable JSON/Markdown pairs.

## Read the implementation

Use `import Examples.Parliament`. The declarations retain the `Parliament` namespace.
The Lake target is named `PolyFunExamples` so that it can coexist with VCVio's
`Examples` target; no generic `Examples` umbrella is introduced.

| Start here | What it demonstrates |
| --- | --- |
| [Interaction](Interaction.lean) | `PFunctor` judgment signatures, request-indexed replies, `IPFunctor.Endo`, `IFreeM.mapM`, and an ongoing `DynSystem`. |
| [History](Minutes/History.lean) | A certified execution history whose commands reconstruct the same state and events. |
| [Application machine](App/Machine.lean) | `DynComputation.ofStep`, explicit effects, and legal history extension only after successful persistence. |
| [Memory handler](App/Memory.lean) and [IO handler](App/Storage.lean) | The same machine interpreted through `StateM` and real Lean `IO`. |
| [Typed documents](Minutes/Document.lean) and [rendering](Minutes/Render.lean) | Contextual action records, exact wording versions, and canonical JSON/Markdown certificates. |

The reusable `PFunctor.DynSystem.DynComputation` driver lives in core. `runChunk`
returns either a value or the exact residual state, and `runIO` resumes chunks of
128 queries. Machine state describes control flow and committed history; handler
state describes external interaction or a test backend. These are distinct layers.

## Guarantees and boundaries

Read the [coverage ledger](Docs/coverage.md), [research sources](Docs/research.md),
[architecture](Docs/architecture.md), and [IO/minutes contract](Docs/runtime.md).
Proofs establish behavior of the authored specification, legal history and replay,
and exact requested draft payloads. They do not establish that all RONR rules are
modeled, that a human ruling is substantively correct, or that physical storage is
durable. Formal minutes approval and correction are outside this model.

Twenty-five meeting scenarios also run through the application machine. Regression
tests include failure before and after a write, stale judgments, tampered exports,
chunk resumption, EOF, multi-meeting history, and real filesystem recovery.

```sh
./scripts/validate.sh --lint --test --axioms
```

The default `lake build` and `import PolyFun` remain independent of this case study.
Validation explicitly builds and audits the example. CLI tests use temporary directories.
