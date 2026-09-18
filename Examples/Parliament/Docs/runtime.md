# IO runtime and verified draft minutes

The executable uses the same PolyFun application machine in production and tests.
A real handler performs terminal and filesystem operations in Lean `IO`; a
`StateM Memory` handler supplies scripted answers and models storage failures.

## The reusable driver

`PFunctor.DynSystem.DynComputation.unrollChunk` builds a finite `FreeM` interaction program from
any compatible `DynComputation`. `Chunk.done` carries a returned result;
`Chunk.paused` carries the exact residual state. `runChunk` interprets this program
through `PFunctor.Handler m p`. `runIO` repeatedly runs 128-interaction chunks.
It does not restart the machine at a chunk boundary or require a proof that the
meeting eventually terminates.

`unrollChunk_result` and `runChunk_result` show agreement with PolyFun's existing
bounded-run observation after forgetting the residual state. `unrollChunk_add`
and `runChunk_add` prove that resuming successive chunks agrees with the combined
budget. These equations apply to arbitrary compatible interfaces and lawful monads,
not just Parliament. They concern query sequencing; the backend remains responsible
for implementing the effect it was asked to perform.

## Certified history and document policy

`History rules initial final` contains accepted `EnabledInput` values. `Journal`
also retains a proof that initialization is structurally valid. Its accepted update
uses `meetingSystem.update`, and its history projects to `LegalTrace` and to an
exactly replayable command/event sequence. Certificates are erased from wire data.

The contextual `recordAction` policy uses each accepted command and its source
state. Thus a `lackSecond` command produces a `notSeconded` entry rather than a
fictional zero-to-zero vote. Consent has its own `DecisionMethod`, without a tally.
An adopted amendment updates the main wording before the main decision is recorded.
A table/referral/postponement records a procedural decision and the resulting
suspension, without declaring the main motion adopted.

`Records` is an ordered inference relation: omit precisely an event with no
recordable contextual action, or retain its corresponding typed entry, then continue.
`RecordsHistory` composes those receipt-level derivations. The proofs establish
that all and only the actions selected by the explicit policy appear in order.
This is the authored editorial specification, not an independent formalization of
all RONR minutes rules.

`DraftMinutes journal meeting` contains exactly the entries for that meeting.
The executable's export contains the chronological entries for the complete journal,
each labeled with meeting/session, date, clock reading, revision, and event index.
This retains earlier meetings when the assembly continues. Current unresolved
questions are listed separately; the display does not invent their eventual outcome.
Metadata is explicitly supplied and has no claim of independent authenticity.

`lower` preserves typed actions in presentation blocks. `Artifacts metadata journal`
carries JSON and Markdown strings plus equalities to their canonical renderings.
`History.entries_determined`, `draftMinutes_reconstruction`, and
`App.artifacts_reconstruction` establish that independently reconstructing the same
initial state and command history gives the same entries and requested payloads.
`verifyArtifacts` can certify observed strings after exact comparison. The CLI
performs the corresponding checks on raw UTF-8 bytes, avoiding newline normalization.

The Markdown renderer escapes supplied syntax and control characters. JSON retains
the modeled word arrays exactly; readable wording joins those words with spaces.
The theorem concerns the specified renderer, not an external Markdown viewer or a
formally verified JSON-parser implementation. Codec round trips and escaping are
covered by execution tests.

## Application protocol and storage

The machine explicitly represents ready, judging, awaiting persistence, publishing,
notification, and final-return phases. A candidate successor is held as an
`EnabledInput`; the committed journal stays unchanged until the persistence response
succeeds. `prepare_preserves_committed`, `failed_persistence_preserves`, and
`successful_persistence_legal`/`successful_persistence_extends` expose this contract.
`machineStep_safe` covers every response at every application phase: acknowledged
history either stays unchanged or extends by one certified legal input.
A publication effect must carry an `Artifacts` certificate for its journal.

The directory contains:

- `journal.json`: format/semantics version 1, initial configuration, and accepted commands.
- `meeting.lock`: the separate inode locked for the entire single-writer session.
- `journal.json.pending`: staged journal replacement, ignored during recovery.
- `exports/rev-N/minutes.json` and `minutes.md`: an immutable pair for revision N.
- `exports/.pending-N/`: staging files that may remain after interrupted publication.

A journal replacement is written and flushed to staging, checked by byte readback,
then renamed. A failure stops further acceptance and reports a nonzero exit. The
program does not assume the old filesystem contents survived an ambiguous failure:
`resume` replays the journal actually present. Temporary journal data is never treated
as an accepted source. Initialization writes revision zero before reading commands.

Export writes and checks both files in a staging directory before renaming that
directory. Existing revisions are verified, not overwritten. Partial staging files
can be rewritten by a retry; an invalid existing final export produces an error.
Export failure preserves committed meeting history. A failed explicit export returns
to the menu; a failed exit export produces a nonzero process status.

File write/read/rename/lock operations are opaque Lean runtime primitives. The kernel
proof establishes which certified payload the machine requests, not physical disk
persistence, power-loss durability, filesystem honesty, or an arbitrary handler's
truthfulness. The real handler reports success only after its required operations
and readback checks complete. The simulated backend tests errors both before and
after a journal may have been stored, and tests mismatched publication readback.

## Terminal and wire input

Run `lake exe polyfun-parliament --help` for workflows, or `example-config` for a complete
JSON configuration template. `new` refuses an existing meeting directory. `resume`
validates and replays the journal before presenting input. `replay` writes exports
without opening a live meeting; `verify` checks both files without changing them.
All loaders reject unknown journal versions and report the first illegal command's
zero-based index. They rebuild states and certificates instead of loading purported
proofs, event histories, or saved states.

The terminal accepts each public command name and prompts for typed parameters.
It also accepts a complete JSON command on one line. The encoding uses named
constructor arguments, for example:

```json
{"attendance":{"actor":0,"member":1,"present":true}}
{"propose":{"actor":1,"motion":{"main":{"text":["fund","the","library"]}}}}
{"vote":{"actor":1,"choice":"yes"}}
```

Nested amendments use the same named-argument encoding:

```json
{"propose":{"actor":1,"motion":{"primary":{"target":0,"edit":{"start":2,"count":1,"words":["museum"]}}}}}
{"propose":{"actor":1,"motion":{"secondary":{"target":2,"edit":{"wording":{"edit":{"start":0,"count":1,"words":["school"]}}}}}}}
```

`judge` displays the exact request, proposed and pending wording, suspended business,
and prior decisions. The operator chooses allow/deny and supplies an explanation.
Cancel or EOF produces no judgment command. The response becomes an ordinary
version-checked command, and the separate appeal opportunity remains open until
explicitly resolved. Replies and the configured identities are attributed inputs,
not authenticated facts.

`export` and `quit` are application actions, never parliamentary motions. EOF behaves
as `quit` and produces an unfinished draft unless adjournment was actually recorded.
No approval, correction, signature, network multi-user service, or formal minutes
adoption procedure is modeled.
