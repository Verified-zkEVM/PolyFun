# Parliament: run a meeting from the terminal

Run a meeting, record motions and votes, and save a journal and readable draft minutes.
Parliament is a nonprobabilistic PolyFun case study using a bounded model of Robert's
Rules of Order Newly Revised (12th edition). One operator enters actions for the
members and supplies procedural judgments; member IDs are not authenticated logins.

## Run the example

From the repository root (Lake builds the executable if needed):

```sh
lake -d Examples/Parliament exe polyfun-parliament new --config Examples/Parliament/Fixtures/assembly.json --dir meeting-data
```

Use a fresh directory: `new` never resets an existing meeting. The supplied configuration
has members 0–3, chair 0, secretary 1, and quorum 3. At the `Action` prompt, enter `help`
to see commands or `status` to inspect the current record. Commands prompt for their
fields; names are case-sensitive, and ordinary text does not need JSON quoting.

### Adopt your first motion

Enter these actions in order. Each item in the right column is a separate response to
a prompt, not a comma-separated line. You can inspect `status` between actions.

| Action | Responses, in prompt order |
|---|---|
| `attendance` | `0`, `0`, `yes` |
| `attendance` | `0`, `1`, `yes` |
| `attendance` | `0`, `2`, `yes` |
| `attendance` | `0`, `3`, `yes` |
| `openMeeting` | `0` |
| `advanceBusiness` | `0` |
| `advanceBusiness` | `0` |
| `requestFloor` | `1` |
| `recognize` | `0`, `1` |
| `propose` | `1`, `main`, `fund the library` |
| `second` | `2` |
| `judge` | `allow`, `Within the assembly purpose.` |
| `continueAfterRuling` | `0` |
| `stateQuestion` | `0` |
| `openVote` | `0` |
| `vote` | `1`, `yes` |
| `vote` | `2`, `yes` |
| `announce` | `0` |

The two `advanceBusiness` actions move through reports and unfinished business to new
business. The `judge` action asks you to interpret the proposal: read the displayed
obligations before allowing it. For this demonstration, assume funding the library is
within the assembly's purpose. `continueAfterRuling` closes the appeal opportunity;
`stateQuestion` then puts the motion before the assembly.

After `announce`, the motion is adopted and the journal is at revision 18. Enter `export`
to publish without leaving, or `quit` to publish and exit. The
[sample Markdown minutes](Fixtures/draft/minutes.md) show this result.

### Browse, quit, and resume

`back` and `forward` browse earlier revisions; `history` asks for a revision number.
Browsing is read-only, so enter `live` before making another motion or judgment.
Accepted commands are saved before acknowledgment. `quit` and EOF leave the meeting
unfinished unless you have actually carried a motion to adjourn.

After quitting, resume where you left off:

```sh
lake -d Examples/Parliament exe polyfun-parliament resume meeting-data
```

### Inspect the saved files

`meeting-data/journal.json` contains the configuration and accepted commands. Exports
are immutable pairs of `minutes.md` and `minutes.json` under `exports/rev-N/`. For the
session above, open `meeting-data/exports/rev-18/minutes.md` in your editor. You can
verify that export against the journal, or reconstruct it in another directory:

```sh
lake -d Examples/Parliament exe polyfun-parliament verify meeting-data/journal.json meeting-data/exports/rev-18
lake -d Examples/Parliament exe polyfun-parliament replay meeting-data/journal.json --out reconstructed
```

If you have continued the meeting, use the export for its latest revision when verifying.
After a write failure, stop and resume from the saved journal before retrying; see the
[recovery contract](Docs/runtime.md) for the storage limits.

### Compare a ruling without entering one

After `second` and before `judge` in the session above, enter `compareRuling`. It displays
hypothetical **allow** and **deny** successors of the outstanding judgment, using the same
command checker as a real ruling. Each assumes the appeal opportunity closes with no appeal;
any rejected transition is printed as a rejection.

Nothing is saved or published, and the live judgment remains unanswered. This is a procedural
comparison, not advice about which ruling is correct. Enter `judge` separately to record your
actual decision. `compareRuling` always labels its source as the current live state, even while
you are browsing history. Use `--help` or `new --help` for generated invocation help.

### Use your own assembly

Print a template to a new file, edit its organization, roster, quorum, and calendar,
then start a separate meeting directory:

```sh
lake -d Examples/Parliament exe polyfun-parliament example-config > assembly.json
lake -d Examples/Parliament exe polyfun-parliament new --config assembly.json --dir my-assembly
```

Whole-command JSON is also accepted at the action prompt. The
[scripted session](Fixtures/meeting.input) shows the same first motion using JSON
commands and an interactive judgment.

## Model and storage limits

This is a bounded model, not a complete parliamentary authority. Human rulings remain
human judgments; the proofs do not establish their substantive correctness or physical
storage durability. The exported action register is a draft. A separate
[minutes workflow](Docs/runtime.md#editable-minutes-are-not-the-action-register) supports submission,
review, approval, and corrections while retaining the original approved text. Approval
does not certify factual accuracy. See the [coverage and sources](Docs/coverage.md)
for the modeled rules and exclusions.

Journal schema version 2 rejects version 1; this example promises no migration path.

## How it uses PolyFun

[Dialogue](Parliament/App/Dialogue.lean) constructs typed forms,
[Machine](Parliament/App/Machine.lean) separates interaction from storage effects, and
[Main](Parliament/App/Main.lean) connects real IO handlers to the resumable driver.
Certified inputs, replay, and publication remain distinct boundaries.

For a guided reading path, start with [Notes](../Notes/README.md), then
[typed attendance](Parliament/Walkthrough/Attendance.lean), the
[application walkthrough](Docs/walkthrough.md), and [architecture](Docs/architecture.md).
This is an independent Lake package: `import Parliament` is available inside it, while
the root default build and `import PolyFun` do not pull it in. Shared console and storage
helpers live in optional `PolyFunIO`.

Developer checks live in the [validation guide](../../docs/development/validation.md),
[validation script](../../scripts/validate.sh), and
[CLI test script](../../scripts/test-parliament-cli.py).
