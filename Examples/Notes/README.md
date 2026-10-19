# Notes: a local notebook in your terminal

Start here for a small application of PolyFun: create a note, replace a previous note's text,
and browse its history. There are no accounts, tags, synchronization, or parliamentary rules.

## Run the example

From the repository root (Lake builds the executable if needed):

```sh
lake -d Examples/Notes exe polyfun-notes new notes-data
```

Use a fresh directory for `new`; existing directories are never reset. A short session:

```text
notes> new
Text (one line, preserved exactly): buy tea
Saved revision 1.
notes> edit
Note ID: 0
Expected version: 0
Replacement text: buy green tea
Saved revision 2.
notes> list
Revision 2
[0 v1] buy green tea
notes> back
Revision 1 (history; use live to edit)
[0 v0] buy tea
notes> live
Revision 2
[0 v1] buy green tea
notes> quit
```

Use `list` to find a note's ID and current version before editing it. An edit replaces
the whole text; previous versions remain in the journal. IDs start at 0, and a new note's
version is 0. The expected-version prompt prevents accidentally overwriting a newer edit.

### Reopen the notebook

Accepted edits are saved as you go. After quitting, reopen the same notebook with:

```sh
lake -d Examples/Notes exe polyfun-notes open notes-data
```

### Preview an edit before saving

Use `preview` instead of `edit` to see both texts before committing. After reopening:

```text
notes> preview
Note ID: 0
Expected version: 1
Replacement text: buy oolong tea
Original:
buy green tea
Proposed:
buy oolong tea
save / cancel: cancel
Cancelled; no command submitted.
```

Enter `save` to submit the edit, or `cancel` to leave the journal unchanged. EOF, malformed
fields, and stale versions also submit nothing. Preview is available only in the live view.
The `edit` command saves immediately after its fields validate.

### History and storage limits

`history` selects a journal revision. `back`, `forward`, and `live` change only the view.
History is read-only; return to `live` before editing. Unknown IDs and stale versions are
errors, not implicit creates or overwrites. EOF quits, and EOF halfway through a form submits
nothing. Text fields preserve whitespace. To enter multiline text, use a single-line JSON command:

```json
{"edit":{"id":0,"expectedVersion":1,"text":"buy green tea\nand milk"}}
```

The command above applies after the sample session; enter it directly at `notes>`.
The notebook is stored in `notes-data/journal.json`. To start another notebook, choose
a different directory with `new`. Only one writer can open a notebook at a time.

Opening `journal.json` replays the commands and rejects an unknown schema or an illegal
edit. Checked writes are not a power-loss durability guarantee. After a save failure,
stop and reopen the notebook before retrying. Original text and accepted replacements
remain in the journal.

### Try the small computation demos

These ask for one line and print the result without saving a notebook:

```sh
lake -d Examples/Notes exe polyfun-notes demo free
lake -d Examples/Notes exe polyfun-notes demo tree
```

Choose `free`, `indexed`, `system`, `machine`, `resumption`, or `tree` to try the same
interaction through different PolyFun representations. See the
[walkthrough source](Notes/Walkthrough.lean) for the implementations and an in-memory
shared-prefix branching example; branching is not filesystem undo.

`demo edit MODEL` starts with note `0`, version `0`, containing `First local note`. Try
replacement text followed by `save`, then run it again with `cancel`. Even `save` only
prints the prepared command: these demos never open or write a notebook directory.

```sh
lake -d Examples/Notes exe polyfun-notes demo edit indexed
lake -d Examples/Notes exe polyfun-notes demo edit tree
```

Use `--help` or `new --help` for generated command-line help. Invalid invocations exit nonzero.

## How it uses PolyFun

[Model](Notes/Model.lean) defines pure note updates and the replayable journal.
[Dialogue](Notes/Dialogue.lean) collects typed actions; [App](Notes/App.lean) handles them
with a returning machine whose effects separate interaction from storage.
[Runtime](Notes/Runtime.lean) supplies real console and filesystem handlers.

For a closer look, [Preview](Notes/Preview.lean) prepares edits using only console operations,
and the [walkthrough](Notes/Walkthrough.lean) connects the computation representations.
Its [correctness companion](Notes/Correctness.lean) separates exact indexed/returning behavior
from weak tree behavior: an added silent step changes fuel, not console interaction.

This directory is its own Lake package, depending on the root checkout by path. `lake build`,
`lake test`, and `import PolyFun` at the repository root do not pull it in. The shared optional
`PolyFunIO` library supplies forms, stream handlers, and checked storage;
it is not in the generic `PolyFun` umbrella. See the
[execution guide](../../docs/guides/execution.md) for generic drivers and silent-step budgets.

Next: [Pipeline](../Pipeline/README.md) for communicating components, or
[Parliament](../Parliament/README.md) for a larger domain model.

Developer checks live in the [validation guide](../../docs/development/validation.md),
[validation script](../../scripts/validate.sh), and [CLI test script](../../scripts/test-notes-cli.py).
