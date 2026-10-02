# Pipeline: compose a local file report

Pipeline reads files and prints byte and newline-byte counts. A loader, analyser, and
collector communicate through typed PolyFun interfaces. The files are never modified.

## Run the example

From the repository root (Lake builds the executable if needed):

```sh
lake -d Examples/Pipeline exe polyfun-pipeline report Examples/Pipeline/lean-toolchain
```

With this checkout's toolchain file, the result is:

```text
Examples/Pipeline/lean-toolchain: 25 bytes, 1 LF bytes
```

The report lists each supplied path in order. Repeating a path makes another read;
an unreadable path prints `ERROR` while the other files still receive report entries.
Counts are raw bytes and LF bytes, not Unicode characters or logical lines.
With no paths, the report is empty and successful.

### Pause and continue

Try a pause followed by continuation within the same process:

```sh
lake -d Examples/Pipeline exe polyfun-pipeline report --split-at 3 Examples/Pipeline/lean-toolchain
```

At that boundary the loader has already read the file. Continuation uses its retained
result; it does not read the file again. The report is the same as an uninterrupted run.

To see an unfinished execution explicitly:

```sh
lake -d Examples/Pipeline exe polyfun-pipeline report --fuel 3 Examples/Pipeline/lean-toolchain
```

This exits with code 2 and prints a pause diagnostic, not a complete report.

### Execution limits

No continuation is saved to disk: rerunning the command starts over. Normal reporting uses nine activations
per input path. This is a protocol budget, not a timeout or CPU-work bound; a filesystem read
is an atomic external effect in this model.

Exit 0 means every file was read; exit 1 means a read or protocol error. Use `report --help`
for generated option help. Arguments are validated before reading files.

## How it uses PolyFun

- [Model](Pipeline/Model.lean): byte counting and a sequential reference specification.
- [Network](Pipeline/Network.lean): component machines composed with `par` and `plug`,
  with handler-polymorphic execution and continuation.
- [Correctness](Pipeline/Correctness.lean): reference equivalence and an activation certificate
  for a deterministic mathematical filesystem; real IO remains a separate boundary.
- [App](Pipeline/App.lean): filesystem interpretation and report output.

The analyser and collector have no filesystem capability. The loader is the only component
whose handler reads files. Composition supplies the routes; the application does not implement
its own network runner. Execution is cooperative, not OS-threaded.

This is an independent, opt-in Lake package. Root `lake build`, `lake test`, and
`import PolyFun` do not pull it in, and it does not depend on Notes or Parliament.
Return to the [examples index](../README.md) to choose another topic.

Developer checks are documented in the [validation guide](../../docs/development/validation.md)
and run by the [validation wrapper](../../scripts/validate.sh) and
[CLI checks](../../scripts/test-pipeline-cli.py).
